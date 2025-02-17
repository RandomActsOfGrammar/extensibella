grammar extensibella:common:abstractSyntax;


nonterminal Type with
   pp, abella_pp, isAtomic,
   toList<Type>, --type broken into a list across arrows
   headConstructor,
   tySubst, subst<Type>,
   unifyWith<Type>, downSubst, upSubst, tyVars,
   freshenSubst, freshenSubst_down, freshen<Type>,
   containsVars, isError,
   type, name,
   typeEnv;
propagate typeEnv on Type;

inherited attribute tySubst::Substitution;

--freshen a type by creating new ty vars for each variable
synthesized attribute freshenSubst::Substitution;
inherited attribute freshenSubst_down::Substitution;
synthesized attribute freshen<a>::a;

--whether there are var types contained within
synthesized attribute containsVars::Boolean;

--"Equality" also accepts error type with anything
--Since this is intended for error checking, we assume the error for
--   the error type has already been produced
attribute compareTo, isEqual occurs on Type;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = ppConcat([if ty1.isAtomic then ty1.pp else parens(ty1.pp),
                     text(" ->"), line(), ty2.pp]);
  top.abella_pp = (if ty1.isAtomic
                   then ty1.abella_pp
                   else "(" ++ ty1.abella_pp ++ ")") ++
                  " -> " ++ ty2.abella_pp;
  top.isAtomic = false;

  top.headConstructor = error("arrowType.headConstructor");

  top.toList = ty1.toList ++ ty2.toList;

  ty1.tySubst = top.tySubst;
  ty2.tySubst = top.tySubst;
  top.subst = arrowType(ty1.subst, ty2.subst);

  ty1.downSubst = top.downSubst;
  local sty2::Type = substituteTy(^ty2, ty1.upSubst);
  sty2.downSubst = ty1.upSubst;
  ty1.unifyWith =
      case top.unifyWith of
      | arrowType(t, _) -> ^t
      | _ -> error("Should not access")
      end;
  sty2.unifyWith =
      case top.unifyWith of
      | arrowType(_, t) -> substituteTy(^t, ty1.upSubst)
      | _ -> error("Should not access")
      end;
  top.upSubst =
      case top.unifyWith of
      | arrowType(t1, t2) -> sty2.upSubst
      | varType(v) -> addSubst(v, ^top, top.downSubst)
      | _ ->
        addErrSubst("Cannot unify " ++ justShow(top.unifyWith.pp) ++
                    " and " ++ justShow(top.pp), top.downSubst)
      end;

  top.freshen = arrowType(ty1.freshen, ty2.freshen);
  ty1.freshenSubst_down = top.freshenSubst_down;
  ty2.freshenSubst_down = ty1.freshenSubst;
  top.freshenSubst = ty2.freshenSubst;

  top.name = error("arrowType.name");

  top.isError = ty1.isError || ty2.isError;

  top.type = arrowType(ty1.type, ty2.type);

  ty1.compareTo =
      case top.compareTo of
      | arrowType(t, _) -> t
      | _ -> error("Should not access")
      end;
  ty2.compareTo =
      case top.compareTo of
      | arrowType(_, t) -> t
      | _ -> error("Should not access")
      end;
  top.isEqual =
      case top.compareTo of
      | arrowType(_, _) -> ty1.isEqual && ty2.isEqual
      | errorType() -> true
      | _ -> false
      end;

  top.containsVars = ty1.containsVars || ty2.containsVars;
}

abstract production nameType
top::Type ::= name::QName
{
  top.pp = name.pp;
  top.abella_pp = name.abella_pp;
  top.isAtomic = true;

  top.headConstructor = ^name;

  top.toList = [^top];

  top.subst = nameType(^name);
  top.upSubst =
      case top.unifyWith of
      | nameType(n) when ^n == ^name -> top.downSubst
      | nameType(n) ->
        addErrSubst("Cannot unify " ++ justShow(top.unifyWith.pp) ++
                    " and " ++ justShow(top.pp), top.downSubst)
      | varType(v) -> addSubst(v, ^top, top.downSubst)
      | _ ->
        addErrSubst("Cannot unify " ++ justShow(top.unifyWith.pp) ++
                    " and " ++ justShow(top.pp), top.downSubst)
      end;

  top.freshen = nameType(^name);
  top.freshenSubst = top.freshenSubst_down;

  top.name = ^name;

  top.isError = !name.typeFound;

  top.type =
      if name.typeFound
      then nameType(name.fullType.name)
      else errorType();

  top.isEqual =
      case top.compareTo of
      | nameType(x) -> ^x == ^name
      | errorType() -> true
      | _ -> false
      end;

  top.containsVars = false;
}

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = ppConcat([functorTy.pp, text(" "),
                     if argTy.isAtomic then argTy.pp
                                       else parens(argTy.pp)]);
  top.abella_pp = functorTy.abella_pp ++ " " ++
                  if argTy.isAtomic
                  then argTy.abella_pp
                  else "(" ++ argTy.abella_pp ++ ")";
  top.isAtomic = false;

  top.headConstructor = functorTy.headConstructor;

  top.toList = [^top];

  functorTy.tySubst = top.tySubst;
  argTy.tySubst = top.tySubst;
  top.subst =
      functorType(functorTy.subst, argTy.subst);

  functorTy.downSubst = top.downSubst;
  local sargTy::Type = substituteTy(^argTy, functorTy.upSubst);
  sargTy.downSubst = functorTy.upSubst;
  functorTy.unifyWith =
      case top.unifyWith of
      | functorType(t, _) -> ^t
      | _ -> error("Should not access")
      end;
  sargTy.unifyWith =
      case top.unifyWith of
      | functorType(_, t) -> substituteTy(^t, functorTy.upSubst)
      | _ -> error("Should not access")
      end;
  top.upSubst =
      case top.unifyWith of
      | functorType(_, _) -> sargTy.upSubst
      | varType(v) -> addSubst(v, ^top, top.downSubst)
      | _ ->
        addErrSubst("Cannot unify " ++ justShow(top.unifyWith.pp) ++
                    " and " ++ justShow(top.pp), top.downSubst)
      end;

  top.freshen = functorType(functorTy.freshen, argTy.freshen);
  functorTy.freshenSubst_down = top.freshenSubst_down;
  argTy.freshenSubst_down = functorTy.freshenSubst;
  top.freshenSubst = argTy.freshenSubst;

  top.name = error("functorType.name");

  top.isError = functorTy.isError || argTy.isError;

  top.type = functorType(functorTy.type, argTy.type);

  functorTy.compareTo =
      case top.compareTo of
      | functorType(t, _) -> t
      | _ -> error("Should not access")
      end;
  argTy.compareTo =
      case top.compareTo of
      | functorType(_, t) -> t
      | _ -> error("Should not access")
      end;
  top.isEqual =
      case top.compareTo of
      | functorType(_, _) -> functorTy.isEqual && argTy.isEqual
      | errorType() -> true
      | _ -> false
      end;

  top.containsVars = functorTy.containsVars || argTy.containsVars;
}


abstract production varType
top::Type ::= name::String
{
  top.pp = text(name);
  top.abella_pp = name;
  top.isAtomic = true;

  top.name = error("Should not access varType.name");

  top.headConstructor = error("varType.headConstructor");
  top.toList = [^top];

  top.subst =
      case lookupSubst(name, top.tySubst) of
      | nothing() -> varType(name)
      | just(ty) -> ty
      end;

  top.upSubst =
      case top.unifyWith of
      | varType(v) when v == name -> top.downSubst
      | varType(v) ->
        --add binding both directions to find substitution when one is
        --unified with a type, regardless which one
        addSubst(name, top.unifyWith,
                 addSubst(v, ^top, top.downSubst))
      | ty -> addSubst(name, ty, top.downSubst)
      end;

  --freshening a type variable is checking if it has already been
  --freshened, taking the new one if it has, or creating a new one
  top.freshen =
      case lookupSubst(name, top.freshenSubst_down) of
      | just(ty) -> ty
      | nothing() ->
        varType("_var_" ++ name ++ "_" ++ toString(genInt()))
      end;
  top.freshenSubst =
      addSubst(name, top.freshen, top.freshenSubst_down);

  top.isEqual =
      case top.compareTo of
      | varType(n) -> n == name
      | errorType() -> true
      | _ -> false
      end;

  top.type = ^top;

  top.isError = false;

  top.containsVars = true;
  top.tyVars <- [name];
}


abstract production errorType
top::Type ::=
{
  top.pp = text("<error>");
  top.abella_pp = error("errorType.abella_pp");
  top.isAtomic = true;

  top.name = error("Should not access errorType.name");

  top.headConstructor = error("errorType.headConstructor");
  top.toList = [^top];

  top.subst = errorType();

  top.upSubst = top.downSubst;

  top.freshen = errorType();
  top.freshenSubst = top.freshenSubst_down;

  top.isEqual = true;

  top.type = ^top;

  top.isError = true;

  top.containsVars = false;
}


--The purpose of this production is only for printing it nicely
abstract production stringType
top::Type ::=
{
  top.pp = text("string");
  forwards to listType(nameType(toQName("$char")));
}





nonterminal TypeList with
   pps, abella_pp,
   toList<Type>, len,
   typeEnv,
   isError,
   tySubst, subst<TypeList>,
   unifyWith<TypeList>, downSubst, upSubst,
   freshen<TypeList>, freshenSubst_down, freshenSubst,
   containsVars, tyVars,
   types;
propagate typeEnv on TypeList;

attribute compareTo, isEqual occurs on TypeList;

abstract production emptyTypeList
top::TypeList ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.subst = emptyTypeList();

  top.freshen = emptyTypeList();
  top.freshenSubst = top.freshenSubst_down;

  top.types = emptyTypeList();

  top.containsVars = false;

  top.upSubst =
      case top.unifyWith of
      | emptyTypeList() -> top.downSubst
      | addTypeList(_, _) ->
        addErrSubst("Cannot unify [] and [" ++
           justShow(ppImplode(text(", "), top.unifyWith.pps)) ++ "]",
           top.downSubst)
      end;

  top.isEqual =
      case top.compareTo of
      | emptyTypeList() -> true
      | _ -> false
      end;

  top.isError = false;
}


abstract production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.pps = ty.pp::rest.pps;
  top.abella_pp = if rest.abella_pp == ""
                  then ty.abella_pp
                  else ty.abella_pp ++ ", " ++ rest.abella_pp;

  top.toList = ^ty::rest.toList;
  top.len = 1 + rest.len;

  ty.tySubst = top.tySubst;
  rest.tySubst = top.tySubst;
  top.subst = addTypeList(ty.subst, rest.subst);

  top.freshen = addTypeList(ty.freshen, rest.freshen);
  ty.freshenSubst_down = top.freshenSubst_down;
  rest.freshenSubst_down = ty.freshenSubst;
  top.freshenSubst = rest.freshenSubst;

  top.types = addTypeList(ty.type, rest.types);

  top.containsVars = ty.containsVars || rest.containsVars;

  ty.downSubst = top.downSubst;
  ty.unifyWith =
      case top.unifyWith of
      | addTypeList(x, _) -> ^x
      | _ -> error("Should not access")
      end;
  local srest::TypeList = substituteTyList(^rest, ty.upSubst);
  srest.downSubst = ty.upSubst;
  srest.unifyWith =
      case top.unifyWith of
      | addTypeList(_, x) -> substituteTyList(^x, ty.upSubst)
      | _ -> error("Should not access")
      end;
  top.upSubst =
      case top.unifyWith of
      | addTypeList(_, _) -> srest.upSubst
      | emptyTypeList() ->
        addErrSubst("Cannot unify [" ++
           justShow(ppImplode(text(", "), top.pps)) ++ "] and [" ++
           justShow(ppImplode(text(", "), top.unifyWith.pps)) ++ "]",
           top.downSubst)
      end;

  ty.compareTo =
      case top.compareTo of
      | addTypeList(x, _) -> x
      | _ -> error("No type")
      end;
  rest.compareTo =
      case top.compareTo of
      | addTypeList(_, x) -> x
      | _ -> error("No type")
      end;
  top.isEqual =
      case top.compareTo of
      | addTypeList(x, _) -> ty.isEqual && rest.isEqual
      | _ -> false
      end;

  top.isError = ty.isError || rest.isError;
}





nonterminal MaybeType with
   pp, abella_pp,
   typeEnv,
   isJust;
propagate typeEnv on MaybeType;

abstract production nothingType
top::MaybeType ::=
{
  top.pp = text("");
  top.abella_pp = "";

  top.isJust = false;
}


abstract production justType
top::MaybeType ::= ty::Type
{
  top.pp = ty.pp;
  top.abella_pp = ty.abella_pp;

  top.isJust = true;
}





type Substitution = Either<[Message] [(String, Type)]>;

function emptySubst
Substitution ::=
{
  return right([]);
}


--Need to be certain
-- 1. varName must not have a binding in base
-- 2. No vars from base occur in ty
function addSubst
Substitution ::= varName::String ty::Type base::Substitution
{
  return
     case base of
     | left(err) -> left(err)
     | right(lst) ->
       right((varName, ^ty)::
          --replace any occurrences of varName with ty in base
          map(\ p::(String, Type) ->
                (p.1,
                 performSubstitutionType(p.2,
                    right([(varName, ^ty)]))),
              lst))
     end;
}


--When using joinSubst, you need to be sure
-- 1. No vars from either substitution occur in the types referenced
--    in each other
-- 2. The vars bound in each are disjoint
function joinSubst
Substitution ::= s1::Substitution s2::Substitution
{
  return
     case s1, s2 of
     | left(err1), left(err2) -> left(err1 ++ err2)
     | left(err), right(_) -> left(err)
     | right(_), left(err) -> left(err)
     | right(l1), right(l2) -> right(l1 ++ l2)
     end;
}


function addErrSubst
Substitution ::= err::String base::Substitution
{
  return
     case base of
     | left(errs) -> left(errorMsg(err)::errs)
     | right(_) -> left([errorMsg(err)])
     end;
}


function lookupSubst
Maybe<Type> ::= name::String subst::Substitution
{
  return lookupSubstHelp(name, subst, []);
}
function lookupSubstHelp
Maybe<Type> ::= name::String subst::Substitution seen::[String]
{
  local lkp::Maybe<Type> =
      case subst of
      | left(err) -> nothing()
      | right(lst) -> lookup(name, lst)
      end;
  local sub::Maybe<Type> =
      case lkp of
      | just(varType(v)) -> lookupSubstHelp(v, subst, name::seen)
      | mt -> mt
      end;
  return if contains(name, seen)
         then nothing()
         else case sub of
              | nothing() -> lkp --catch no further binding
              | _ -> sub
              end;
}


function errorsFromSubst
[Message] ::= subst::Substitution
{
  return case subst of
         | left(err) -> err
         | _ -> []
         end;
}


function showSubst
String ::= s::Either<[Message] [(String, Type)]>
{
  return
     case s of
     | left(errs) ->
       "Error:  [" ++ implode("; ", map((.msg_pp), errs)) ++ "]"
     | right(lst) ->
       "Subst:  [" ++ 
          implode(", ",
             map(\ p::(String, Type) ->
                   "(" ++ p.1 ++ ", " ++ justShow(p.2.pp) ++ ")",
                 lst)) ++ "]"
     end;
}


function substituteTy
Type ::= ty::Type subst::Substitution
{
  ty.tySubst = subst;
  return ty.subst;
}
function substituteTyList
TypeList ::= tyL::TypeList subst::Substitution
{
  tyL.tySubst = subst;
  return tyL.subst;
}





nonterminal TypeUnify with upSubst, downSubst;

abstract production typeUnify
top::TypeUnify ::= ty1::Type ty2::Type
{
  local substTy1::Type = performSubstitutionType(^ty1, top.downSubst);
  local substTy2::Type = performSubstitutionType(^ty2, top.downSubst);
  substTy1.unifyWith = ^substTy2;
  substTy1.downSubst = top.downSubst;
  top.upSubst = substTy1.upSubst;
}


--for when we don't have types to unify, but still need the unify
abstract production blankUnify
top::TypeUnify ::=
{
  top.upSubst = top.downSubst;
}



function performSubstitutionType
Type ::= t::Type s::Substitution
{
  t.tySubst = s;
  return t.subst;
}


function performSubstitutionTypeList
TypeList ::= t::TypeList s::Substitution
{
  t.tySubst = s;
  return t.subst;
}



function freshenType
Type ::= ty::Type
{
  ty.freshenSubst_down = emptySubst();
  return ty.freshen;
}


function freshenTypeList
TypeList ::= ty::TypeList
{
  ty.freshenSubst_down = emptySubst();
  return ty.freshen;
}
