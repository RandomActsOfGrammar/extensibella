grammar extensibella:common:abstractSyntax;


nonterminal Metaterm with
   pp, abella_pp, isAtomic,
   splitImplies, splitConjunctions,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames,
   upSubst, downSubst, downVarTys, tyVars,
   unknownKReplaced<Metaterm>, replaceUnknownK,
   subst<Metaterm>, substName, substTerm;
propagate typeEnv, constructorEnv, relationEnv,
          replaceUnknownK, unknownKReplaced, substName, substTerm
   on Metaterm;
propagate boundNames, downVarTys on Metaterm
   excluding bindingMetaterm;

abstract production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = cat(ppImplode(text(" "), rel.pp::args.pps), r.pp);
  top.abella_pp =
      rel.abella_pp ++ " " ++ args.abella_pp ++ r.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [^top];
  top.splitConjunctions = [^top];

  local unify::TypeUnify =
      if rel.relFound
      then typeUnify(
              freshenType(
                 foldr1(arrowType, rel.fullRel.types.toList)),
              foldr(arrowType, propType, args.types.toList))
      else blankUnify();
  args.downSubst = top.downSubst;
  unify.downSubst = args.upSubst;
  top.upSubst = unify.upSubst;

  top.subst = relationMetaterm(^rel, args.subst, ^r);
}

abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = text("true");
  top.abella_pp = "true";
  top.isAtomic = true;

  top.splitImplies = [^top];
  top.splitConjunctions = [^top];

  top.upSubst = top.downSubst;

  top.subst = ^top;
}

abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = text("false");
  top.abella_pp = "false";
  top.isAtomic = true;

  top.splitImplies = [^top];
  top.splitConjunctions = [^top];

  top.upSubst = top.downSubst;

  top.subst = ^top;
}

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = ppImplode(text(" "), [t1.pp, text("="), t2.pp]);
  top.abella_pp = t1.abella_pp ++ " = " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [^top];
  top.splitConjunctions = [^top];

  local unify::TypeUnify = typeUnify(t1.type, t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify.downSubst = t2.upSubst;
  top.upSubst = unify.upSubst;

  top.subst = eqMetaterm(t1.subst, t2.subst);
}

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = docGroup(if t1.isAtomic then t1.pp else parens(t1.pp)) ++
           text(" ->") ++ softbreak() ++ docGroup(t2.pp);
  top.abella_pp = "(" ++ t1.abella_pp ++ ") -> " ++ t2.abella_pp;
  top.isAtomic = false;

  top.splitImplies = ^t1::t2.splitImplies;
  top.splitConjunctions = [^top];

  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  top.upSubst = t2.upSubst;

  top.subst = impliesMetaterm(t1.subst, t2.subst);
}

abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = docGroup(if t1.isAtomic then t1.pp else parens(t1.pp)) ++
           text(" \\/") ++ line() ++
           docGroup(if t2.isAtomic then t2.pp else parens(t2.pp));
  top.abella_pp =
      "(" ++ t1.abella_pp ++ ") \\/ (" ++ t2.abella_pp ++ ")";
  top.isAtomic = false;

  top.splitImplies = [^top];
  top.splitConjunctions = [^top];

  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  top.upSubst = t2.upSubst;

  top.subst = orMetaterm(t1.subst, t2.subst);
}

abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = docGroup(if t1.isAtomic then t1.pp else parens(t1.pp)) ++
           text(" /\\") ++ line() ++
           docGroup(if t2.isAtomic then t2.pp else parens(t2.pp));
  top.abella_pp =
      "(" ++ t1.abella_pp ++ ") /\\ (" ++ t2.abella_pp ++ ")";
  top.isAtomic = false;

  top.splitImplies = [^top];
  --split both because associative
  top.splitConjunctions = t1.splitConjunctions ++ t2.splitConjunctions;

  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  top.upSubst = t2.upSubst;

  top.subst = andMetaterm(t1.subst, t2.subst);
}

abstract production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  top.pp = b.pp ++ text(" ") ++
           ppImplode(text(" "), nameBindings.pps) ++ text(",") ++
           nest(2, line() ++ docGroup(body.pp));
  top.abella_pp = b.abella_pp ++ " " ++ nameBindings.abella_pp ++
                  ", " ++ body.abella_pp;
  top.isAtomic = false;

  top.splitImplies = body.splitImplies;
  top.splitConjunctions = [^top];

  --Want ALL names which occur, even if only in bindings
  top.usedNames := nameBindings.usedNames ++ body.usedNames;

  body.boundNames = top.boundNames ++ nameBindings.usedNames;

  --save the names for var types here
  local varTys::[(String, Either<Type String>)] =
      map(\ p::(String, MaybeType) ->
            (p.1, case p.2 of
                  | justType(t) -> left(^t)
                  | nothingType() ->
                    right("__Bound" ++ toString(genInt()))
                  end),
          nameBindings.toList);
  body.downVarTys =
      map(\ p::(String, Either<Type String>) ->
            (p.1, case p.2 of
                  | left(t) -> t
                  | right(s) -> varType(s)
                  end),
          varTys) ++ top.downVarTys;

  body.downSubst = top.downSubst;
  top.upSubst = body.upSubst;
  top.tyVars <- flatMap(\ p::(String, Either<Type String>) ->
                          case p.2 of
                          | left(_) -> []
                          | right(s) -> [s]
                          end,
                        varTys);

  top.subst = bindingMetaterm(^b, ^nameBindings, body.subst);
}





nonterminal Bindings with
   pps, abella_pp,
   toList<(String, MaybeType)>, len,
   usedNames,
   typeEnv;
propagate typeEnv on Bindings;

abstract production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.pps =
      if mty.isJust
      then [parens(ppConcat([text(name), text(" : "), mty.pp]))]
      else [text(name)];
  top.abella_pp =
      if mty.isJust
      then "(" ++ name ++ " : " ++ mty.abella_pp ++ ")"
      else name;

  top.toList = [(name, ^mty)];
  top.len = 1;

  top.usedNames := [name];
}


abstract production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.pps =
     (if mty.isJust
      then parens(ppConcat([text(name), text(" : "), mty.pp]))
      else text(name))::rest.pps;
  top.abella_pp =
      ( if mty.isJust
        then "(" ++ name ++ " : " ++ mty.abella_pp ++ ")"
        else name ) ++ " " ++ rest.abella_pp;

  top.toList = (name, ^mty)::rest.toList;
  top.len = 1 + rest.len;

  top.usedNames := name::rest.usedNames;
}




nonterminal Restriction with pp, abella_pp,
   compareTo, isEqual;
propagate compareTo, isEqual on Restriction;

abstract production emptyRestriction
top::Restriction ::=
{
  top.pp = notext();
  top.abella_pp = "";
}

abstract production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = cat(text(" "), text(replicate(n, "*")));
  top.abella_pp = " " ++ replicate(n, "*");
}

abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = cat(text(" "), text(replicate(n, "@")));
  top.abella_pp = " " ++ replicate(n, "@");
}

abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = cat(text(" "), text(replicate(n, "+")));
  top.abella_pp = " " ++ replicate(n, "+");
}

abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = cat(text(" "), text(replicate(n, "#")));
  top.abella_pp = " " ++ replicate(n, "#");
}




nonterminal Binder with pp, abella_pp,
   compareTo, isEqual;
propagate compareTo, isEqual on Binder;

abstract production forallBinder
top::Binder ::=
{
  top.pp = text("forall");
  top.abella_pp = "forall";
}

abstract production existsBinder
top::Binder ::=
{
  top.pp = text("exists");
  top.abella_pp = "exists";
}

abstract production nablaBinder
top::Binder::=
{
  top.pp = text("nabla");
  top.abella_pp = "nabla";
}




nonterminal Term with
   pp, abella_pp, isAtomic,
   typeEnv, constructorEnv, relationEnv,
   isStructured, headConstructor, isConstant,
   isUnknownTermI, isUnknownTermK, unknownId,
   unknownKReplaced, replaceUnknownK,
   substName, substTerm, subst<Term>,
   unifyWith<Term>, unifySuccess, unifyEqs, unifySubst,
   boundNames, usedNames,
   upSubst, downSubst, downVarTys, tyVars, type;
--note typeErrors does not include errors for not finding definitions of QNames
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm, downVarTys, replaceUnknownK on Term;
propagate unknownKReplaced on Term excluding unknownKTerm, nameTerm;

attribute compareTo, isEqual occurs on Term;
propagate compareTo, isEqual on Term
   excluding nameTerm, underscoreTerm;

aspect default production
top::Term ::=
{
  top.isUnknownTermI = false;
  top.isUnknownTermK = false;
  top.unknownId = nothing();
}


abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp = ppImplode(text(" "),
              (if f.isAtomic then f.pp else parens(f.pp))::args.pps);
  top.abella_pp = "(" ++ f.abella_pp ++ ") " ++ args.abella_pp;
  top.isAtomic = false;

  top.isStructured = true;

  top.headConstructor = f.headConstructor;

  top.isConstant = f.isConstant && args.isConstant;

  top.subst = applicationTerm(f.subst, args.subst);

  args.unifyWith =
      case top.unifyWith of
      | applicationTerm(_, a) -> ^a
      | _ -> error("Should not access")
      end;
  top.unifySuccess =
      case top.unifyWith of
      | applicationTerm(_, _) -> true
      | nameTerm(q, _) when !isConstantName(^q) -> true
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | applicationTerm(f2, _) -> (^f, ^f2)::args.unifyEqs
      | _ -> [] --shouldn't really access
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, ^top)]
      | _ -> [] --shouldn't really access
      end;

  top.type = ^appResult;
  local appResult::Type =
      varType("__AppResult" ++ toString(genInt()));
  --(arg ty 1) -> (arg ty 2) -> ... -> (arg ty n) -> appResult
  local argArrowType::Type =
      foldr(arrowType, ^appResult, args.types.toList);
  local unify::TypeUnify = typeUnify(f.type, @argArrowType);
  f.downSubst = top.downSubst;
  args.downSubst = f.upSubst;
  unify.downSubst = args.upSubst;
  top.upSubst = unify.upSubst;
}

abstract production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.pp =
      if mty.isJust
      then parens(ppConcat([name.pp, text(" : "), mty.pp]))
      else name.pp;
  top.abella_pp =
      if mty.isJust
      then "(" ++ name.abella_pp ++ " : " ++ mty.abella_pp ++ ")"
      else name.abella_pp;
  top.isAtomic = true;

  top.usedNames := if name.isQualified then [] else [name.shortName];

  top.isStructured = name.constrFound;
  top.isUnknownTermI = case name of
                       | unknownIQName(_) -> true
                       | _ -> false
                       end;
  top.isUnknownTermK = case name of
                       | unknownKQName(_) -> true
                       | _ -> false
                       end;
  top.unknownId =
      case name of
      | unknownIQName(_) when name.typeFound -> just(name.fullType.name)
      | unknownKQName(_) when name.relFound -> just(name.fullRel.name)
      | _ -> nothing()
      end;
  top.unknownKReplaced =
      case name of
      | unknownKQName(_) -> top.replaceUnknownK
      | _ -> ^top
      end;

  top.headConstructor = ^name;

  top.isConstant =
      if contains(name.shortName, top.boundNames)
      then false --bound var
      else name.constrFound;

  top.subst =
      if ^name == toQName(top.substName)
      then top.substTerm
      else ^top;

  top.unifySuccess =
      if isConstantName(^name)
      then case top.unifyWith of
           | nameTerm(q, _) when isConstantName(^q) -> ^q == ^name
           | nameTerm(x, _) -> true
           | _ -> false
           end
      else true;
  top.unifyEqs = []; --nothing more to unify here
  top.unifySubst =
      if isConstantName(^name)
      then case top.unifyWith of
           | nameTerm(x, _) -> [(x.shortName, ^top)]
           | _ -> []
           end
      else [(name.shortName, top.unifyWith)];

  top.type =
      case lookup(name.shortName, top.downVarTys) of
      | just(t) -> t
      | _ ->
        if name.constrFound
        then case name.fullConstr of
             | left(rel) ->
               freshenType(foldr1(arrowType, rel.types.toList))
             | right(con) -> freshenType(foldr(arrowType, con.type,
                                               con.types.toList))
             end
        else errorType()
      end;

  top.upSubst = top.downSubst;

  name.compareTo =
      case top.compareTo of
      | nameTerm(q, _) -> q
      | _ -> error("Should not access compareTo (nameTerm)")
      end;
  top.isEqual =
      case top.compareTo of
      | nameTerm(_, _) -> name.isEqual
      | _ -> false
      end;
}

abstract production consTerm
top::Term ::= t1::Term t2::Term
{
  top.pp = ppConcat([if t1.isAtomic then t1.pp else parens(t1.pp),
                     text("::"),
                     if t2.isAtomic then t2.pp else parens(t2.pp)]);
  top.abella_pp = "(" ++ t1.abella_pp ++ ")::(" ++ t2.abella_pp ++ ")";
  top.isAtomic = false;

  top.isStructured = true;

  top.headConstructor = error("consTerm.headConstructor not valid");

  top.subst = consTerm(t1.subst, t2.subst);

  top.isConstant = t1.isConstant && t2.isConstant;

  top.unifySuccess =
      case top.unifyWith of
      | consTerm(_, _) -> true
      | listTerm(c) -> c.len > 0
      | nameTerm(q, _) when !isConstantName(^q) -> true
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | consTerm(a, b) -> [(^t1, ^a), (^t2, ^b)]
      | listTerm(c) ->
        [(^t1, head(c.toList)),
         (^t2, foldr(consTerm, nilTerm(), tail(c.toList)))]
      | _ -> []
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, ^top)]
      | _ -> []
      end;

  --use this to ensure it has a list shape
  top.type = listType(t1.type);
  local unify::TypeUnify =
      typeUnify(listType(t1.type), t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify.downSubst = t2.upSubst;
  top.upSubst = unify.upSubst;
}

abstract production nilTerm
top::Term ::=
{
  top.pp = text("nil");
  top.abella_pp = "nil";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("nilTerm.headConstructor not valid");

  top.subst = ^top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | nilTerm() -> true
      | listTerm(c) -> c.len == 0
      | nameTerm(q, _) when !isConstantName(^q) -> true
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, ^top)]
      | _ -> []
      end;

  top.type = listType(varType("__Nil" ++ toString(genInt())));
  top.upSubst = top.downSubst;
}

abstract production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.pp =
      if mty.isJust
      then parens(cat(text("_ : "), mty.pp))
      else text("_");
  top.abella_pp =
      if mty.isJust
      then "(_ : " ++ mty.abella_pp ++ ")"
      else "_";

  top.isAtomic = true;

  top.isStructured = false;

  top.headConstructor =
      error("underscoreTerm.headConstructor not valid");

  top.subst = ^top;

  --shouldn't access isConstant on input
  top.isConstant = false;

  top.unifySuccess = true;
  top.unifyEqs = [];
  top.unifySubst = [];

  top.type =
      case mty of
      | justType(t) -> ^t
      | nothingType() ->
        varType("__Underscore" ++ toString(genInt()))
      end;
  top.upSubst = top.downSubst;

  top.isEqual =
      case top.compareTo of
      | underscoreTerm(_) -> true
      | _ -> false
      end;
}




nonterminal TermList with
   pps, abella_pp, toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames,
   substName, substTerm, subst<TermList>,
   unifyWith<TermList>, unifyEqs, unifySuccess,
   isStructuredList, isConstant,
   replaceUnknownK, unknownKReplaced,
   types, downSubst, upSubst, downVarTys, tyVars;
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm, downVarTys,
          replaceUnknownK, unknownKReplaced on TermList;

attribute compareTo, isEqual occurs on TermList;
propagate compareTo, isEqual on TermList;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pps = [if t.isAtomic then t.pp else parens(t.pp)];
  top.abella_pp = "(" ++ t.abella_pp ++ ")";

  top.toList = [^t];
  top.len = 1;

  top.isStructuredList = [t.isStructured];

  top.subst = singleTermList(t.subst);

  top.isConstant = t.isConstant;

  top.unifySuccess =
      case top.unifyWith of
      | singleTermList(_) -> true
      | consTermList(_, emptyTermList()) -> true
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | singleTermList(t2) -> [(^t, ^t2)]
      | consTermList(t2, _) -> [(^t, ^t2)]
      | _ -> []
      end;

  top.types = addTypeList(t.type, emptyTypeList());
  t.downSubst = top.downSubst;
  top.upSubst = t.upSubst;
}

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pps = (if t.isAtomic then t.pp else parens(t.pp))::rest.pps;
  top.abella_pp = "(" ++ t.abella_pp ++ ") " ++ rest.abella_pp;

  top.toList = ^t::rest.toList;
  top.len = 1 + rest.len;

  top.isStructuredList = t.isStructured::rest.isStructuredList;

  top.subst = consTermList(t.subst, rest.subst);

  top.isConstant = t.isConstant && rest.isConstant;

  rest.unifyWith =
      case top.unifyWith of
      | consTermList(_, r) -> ^r
      | _ -> emptyTermList() --valid for single, no better for empty
      end;
  top.unifySuccess =
      case top.unifyWith of
      | consTermList(_, _) -> rest.unifySuccess
      | singleTermList(_) -> rest.unifySuccess
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | consTermList(t2, _) -> (^t, ^t2)::rest.unifyEqs
      | singleTermList(t2) -> (^t, ^t2)::rest.unifyEqs
      | emptyTermList() -> []
      end;

  top.types = addTypeList(t.type, rest.types);
  t.downSubst = top.downSubst;
  rest.downSubst = t.upSubst;
  top.upSubst = rest.upSubst;
}

abstract production emptyTermList
top::TermList ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.isStructuredList = [];

  top.subst = ^top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | emptyTermList() -> true
      | _ -> false
      end;
  top.unifyEqs = [];

  top.types = emptyTypeList();
  top.upSubst = top.downSubst;
}

