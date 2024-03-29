grammar extensibella:common:abstractSyntax;


--METATERMS
abstract production translationMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term trans::Term
{
  top.pp = ppImplode(text(" "),
              args.pps ++ [ppConcat([text("|{"), ty.pp, text("}-")]),
                           orig.pp, text("~~>"), trans.pp]);
  top.abella_pp =
      (if args.len == 0 then "" else args.abella_pp ++ " ") ++
      "|{" ++ ty.abella_pp ++ "}- " ++ orig.abella_pp ++ " ~~> " ++
                                       trans.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unifyTransTy::TypeUnify =
      if ty.typeFound
      then typeUnify(nameType(ty.fullType.name), orig.type)
      else blankUnify();
  local unifyTerms::TypeUnify = typeUnify(orig.type, trans.type);
  local unifyArgs::TypeUnify =
      if ty.typeFound
      then typeUnify(
              --propType is a placeholder to make this easier to write
              foldr(arrowType, propType, ty.fullType.transTypes.toList),
              foldr(arrowType, propType, args.types.toList))
      else blankUnify();
  args.downSubst = top.downSubst;
  orig.downSubst = args.upSubst;
  trans.downSubst = orig.upSubst;
  unifyTransTy.downSubst = trans.upSubst;
  unifyTerms.downSubst = unifyTransTy.upSubst;
  unifyArgs.downSubst = unifyTerms.upSubst;
  top.upSubst = unifyArgs.upSubst;
}


{-
  Why don't we just put these operations in Term?  Then we could use
  something like `3+4` directly in the next addition.  That sounds
  wonderful, but it doesn't really fit the Abella style, and thus it
  would be really difficult to use.  We would not have a good way to
  use properties of the arithmetic operations, which are properties
  that need to be applied.

  The translation of the numeric operations will need to be dependent
  on typing once we add floats.
-}
abstract production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" + "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = integerAdditionName ++ " (" ++ t1.abella_pp ++
      ") (" ++ t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  local unify3::TypeUnify = typeUnify(integerType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" - "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = integerSubtractionName ++ " (" ++ t1.abella_pp ++
      ") (" ++ t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  local unify3::TypeUnify = typeUnify(integerType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" * "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = integerMultiplicationName ++ " (" ++ t1.abella_pp ++
      ") (" ++ t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  local unify3::TypeUnify = typeUnify(integerType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" / "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = integerDivisionName ++ " (" ++ t1.abella_pp ++
      ") (" ++ t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  local unify3::TypeUnify = typeUnify(integerType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" mod "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = integerModulusName ++ " (" ++ t1.abella_pp ++
      ") (" ++ t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  local unify3::TypeUnify = typeUnify(integerType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = ppConcat([text("- "), t.pp, text(" = "), result.pp]);
  top.abella_pp = integerNegateName ++ " (" ++ t.abella_pp ++ ") (" ++
                  result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t.type);
  local unify2::TypeUnify = typeUnify(integerType, result.type);
  t.downSubst = top.downSubst;
  result.downSubst = t.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = ppConcat([t1.pp, text(" < "), t2.pp]);
  top.abella_pp = integerLessName ++ " (" ++ t1.abella_pp ++
                  ") (" ++ t2.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify1.downSubst = t2.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = ppConcat([t1.pp, text(" <= "), t2.pp]);
  top.abella_pp = integerLessEqName ++ " (" ++ t1.abella_pp ++
                  ") (" ++ t2.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify1.downSubst = t2.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = ppConcat([t1.pp, text(" > "), t2.pp]);
  top.abella_pp = integerGreaterName ++ " (" ++ t1.abella_pp ++
                  ") (" ++ t2.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify1.downSubst = t2.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = ppConcat([t1.pp, text(" >= "), t2.pp]);
  top.abella_pp = integerGreaterEqName ++ " (" ++ t1.abella_pp ++
                  ") (" ++ t2.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(integerType, t1.type);
  local unify2::TypeUnify = typeUnify(integerType, t2.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  unify1.downSubst = t2.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}

--because we can do induction on append, should have a restriction
abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.pp = ppConcat([t1.pp, text(" ++ "), t2.pp, text(" = "),
                     result.pp, r.pp]);
  top.abella_pp = appendName ++ " (" ++ t1.abella_pp ++ ") (" ++
                  t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local lis::Type =
      listType(varType("__Append" ++ toString(genInt())));
  local unify1::TypeUnify = typeUnify(lis, t1.type);
  local unify2::TypeUnify = typeUnify(lis, t2.type);
  local unify3::TypeUnify = typeUnify(lis, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" || "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = orName ++ " (" ++ t1.abella_pp ++ ") (" ++
                  t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(boolType, t1.type);
  local unify2::TypeUnify = typeUnify(boolType, t2.type);
  local unify3::TypeUnify = typeUnify(boolType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp =
      ppConcat([t1.pp, text(" && "), t2.pp, text(" = "), result.pp]);
  top.abella_pp = andName ++ " (" ++ t1.abella_pp ++ ") (" ++
                  t2.abella_pp ++ ") (" ++ result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(boolType, t1.type);
  local unify2::TypeUnify = typeUnify(boolType, t2.type);
  local unify3::TypeUnify = typeUnify(boolType, result.type);
  t1.downSubst = top.downSubst;
  t2.downSubst = t1.upSubst;
  result.downSubst = t2.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  unify3.downSubst = unify2.upSubst;
  top.upSubst = unify3.upSubst;
}

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = ppConcat([text("! "), t.pp, text(" = "), result.pp]);
  top.abella_pp = notName ++ " (" ++ t.abella_pp ++ ") (" ++
                  result.abella_pp ++ ")";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify1::TypeUnify = typeUnify(boolType, t.type);
  local unify2::TypeUnify = typeUnify(boolType, result.type);
  t.downSubst = top.downSubst;
  result.downSubst = t.upSubst;
  unify1.downSubst = result.upSubst;
  unify2.downSubst = unify1.upSubst;
  top.upSubst = unify2.upSubst;
}


--Special relation applications for extSize and transRel
abstract production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = cat(ppImplode(text(" "),
                  ppConcat([text("<"), rel.pp, text(" {ES}>")]
                          )::args.pps), r.pp);
  top.abella_pp = "<" ++ rel.abella_pp ++ " {ES}> " ++
                  args.abella_pp ++ r.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify::TypeUnify =
      if rel.relFound
      then typeUnify( --end with integer because ES adds integer
              foldr(arrowType, integerType, rel.fullRel.types.toList),
              foldr(arrowType, integerType, args.types.toList))
      else blankUnify();
  args.downSubst = top.downSubst;
  unify.downSubst = args.upSubst;
  top.upSubst = unify.upSubst;
}

abstract production transRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = cat(ppImplode(text(" "),
                  ppConcat([text("<"), rel.pp, text(" {T}>")]
                          )::args.pps), r.pp);
  top.abella_pp = "<" ++ rel.abella_pp ++ " {T}> " ++
                  args.abella_pp ++ r.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];

  local unify::TypeUnify =
      if rel.relFound
      then typeUnify(
              foldr(arrowType, propType, rel.fullRel.types.toList),
              foldr(arrowType, propType, args.types.toList))
      else blankUnify();
  args.downSubst = top.downSubst;
  unify.downSubst = args.upSubst;
  top.upSubst = unify.upSubst;
}





--TERMS
abstract production unknownTerm
top::Term ::= ty::QName
{
  top.pp = ppConcat([text("<unknown "), ty.pp, text(">")]);
  top.abella_pp = "<unknown " ++ ty.abella_pp ++ ">";
  top.isAtomic = true;

  top.isStructured = true;
  top.isUnknownTerm = true;

  top.headConstructor =
      error("unknownTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | unknownTerm(ty2) -> ty == ty2
      | nameTerm(q, _) when !q.isQualified -> true
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type =
      if ty.typeFound
      then nameType(ty.fullType.name)
      else errorType();
  top.upSubst = top.downSubst;
}

abstract production intTerm
top::Term ::= i::Integer
{
  top.pp = text(toString(i));
  top.abella_pp = integerToIntegerTerm(i).abella_pp;
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("intTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | intTerm(j) -> i == j
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = integerType;
  top.upSubst = top.downSubst;
}

abstract production stringTerm
top::Term ::= contents::String
{
  top.pp = text("\"" ++ contents ++ "\"");
  top.abella_pp = "\"" ++ contents ++ "\"";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("stringTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | stringTerm(s) -> contents == s
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = stringType();
  top.upSubst = top.downSubst;
}

abstract production trueTerm
top::Term ::=
{
  top.pp = text("true");
  top.abella_pp = trueName;
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("trueTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | trueTerm() -> true
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = boolType;
  top.upSubst = top.downSubst;
}

abstract production falseTerm
top::Term ::=
{
  top.pp = text("false");
  top.abella_pp = falseName;
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("falseTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | falseTerm() -> true
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = boolType;
  top.upSubst = top.downSubst;
}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = ppConcat([text("["), ppImplode(text(", "), contents.pps),
                     text("]")]);
  top.abella_pp = contents.abella_pp;
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("listTerm.headConstructor not valid");

  top.subst = listTerm(contents.subst);

  top.isConstant = contents.isConstant;

  top.unifySuccess =
      case top.unifyWith of
      | listTerm(c) -> contents.len == c.len
      | consTerm(_, _) -> contents.len > 0
      | nilTerm() -> contents.len == 0
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | listTerm(c) -> zip(contents.toList, c.toList)
      | consTerm(a, b) ->
        [(head(contents.toList), a),
         (foldr(consTerm, nilTerm(), tail(contents.toList)), b)]
      | _ -> []
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = listType(contents.type);
  contents.downSubst = top.downSubst;
  top.upSubst = contents.upSubst;
}

abstract production pairTerm
top::Term ::= contents::PairContents
{
  top.pp = ppConcat([text("("), ppImplode(text(", "), contents.pps),
                     text(")")]);
  top.abella_pp = contents.abella_pp;
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("pairTerm.headConstructor not valid");

  top.subst = pairTerm(contents.subst);

  top.isConstant = contents.isConstant;

  top.unifySuccess =
      case top.unifyWith of
      | pairTerm(c) -> contents.len == c.len
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | pairTerm(c) ->
        zip(contents.toList, c.toList)
      | _ -> []
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = contents.type;
  contents.downSubst = top.downSubst;
  top.upSubst = contents.upSubst;
}

abstract production charTerm
top::Term ::= char::String
{
  top.pp = text("\"" ++ char ++ "\"");
  top.abella_pp = "\"" ++ char ++ "\"";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("charTerm.headConstructor not valid");

  top.subst = top;

  top.isConstant = true;

  top.unifySuccess =
      case top.unifyWith of
      | charTerm(c) -> char == c
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;

  top.type = stringType();
  top.upSubst = top.downSubst;
}




nonterminal ListContents with
   pps, abella_pp,
   toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   substName, substTerm, subst<ListContents>,
   boundNames, usedNames,
   isConstant,
   type, upSubst, downSubst, downVarTys, tyVars; --type is type of contents
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm, downVarTys on ListContents;

attribute compareTo, isEqual occurs on ListContents;
propagate compareTo, isEqual on ListContents;

abstract production emptyListContents
top::ListContents ::=
{
  top.pps = [];
  top.abella_pp = "nil";
  top.toList = [];
  top.len = 0;
  top.subst = top;

  top.isConstant = true;

  top.type = varType("__EmptyListContents" ++ toString(genInt()));
  top.upSubst = top.downSubst;
}

abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pps = t.pp::rest.pps;
  top.abella_pp = "(" ++ t.abella_pp ++ ")::" ++ rest.abella_pp;
  top.toList = t::rest.toList;
  top.len = 1 + rest.len;
  top.subst = addListContents(t.subst, rest.subst);

  top.isConstant = t.isConstant && rest.isConstant;

  top.type = t.type;

  local unify::TypeUnify = typeUnify(t.type, rest.type);
  t.downSubst = top.downSubst;
  rest.downSubst = t.upSubst;
  top.upSubst = rest.upSubst;
}




nonterminal PairContents with
   pps, abella_pp,
   toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   substName, substTerm, subst<PairContents>,
   boundNames, usedNames,
   isConstant,
   type, upSubst, downSubst, downVarTys, tyVars; --type is full pair type
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm, downVarTys on PairContents;

attribute compareTo, isEqual occurs on PairContents;
propagate compareTo, isEqual on PairContents;

abstract production singlePairContents
top::PairContents ::= t::Term
{
  top.pps = [t.pp];
  top.abella_pp = t.abella_pp;
  top.toList = [t];
  top.len = 1;
  top.subst = singlePairContents(t.subst);

  top.isConstant = true;

  top.type = t.type;
  t.downSubst = top.downSubst;
  top.upSubst = t.upSubst;
}

abstract production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.pps = t.pp::rest.pps;
  top.abella_pp = pairConstructorName ++ " (" ++ t.abella_pp ++
                  ") (" ++ rest.abella_pp ++ ")";
  top.toList = t::rest.toList;
  top.len = 1 + rest.len;
  top.subst = addPairContents(t.subst, rest.subst);

  top.isConstant = true;

  top.type = functorType(functorType(nameType(toQName("pair")),
                            t.type), rest.type);
  t.downSubst = top.downSubst;
  rest.downSubst = t.upSubst;
  top.upSubst = rest.upSubst;
}

