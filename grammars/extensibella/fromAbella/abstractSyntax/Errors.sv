grammar extensibella:fromAbella:abstractSyntax;





nonterminal WarningMessage with
   pp,
   fromAbella<WarningMessage>;

abstract production stratificationWarning
top::WarningMessage ::= name::QName
{
  top.pp = text("Definition might not be stratified") ++ realLine() ++
      text("(\"") ++ name.pp ++ text("\" occurs to the left of ->)");

  top.fromAbella = stratificationWarning(^name);
}


abstract production defeatStratification
top::WarningMessage ::= name::QName
{
  top.pp = text("Definition can be used to defeat stratification") ++
           realLine() ++ text(" (higher-order argument \"") ++
           name.pp ++ text("\" occurs to the left of ->)");

  top.fromAbella = defeatStratification(^name);
}


abstract production overridingLemma
top::WarningMessage ::= name::QName
{
  top.pp = text("overriding existing lemma named \"") ++ name.pp ++
           text("\"");

  top.fromAbella = overridingLemma(^name);
}





nonterminal ProcessingErrorMessage with
   pp,
   fromAbella<ProcessingErrorMessage>,
   typeEnv, relationEnv, constructorEnv;
propagate typeEnv, relationEnv, constructorEnv
   on ProcessingErrorMessage;

abstract production undeterminedVarType
top::ProcessingErrorMessage ::=
{
  top.pp = text("Types of variables are not fully determined");

  top.fromAbella = undeterminedVarType();
}


abstract production searchFailure
top::ProcessingErrorMessage ::=
{
  top.pp = text("Search failed");

  top.fromAbella = searchFailure();
}


abstract production unknownHypLemma
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Could not find hypothesis or lemma ") ++ name.pp;

  top.fromAbella = unknownHypLemma(name.fromAbella);
}


abstract production unknownConstant
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown constant: " ++ name);

  top.fromAbella = unknownConstant(name);
}


abstract production importedUnknownTy
top::ProcessingErrorMessage ::= names::[String]
{
  top.pp = text("Imported file makes reference to unknown types:") ++
           line() ++ ppImplode(text(",") ++ line(), map(text, names));

  top.fromAbella = importedUnknownTy(names);
}


abstract production invalidFormula
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = text("Invalid formula: ") ++ formula.pp ++ realLine() ++
           text("Cannot use size restrictions (*, @, #, or +)");

  top.fromAbella = invalidFormula(formula.fromAbella);
}


abstract production unboundedTyVars
top::ProcessingErrorMessage ::=
{
  top.pp = text("Some type variables in the theorem are not bounded");

  top.fromAbella = unboundedTyVars();
}


abstract production alreadyDefined
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Predicate or constant ") ++ name.pp ++
           text(" already exists");

  top.fromAbella = alreadyDefined(^name);
}


abstract production invalidCapDefName
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Invalid defined predicate name \"") ++ name.pp ++
           text("\".") ++ realLine() ++ text(" Defined predicates") ++
           text(" may not begin with a capital letter.");

  top.fromAbella = invalidCapDefName(^name);
}


abstract production invalidCapConstName
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Constants may not begin with a capital letter: ") ++
           name.pp;

  top.fromAbella = invalidCapConstName(^name);
}


abstract production strayClause
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Found stray clause for " ++ name);

  top.fromAbella = strayClause(name);
}


abstract production invalidHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = text("Invalid head in definition:") ++ line() ++
           formula.pp;

  top.fromAbella = invalidHead(formula.fromAbella);
}


abstract production nonatomicHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = text("Definitional clause head not atomic:") ++
           realLine() ++ formula.pp;

  top.fromAbella = nonatomicHead(formula.fromAbella);
}


abstract production caseUndefinedAtom
top::ProcessingErrorMessage ::=
{
  top.pp = text("Cannot perform case-analysis on undefined atom");

  top.fromAbella = caseUndefinedAtom();
}


abstract production caseThisKind
top::ProcessingErrorMessage ::=
{
  top.pp = text("Cannot perform case-analysis on this kind of formula");

  top.fromAbella = caseThisKind();
}


abstract production unknownHypVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown hypothesis or variable " ++ name);

  top.fromAbella = unknownHypVar(name);
}


abstract production unknownTheorem
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Could not find theorem named \"" ++ name ++ "\"");

  top.fromAbella = unknownTheorem(name);
}


abstract production unknownVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown variable " ++ name);

  top.fromAbella = unknownVar(name);
}


abstract production inductPredJudg
top::ProcessingErrorMessage ::=
{
  top.pp = text("Can only induct on predicates and judgments");

  top.fromAbella = inductPredJudg();
}


abstract production inductUndefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Cannot induct on " ++ name ++
                " since it has not been defined");

  top.fromAbella = inductUndefined(name);
}


abstract production tooManyInductions
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = text("Expecting " ++ toString(expected) ++
                " induction arguments but got " ++ toString(got));

  top.fromAbella = tooManyInductions(expected, got);
}


abstract production needlessSplit
top::ProcessingErrorMessage ::=
{
  top.pp = text("Needless use of split");

  top.fromAbella = needlessSplit();
}


abstract production cannotSplit
top::ProcessingErrorMessage ::=
{
  top.pp = text("Cannot split this type of theorem");

  top.fromAbella = cannotSplit();
}


abstract production nameExistingHyp
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("\"" ++ name ++
                "\" already refers to an existing hypothesis");

  top.fromAbella = nameExistingHyp(name);
}


abstract production nameExistingLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("\"" ++ name ++ "\" already refers to a lemma");

  top.fromAbella = nameExistingLemma(name);
}


abstract production nameExistingVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("\"" ++ name ++
                "\" already refers to an existing variable");

  top.fromAbella = nameExistingVar(name);
}


abstract production unknownVarHypLabel
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown variable or hypothesis label \"" ++
                name ++ "\"");

  top.fromAbella = unknownVarHypLabel(name);
}


abstract production cannotGoBack
top::ProcessingErrorMessage ::=
{
  top.pp = text("Cannot go that far back!");

  top.fromAbella = cannotGoBack();
}


abstract production matchingUnificationFailureConstants
top::ProcessingErrorMessage ::= argnum::Integer const1::QName const2::QName
{
  top.pp = text("While matching argument #" ++ toString(argnum) ++
                ":") ++ realLine() ++
           text("Unification failure (constant clash between ") ++
           const1.pp ++ text(" and ") ++ const2.pp ++ text(")");

  top.fromAbella =
      matchingUnificationFailureConstants(argnum, ^const1, ^const2);
}


abstract production matchingUnificationFailure
top::ProcessingErrorMessage ::= argnum::Integer
{
  top.pp = text("While matching argument #" ++ toString(argnum) ++
                ":") ++ realLine() ++ text("Unification failure");

  top.fromAbella = matchingUnificationFailure(argnum);
}


abstract production unificationFailure
top::ProcessingErrorMessage ::=
{
  top.pp = text("Unification failure");

  top.fromAbella = unificationFailure();
}


abstract production tyConstrInconsistentKinds
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Type constructor ") ++ name.pp ++
           text(" has inconsistent kind declarations");

  top.fromAbella = tyConstrInconsistentKinds(^name);
}


abstract production tyNoCaps
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = text("Types may not begin with a capital letter: ") ++
           name.pp;

  top.fromAbella = tyNoCaps(^name);
}


abstract production unknownTyConstr
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown type constructor: " ++ name);

  top.fromAbella = unknownTyConstr(name);
}


abstract production wrongArgNumber
top::ProcessingErrorMessage ::= name::QName expected::Integer
                                given::Integer
{
  top.pp = name.pp ++ text(" expects " ++ toString(expected) ++
           " arguments but has " ++ toString(given));

  top.fromAbella = wrongArgNumber(^name, expected, given);
}


abstract production noQuantifyProp
top::ProcessingErrorMessage ::=
{
  top.pp = text("Cannot quantify over type prop");

  top.fromAbella = noQuantifyProp();
}


abstract production unknownSettingKey
top::ProcessingErrorMessage ::= name::String
{
  top.pp = text("Unknown key '" ++ name ++ "'");

  top.fromAbella = unknownSettingKey(name);
}


abstract production unknownSettingsValueExpectInt
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = text("Unknown value '" ++ val ++ "' for key \"" ++ key ++
                "\"; expected non-negative integer");

  top.fromAbella = unknownSettingsValueExpectInt(val, key);
}


abstract production unknownSettingsValueExpectOnOff
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = text("Unknown value '" ++ val ++ "' for key \"" ++ key ++
                "\"; expected 'on' or 'off'");

  top.fromAbella = unknownSettingsValueExpectOnOff(val, key);
}


abstract production unknownSettingsValueExpectMany
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = text("Unknown value '" ++ val ++ "' for key \"" ++ key ++
                "\"; expected 'on', 'off', non-negative integer, or " ++
                "depth specification");

  top.fromAbella = unknownSettingsValueExpectMany(val, key);
}


abstract production applyWrongArgsNumber
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = text(
      ( if expected > got
        then "Not enough"
        else "Too many" ) ++
      " arguments to apply\n(Expected " ++ toString(expected) ++
      " but got " ++ toString(got) ++ ")");

  top.fromAbella = applyWrongArgsNumber(expected, got);
}


abstract production logicVariableToplevel
top::ProcessingErrorMessage ::=
{
  top.pp = text("Found logic variable at toplevel");

  top.fromAbella = logicVariableToplevel();
}


abstract production appliedStructure
top::ProcessingErrorMessage ::=
{
  top.pp = text("Structure of applied term must be a substructure " ++
                "of the following.") ++ realLine() ++
      text("forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C");

  top.fromAbella = appliedStructure();
}


abstract production inductiveRestrictionViolated
top::ProcessingErrorMessage ::=
{
  top.pp = text("Inductive restriction violated");

  top.fromAbella = inductiveRestrictionViolated();
}


abstract production noMatchingClauses
top::ProcessingErrorMessage ::=
{
  top.pp = text("No matching clauses");

  top.fromAbella = noMatchingClauses();
}


abstract production strictSubtermsRestrictions
top::ProcessingErrorMessage ::= m::Metaterm
{
  top.pp = text("Inductive restrictions must not occur in strict subterms:\n") ++ m.pp;

  top.fromAbella = strictSubtermsRestrictions(m.fromAbella);
}





nonterminal TypingErrorMessage with
   pp,
   fromAbella<TypingErrorMessage>,
   typeEnv;
propagate typeEnv on TypingErrorMessage;

abstract production badTypeUsage
top::TypingErrorMessage ::= hasType::Type usedType::Type
{
  top.pp = text("Expression has type ") ++ hasType.pp ++
           text(" but is used here with type ") ++ usedType.pp ++
           text(".");

  top.fromAbella =
      badTypeUsage(hasType.fromAbella, usedType.fromAbella);
}


abstract production tooManyArguments
top::TypingErrorMessage ::=
{
  top.pp = text("Expression is applied to too many arguments");

  top.fromAbella = tooManyArguments();
}





attribute
   fromAbella<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.fromAbella = arrowType(ty1.fromAbella, ty2.fromAbella);
}


aspect production nameType
top::Type ::= name::QName
{
  top.fromAbella = nameType(name.tyFromAbella);
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.fromAbella =
      case functorTy, argTy of
      | nameType(basicQName(baseName("list"))),
        nameType(basicQName(baseName("$char"))) -> stringType()
      | _, _ ->
        functorType(functorTy.fromAbella, argTy.fromAbella)
      end;
}


aspect production varType
top::Type ::= name::String
{
  top.fromAbella = ^top;
}


aspect production errorType
top::Type ::=
{
  top.fromAbella = error("errorType.fromAbella");
}





attribute
   fromAbella<MaybeType>
occurs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.fromAbella = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.fromAbella = justType(ty.fromAbella);
}
