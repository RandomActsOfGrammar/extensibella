grammar extensibella:toAbella:abstractSyntax;

abstract production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.pp = text("Projection_Constraint ") ++ name.pp ++ text(" :") ++
      line() ++ text("forall ") ++ ppImplode(text(" "), binds.pps) ++
      text(",") ++ line() ++ body.pp ++ text(".") ++ realLine();
  top.abella_pp =
      "Projection_Constraint " ++ name.abella_pp ++ " : " ++
      "forall " ++ binds.abella_pp ++ ", " ++ body.abella_pp ++ ".\n";

  production fullName::QName =
      if name.isQualified
      then ^name
      else addQNameBase(top.currentModule, name.shortName);

  body.boundNames = binds.usedNames;
  body.specialIHNames = [];

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
        foldl(\ rest::[String] p::(Maybe<String>, Metaterm) ->
                case p.1 of
                | just(x) -> rest ++ [x]
                | nothing() -> rest ++
                  --using "H" as base triggers an Abella error
                  [freshName("Hyp", rest ++ labels)]
                end,
              [], body.premises);

  local projTy::QName =
      case body.premises of
      | (_, projectionMetaterm(_, ty, _, _))::_ -> ^ty
      | _ -> error("Should not access projTy")
      end;
  projTy.typeEnv = top.typeEnv;
  local fullType::TypeEnvItem = projTy.fullType;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared projection constraint name " ++
                    justShow(name.pp) ++ " does not have correct " ++
                    "module (expected " ++
                    justShow(top.currentModule.pp) ++ ")")]
      else [];
  --check there are premises, the first premise is a projection,
  --   and the projection is for a type from the same module
  top.toAbellaMsgs <-
      case body.premises of
      | [] -> [errorMsg("Projection constraint " ++
                  justShow(name.pp) ++ " must have premises")]
      | (_, projectionMetaterm(_, q, _, _))::_ ->
        let decQ::Decorated QName with {typeEnv} =
            decorate ^q with {typeEnv = top.typeEnv;}
        in
          if !decQ.typeFound ||
             sameModule(top.currentModule, decQ.fullType.name)
          then []
          else [errorMsg("New projection constraints must be for " ++
                   "new types; " ++ justShow(decQ.fullType.name.pp) ++
                   " is imported")]
        end
      | (_, m)::_ ->
        [errorMsg("First premise in projection constraint " ++
            justShow(name.pp) ++ " must be a projection; found " ++
            justShow(m.pp))]
      end;
  --check there are no existing theorems with this full name
  top.toAbellaMsgs <-
      if null(findTheorem(^fullName, top.proverState))
      then []
      else [errorMsg("Theorem named " ++ justShow(fullName.pp) ++
                     " already exists")];

  --check the body is well-typed
  top.toAbellaMsgs <-
      case body.upSubst of
      | right(_) -> []
      | left(_) ->
        --given the messages are not terribly useful:
        [errorMsg("Type error in " ++ justShow(name.pp))]
      end;
  body.downVarTys =
      map(\ p::(String, MaybeType) ->
            (p.1,
             case p.2 of
             | justType(t) -> ^t
             | nothingType() -> varType("__X" ++ toString(genInt()))
             end),
          binds.toList);
  body.downSubst = emptySubst();

  top.toAbella =
      [anyTopCommand(theoremDeclaration(^fullName, [],
          bindingMetaterm(forallBinder(), ^binds, body.toAbella))),
       anyProofCommand(introsTactic(introsNames)),
       anyProofCommand(caseTactic(nameHint(head(introsNames)),
          head(introsNames), true))];

  top.provingTheorems = [(^fullName, body.thm)];

  --no skips at declaration time, so no during commands
  top.duringCommands = [];

  top.afterCommands = [];

  top.is_nonextensible = false;
}


abstract production proveConstraint
top::TopCommand ::= name::QName
{
  top.pp = text("Prove_Constraint ") ++ name.pp ++ text(".") ++
           realLine();
  top.abella_pp =
      error("Should not access proveConstraint.abella_pp");

  --check for the expected theorems being proven
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | projectionConstraintTheorem(q, x, b, _)::_ ->
        if ^name == ^q
        then []
        else [errorMsg("Expected projection constraint obligation" ++
                 " " ++ justShow(q.pp))]
      | l -> [wrongObligation(l)]
      end;

  local obligation::(QName, Bindings, ExtBody) =
      case head(top.proverState.remainingObligations) of
      | projectionConstraintTheorem(q, x, b, _) -> (^q, ^x, ^b)
      | _ -> error("Not possible (length top.toAbellaMsgs = " ++
                   toString(length(top.toAbellaMsgs)) ++ ")")
      end;
  local binds::Bindings = obligation.2;
  local body::ExtBody = obligation.3;
  body.boundNames = binds.usedNames;
  body.typeEnv = top.typeEnv;
  body.relationEnv = top.relationEnv;
  body.constructorEnv = top.constructorEnv;

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
        foldl(\ rest::[String] p::(Maybe<String>, Metaterm) ->
                case p.1 of
                | just(x) -> rest ++ [x]
                | nothing() -> rest ++
                  --using "H" as base triggers an Abella error
                  [freshName("Hyp", rest ++ labels)]
                end,
              [], body.premises);

  local projTy::QName =
      case body.premises of
      | (_, projectionMetaterm(_, ty, _, _))::_ -> ^ty
      | _ -> error("Should not access projTy")
      end;
  projTy.typeEnv = top.typeEnv;
  local fullType::TypeEnvItem = projTy.fullType;

  top.provingTheorems =
      [(obligation.1,
        bindingMetaterm(forallBinder(), obligation.2,
           obligation.3.thm))];

  --for the subgoals that should arise, the last digit of the subgoal
  --number and whether we need to prove it
  local expectedSubgoals::[(Integer, Boolean)] =
      foldl(\ thusFar::(Integer, [(Integer, Boolean)]) now::QName ->
              if now == top.currentModule --new constr
              then (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, true)])
              else (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, false)]),
            (1, []), fullType.clauseModules).2;
  --group consecutive skips
  local groupedExpectedSubgoals::[[(Integer, Boolean)]] =
      groupBy(\ p1::(Integer, Boolean) p2::(Integer, Boolean) ->
                p1.2 == p2.2,
              expectedSubgoals);
  --last digit of subgoal and skips needed
  local subgoalDurings::[(Integer, [ProofCommand])] =
      flatMap(\ l::[(Integer, Boolean)] ->
                if !null(l) && !head(l).2 --things we don't do we skip
                then [(head(l).1,
                       map(\ x::(Integer, Boolean) ->
                             skipTactic(), l))]
                else [], --nothing for things we need to prove
              groupedExpectedSubgoals);
  --turned into full subgoals
  local subgoalDuringCommands::[(SubgoalNum, [ProofCommand])] =
      map(\ p::(Integer, [ProofCommand]) -> ([p.1], p.2),
          subgoalDurings);

  local hasInitialSkips::Boolean =
      !null(subgoalDuringCommands) && head(subgoalDurings).1 == 1;

  top.toAbella =
      [anyTopCommand(theoremDeclaration(obligation.1, [],
          bindingMetaterm(forallBinder(), ^binds, body.toAbella))),
       anyProofCommand(introsTactic(introsNames)),
       anyProofCommand(caseTactic(nameHint(head(introsNames)),
          head(introsNames), true))] ++
      --add any initial skips
      if hasInitialSkips
      then map(anyProofCommand, head(subgoalDuringCommands).2)
      else [];

  --This shouldn't be accessed if we have errors, but it is
  --I should figure this out at some point
  top.duringCommands =
      if null(top.toAbellaMsgs)
      then if hasInitialSkips
           then tail(subgoalDuringCommands)
           else subgoalDuringCommands
      else [];

  top.afterCommands = [];

  top.is_nonextensible = false;
}
