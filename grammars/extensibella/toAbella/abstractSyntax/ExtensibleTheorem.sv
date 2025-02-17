grammar extensibella:toAbella:abstractSyntax;


abstract production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.pp = text("Extensible_Theorem") ++
           nest(3, realLine() ++ ppImplode(text(",") ++ realLine(),
                                           thms.pps)) ++
           (if alsos.len == 0 then text("")
            else text("also") ++ realLine() ++
                 nest(3, realLine() ++
                         ppImplode(text(",") ++ realLine(),
                                   alsos.pps))) ++
           text(".") ++ realLine();
  --need this for compilation
  top.abella_pp = "Extensible_Theorem " ++ thms.abella_pp ++
      (if alsos.len == 0 then "" else " also " ++ alsos.abella_pp) ++ ".\n";

  production extName::QName =
      if thms.len + alsos.len > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(thms.provingTheorems).1;

  top.toAbella =
      if null(thms.extIndChecks)
      then extThmCmds
      else extIndCheckStart;

  local extThmCmds::[AnyCommand] =
      --declare theorems
      [anyTopCommand(theoremDeclaration(^extName, [], ^fullThms))] ++
      --declare inductions
      map(\ l::[Integer] ->
            anyProofCommand(inductionTactic(noHint(), l)),
          transpose(thms.inductionNums ++ alsos.inductionNums)) ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          thms.renamedIHs ++ alsos.renamedIHs) ++
      --split
      (if thms.len + alsos.len > 1
       then [anyProofCommand(splitTactic())] else []) ++
      --initial set of during commands, which is at least intros
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm
  production fullThms::Metaterm =
      if alsos.len > 0
      then andMetaterm(thms.toAbella, alsos.toAbella)
      else thms.toAbella;

  local extIndCheck::Metaterm =
      foldr1(andMetaterm,
         map(fst, thms.extIndChecks) ++
         [bindingMetaterm(existsBinder(),
             oneBinding("$", justType(integerType)),
             ^fullThms)]);
  --during commands for extIndCheck, including declaration of ExtThm
  local extIndCheckCmds::[(SubgoalNum, [ProofCommand])] =
      --intros for each check
      map(\ p::(Integer, Metaterm, [ProofCommand]) -> ([p.1], p.3),
          enumerateFrom(1, thms.extIndChecks)) ++
      --exists to remove binding from front, then set-up for ExtThm
      [([length(thms.extIndChecks) + 1],
        existsTactic(oneEWitnesses(termEWitness(integerToIntegerTerm(0))))::
        map(\ a::AnyCommand -> case a of
                               | anyProofCommand(p) -> ^p
                               | _ -> error("only proof commands")
                               end, tail(extThmCmds)))];
  local extIndCheckStart::[AnyCommand] =
      --declare checks
      [anyTopCommand(
          theoremDeclaration(toQName("$ExtIndCheck_" ++ toString(genInt())),
             [], ^extIndCheck)),
      --split (must split because at least 1 + true)
       anyProofCommand(splitTactic())] ++
      --intros/set-up for first one
      map(anyProofCommand, head(extIndCheckCmds).2);

  top.provingTheorems = thms.provingTheorems ++ alsos.provingTheorems;

  top.duringCommands =
      if null(thms.extIndChecks)
      then tail(thms.duringCommands)
      else tail(extIndCheckCmds) ++ tail(thms.duringCommands);

  top.afterCommands =
      if !null(thms.extIndChecks)
      then flatMap(\ p::(QName, Metaterm) ->
                     [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                      anyProofCommand(skipTactic())],
                   zip(map(fst, thms.provingTheorems ++ alsos.provingTheorems),
                       splitMetaterm(^fullThms)))
      else if thms.len + alsos.len == 1
      then [] --nothing to do after if there is only one being proven
      else [anyTopCommand(splitTheorem(^extName,
               map(fst, thms.provingTheorems ++ alsos.provingTheorems)))];

  top.keyRelModules = thms.keyRelModules ++ alsos.keyRelModules;

  thms.startingGoalNum =
       if null(thms.extIndChecks)
       then if thms.len + alsos.len > 1
            then [1]
            else [] --only one thm, so subgoals for it are 1, 2, ...
       else if thms.len + alsos.len > 1
            --same, but under subgoal after ExtInd validity check
            then [length(thms.extIndChecks) + 1, 1]
            else [length(thms.extIndChecks) + 1];

  --find extInd if needed for the relations
  local extIndGroup::Maybe<[(QName, [String], Bindings,
                             ExtIndPremiseList)]> =
      findExtIndGroup(head(thms.keyRels), top.proverState);
  --need extInd for all if any relations are imported
  local importedKeyRels::[QName] =
      filter(\ r::QName -> !sameModule(top.currentModule, r),
             thms.keyRels);
  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else if !extIndGroup.isJust
      then [errorMsg("Did not find Ext_Ind required for induction " ++
                     "on relations " ++
                     implode(", ",
                        map(justShow, map((.pp), importedKeyRels))))]
      else let missing::[QName] =
               case extIndGroup of
               | just(eg) ->
                 removeAll(map(fst, eg), thms.keyRels)
               | nothing() -> error("toAbellaMsgs:  let missing")
               end
           in
             if null(missing)
             then []
             else [errorMsg("Ext_Ind group does not include " ++
                            "key relations " ++
                            implode(", ",
                               map(justShow, map((.pp), missing))))]
           end;
  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else if alsos.len > 0
      then [errorMsg("Cannot have also theorems when using Ext_Ind")]
      else [];

  --check for naming IH's the same thing
  top.toAbellaMsgs <-
      foldl(\ rest::([(String, String)], [Message])
              p::(String, String, String) ->
              case lookup(p.2, rest.1) of
              | just(thm) ->
                (rest.1, errorMsg("IH name " ++ p.2 ++
                            " already used by " ++ thm)::rest.2)
              | nothing() -> ((p.2, p.3)::rest.1, rest.2)
              end, ([], []), thms.renamedIHs ++ alsos.renamedIHs).2;

  --check for naming thms the same thing
  top.toAbellaMsgs <-
      map(\ q::QName ->
            errorMsg("Theorem " ++ justShow(q.pp) ++ " is declared " ++
                     "multiple times"),
                               --(seen,    multiple)
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else if contains(q, rest.2)
                  then (rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), thms.thmNames ++ alsos.thmNames).2);

  --check all use the same number of inductions
  top.toAbellaMsgs <-
      case nub(thms.numsInductions ++ alsos.numsInductions) of
      | [_] -> [] --all are the same
      | _ -> --must have been at least one number, so this is at least
             --   two different numbers of inductions
        [errorMsg("Not all mutual theorems declare the same number" ++
                  " of inductions")]
      end;

  thms.useExtInd = if null(importedKeyRels) || !extIndGroup.isJust
                   then []
                   else case extIndGroup of
                        | just(eg) -> eg
                        | nothing() -> error("thms.useExtInd")
                        end;
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  thms.expectedIHNum = 0;
  thms.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  thms.numMutualThms = thms.len + alsos.len;

  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];
  alsos.startingGoalNum = thms.nextGoalNum;
  alsos.useExtInd = []; --don't need anything here
  alsos.expectedIHNum = thms.len;
  alsos.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  alsos.numMutualThms = thms.len + alsos.len;

  top.is_nonextensible = false;
}


abstract production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.pp = text("Prove ") ++ nest(6, ppImplode(text(",") ++ line(),
                                        map((.pp), names))) ++
           (if newThms.len > 0
            then realLine() ++ text("with") ++
                 nest(3, realLine() ++
                         ppImplode(text(",") ++ realLine(),
                                   newThms.pps))
            else text("")) ++
           (if newAlsos.len > 0
            then realLine() ++ text("also") ++
                 nest(3, realLine() ++
                         ppImplode(text(",") ++ realLine(),
                                   newAlsos.pps))
            else text("")) ++
           text(".") ++ realLine();
  top.abella_pp =
      error("proveObligations.abella_pp should not be accessed");

  --check for the expected theorems being proven
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | extensibleMutualTheoremGroup(thms, alsos, _)::_ ->
        let expectedNames::[QName] = map(fst, thms)
        in
        let expectedAlsoNames::[QName] = map(fst, alsos)
        in
          if setEq(names, expectedNames)
          then []
          else if subset(names, expectedNames)
          then let missing::[QName] = removeAll(names, expectedNames)
               in
                 [errorMsg("Missing mutually-inductive obligation" ++
                    (if length(missing) == 1 then " " else "s ") ++
                    implode(", ", map(justShow,
                       map((.pp), removeAll(names, expectedNames)))))]
               end
          else if subset(expectedNames, names)
          then let extras::[QName] = removeAll(expectedNames, names)
               in
                 if subset(extras, expectedAlsoNames)
                 then [errorMsg("Should not include names for also theorems " ++
                          implode(", ", map(justShow, map((.pp), extras))))]
                 else [errorMsg("Too many mutually-inductive obligations;" ++
                          " should not have " ++
                          implode(", ", map(justShow, map((.pp), extras))))]
               end
          else [errorMsg("Expected inductive obligation" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ", map(justShow,
                                         map((.pp), expectedNames))) ++
                   if null(alsos) then ""
                   else " also " ++
                        implode(", ", map(justShow,
                                          map((.pp), map(fst, alsos)))))]
        end end
      | l -> [wrongObligation(l)]
      end;

  --find extInd if needed for the relations
  local extIndGroup::Maybe<[(QName, [String], Bindings,
                             ExtIndPremiseList)]> =
      findExtIndGroup(head(thms.keyRels), top.proverState);
  --need ExtInd for all if any key relations are imported in their properties's modules
  local newImportedKeyRels::[QName] =
      filterMap(\ p::(QName, QName) ->
                  if !sameModule(p.1.moduleName, p.2) then just(p.2) else nothing(),
         zip(newThms.thmNames, newThms.keyRels));
  local oldImportedKeyRels::[QName] =
      if obligationFound
      then filterMap(\ p::(QName, QName) ->
                       if !sameModule(p.1.moduleName, p.2) then just(p.2) else nothing(),
              take(length(names), zip(thms.thmNames, thms.keyRels)))
      else [];
  local importedKeyRels::[QName] =
      oldImportedKeyRels ++ newImportedKeyRels;

  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else if !extIndGroup.isJust
      then [errorMsg("Did not find Ext_Ind required for induction " ++
                     "on relations " ++
                     implode(", ",
                        map(justShow, map((.pp), importedKeyRels))))]
      else let missing::[QName] =
               case extIndGroup of
               | just(eg) ->
                 removeAll(map(fst, eg), thms.keyRels)
               | nothing() -> error("toAbellaMsgs:  let missing")
               end
           in
             if null(missing)
             then []
             else [errorMsg("Ext_Ind group does not include " ++
                            "key relations " ++
                            implode(", ",
                               map(justShow, map((.pp), missing))))]
           end;
  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else if alsos.len > 0
      then [errorMsg("Cannot have also theorems when using Ext_Ind")]
      else [];
  --check we don't now require ExtInd when we didn't before
  top.toAbellaMsgs <-
      if !obligationFound || null(newImportedKeyRels)
      then [] --imported not known or no attempt to use ExtInd for new
      else if !null(oldImportedKeyRels)
      then [] --old already used ExtInd
      else [errorMsg("Cannot have new properties using imported " ++
               "key relations when existing properties do not")];
  --check for naming IH's the same thing
  top.toAbellaMsgs <-
      foldl(\ rest::([(String, String)], [Message])
              p::(String, String, String) ->
              case lookup(p.2, rest.1) of
              | just(thm) ->
                (rest.1, errorMsg("IH name " ++ p.2 ++
                            " already used by " ++ thm)::rest.2)
              | nothing() -> ((p.2, p.3)::rest.1, rest.2)
              end, ([], []), thms.renamedIHs ++ alsos.renamedIHs).2;

  --check for naming thms the same thing
  top.toAbellaMsgs <-
      map(\ q::QName ->
            errorMsg("Theorem " ++ justShow(q.pp) ++ " is declared " ++
                     "multiple times"),
                               --(seen,    multiple)
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else if contains(q, rest.2)
                  then (rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), thms.thmNames ++ alsos.thmNames).2);

  --check all use the same number of inductions
  top.toAbellaMsgs <-
      case nub(thms.numsInductions ++ alsos.numsInductions) of
      | [_] -> [] --all are the same
      | _ -> --must have been at least one number, so this is at least
             --   two different numbers of inductions
        [errorMsg("Not all mutual theorems declare the same number" ++
                  " of inductions")]
      end;

  local obligationFound::Boolean =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(thms, _, _) ->
        setEq(names, map(fst, thms))
      | _ -> false
      end;
  local obligations::[(QName, Bindings, ExtBody, InductionOns)] =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(x, _, _) -> x
      | _ -> error("Not possible (proveObligations.obligations)")
      end;
  local alsosInfo::[(QName, Bindings, ExtBody, InductionOns)] =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(_, x, _) -> x
      | _ -> error("Not possible (proveObligations.alsosInfo)")
      end;

  local thms::ExtThms =
      if obligationFound
      then foldr(\ p::(QName, Bindings, ExtBody, InductionOns) rest::ExtThms ->
                   addExtThms(p.1, p.2, p.3, p.4, rest),
                 ^newThms, obligations)
      else endExtThms(); --should not access, but may
  thms.startingGoalNum =
       if null(neededExtIndChecks)
       then if thms.len + alsos.len > 1
            then [1]
            else [] --only one thm, so subgoals for it are 1, 2, ...
       else if thms.len + alsos.len > 1
            --same, but under subgoal after ExtInd validity check
            then [length(neededExtIndChecks) + 1, 1]
            else [length(neededExtIndChecks) + 1];
  thms.typeEnv = top.typeEnv;
  thms.relationEnv = top.relationEnv;
  thms.constructorEnv = top.constructorEnv;
  thms.currentModule = top.currentModule;
  thms.useExtInd = if null(importedKeyRels) || !extIndGroup.isJust
                   then []
                   else case extIndGroup of
                        | just(eg) -> eg
                        | nothing() -> error("thms.useExtInd")
                        end;
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  thms.expectedIHNum = 0;
  thms.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  thms.numMutualThms = thms.len + alsos.len;
  local alsos::ExtThms =
      if obligationFound
      then foldr(\ p::(QName, Bindings, ExtBody, InductionOns) rest::ExtThms ->
                   addExtThms(p.1, p.2, p.3, p.4, rest),
                 ^newAlsos, alsosInfo)
      else endExtThms(); --should not access, but may
  alsos.startingGoalNum = thms.nextGoalNum;
  alsos.typeEnv = top.typeEnv;
  alsos.relationEnv = top.relationEnv;
  alsos.constructorEnv = top.constructorEnv;
  alsos.currentModule = top.currentModule;
  alsos.useExtInd = []; --don't need it for alsos
  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];
  alsos.expectedIHNum = thms.len; --because they start with 0
  alsos.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  alsos.numMutualThms = thms.len + alsos.len;

  --need to decorate newThms, newAlsos as well because we use them for errs
  newThms.useExtInd = if null(importedKeyRels) || !extIndGroup.isJust
                      then []
                      else case extIndGroup of
                           | just(eg) -> eg
                           | nothing() -> error("thms.useExtInd")
                           end;
  newThms.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  newThms.shouldBeExtensible = true;
  --
  newAlsos.useExtInd = [];
  newAlsos.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  newAlsos.shouldBeExtensible = false;

  production extName::QName =
      if thms.len + alsos.len > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(names);

  --imported thms used ExtInd already
  local importedUsedExtInd::Boolean = !null(oldImportedKeyRels);
  local neededExtIndChecks::[(Metaterm, [ProofCommand])] =
      if importedUsedExtInd
      then newThms.extIndChecks --old already done, so only new
      else thms.extIndChecks; --nothing done, so use them all

  local extIndCheck::Metaterm =
      foldr1(andMetaterm,
         map(fst, neededExtIndChecks) ++
         [bindingMetaterm(existsBinder(),
             oneBinding("$", justType(integerType)),
             ^fullThms)]);
  --during commands for extIndCheck, including declaration of ExtThm
  local extIndCheckCmds::[(SubgoalNum, [ProofCommand])] =
      --intros for each check
      map(\ p::(Integer, Metaterm, [ProofCommand]) -> ([p.1], p.3),
          enumerateFrom(1, neededExtIndChecks)) ++
      --exists to remove binding from front, then set-up for ExtThm
      [([length(neededExtIndChecks) + 1],
        existsTactic(oneEWitnesses(termEWitness(integerToIntegerTerm(0))))::
        map(\ a::AnyCommand -> case a of
                               | anyProofCommand(p) -> ^p
                               | _ -> error("only proof commands")
                               end, tail(extThmCmds)))];
  local extIndCheckStart::[AnyCommand] =
      --declare checks
      [anyTopCommand(
          theoremDeclaration(toQName("$ExtIndCheck_" ++ toString(genInt())),
             [], ^extIndCheck)),
      --split (must split because at least 1 + true)
       anyProofCommand(splitTactic())] ++
      --intros/set-up for first one
      map(anyProofCommand, head(extIndCheckCmds).2);

  local extThmCmds::[AnyCommand] =
      --declare theorems
      [anyTopCommand(theoremDeclaration(^extName, [], ^fullThms))] ++
      --declare inductions
      map(\ l::[Integer] ->
            anyProofCommand(inductionTactic(noHint(), l)),
          transpose(thms.inductionNums ++ alsos.inductionNums)) ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          thms.renamedIHs ++ alsos.renamedIHs) ++
      --split
      (if thms.len + alsos.len > 1
       then [anyProofCommand(splitTactic())]
       else []) ++
      --initial set of during commands, which is at least intros, but
      --   probably also some skips here
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm
  local fullThms::Metaterm =
      if alsos.len > 0
      then andMetaterm(thms.toAbella, alsos.toAbella)
      else thms.toAbella;

  top.toAbella =
      if null(neededExtIndChecks)
      then extThmCmds
      else extIndCheckStart;

  top.provingTheorems = thms.provingTheorems ++ alsos.provingTheorems;

  top.duringCommands =
      if null(neededExtIndChecks)
      then tail(thms.duringCommands)
      else tail(extIndCheckCmds) ++ tail(thms.duringCommands);
  top.afterCommands =
      if thms.len + alsos.len > 1
      then [anyTopCommand(splitTheorem(^extName,
                             map(fst, top.provingTheorems)))]
      else []; --nothing to split, so nothing to do

  --don't need alsos because we aren't proving them
  top.keyRelModules = thms.keyRelModules;

  top.is_nonextensible = false;
}


--matrix transpose to turn rows into columns
--used for re-grouping induction nums from per-thm to per-induction
function transpose
[[a]] ::= l::[[a]]
{
  local firstNewRow::[a] = map(head, l);
  local newRest::[[a]] = transpose(map(tail, l));
  return case l of
         | [] -> [] --shouldn't see this, really
         | []::_ -> [] --assume all empty
         | _ -> firstNewRow::newRest
         end;
}





nonterminal ExtThms with
   pps, abella_pp, len,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   inductionNums, keyRels, specialKeyRels,
   useExtInd, shouldBeExtensible,
   expectedIHNum, renamedIHs, specialIHNames, thmNames,
   startingGoalNum, nextGoalNum, followingCommands, duringCommands,
   numMutualThms,
   numsInductions,
   keyRelModules, extIndChecks,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs, useExtInd, shouldBeExtensible,
          followingCommands, specialIHNames, numMutualThms on ExtThms;

--prefix for the subgoals arising from a theorem
inherited attribute startingGoalNum::SubgoalNum;
--next one afterward
synthesized attribute nextGoalNum::SubgoalNum;
--gather indices for induction, grouped by thm
--e.g. [[1, 3], [2, 1]] -> induction on 1 2. induction on 3 1.
synthesized attribute inductionNums::[[Integer]];
--Key relations for all thms
synthesized attribute keyRels::[QName];
--Ext_Ind definition to use if needed
inherited attribute useExtInd::[(QName, [String], Bindings,
                                 ExtIndPremiseList)];
--commands following this set of ExtThms
inherited attribute followingCommands::[(SubgoalNum, [ProofCommand])];
--whether the theorem is expected to be extensible
inherited attribute shouldBeExtensible::Boolean;
--the number the IH should be (0 for "IH")
inherited attribute expectedIHNum::Integer;
--new names for IH for various theorems (old name, new name, thm name)
synthesized attribute renamedIHs::[(String, String, String)];
--special names for IH to check they don't interfere with labels
inherited attribute specialIHNames::[(String, String, String)];
--thm names used
synthesized attribute thmNames::[QName];
--statements and initial commands for showing ExtInd use is valid
synthesized attribute extIndChecks::[(Metaterm, [ProofCommand])];
--total number of thms being proved together
inherited attribute numMutualThms::Integer;
--numbers of inductions for each thm
synthesized attribute numsInductions::[Integer];
--key relations that are R_ES or R_P
synthesized attribute specialKeyRels::[Boolean];

abstract production endExtThms
top::ExtThms ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.len = 0;

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];

  top.inductionNums = [];
  top.keyRels = [];

  top.specialKeyRels = [];

  top.duringCommands = top.followingCommands;

  top.extIndChecks = [];

  top.keyRelModules = [];

  top.renamedIHs = [];

  top.nextGoalNum = top.startingGoalNum;

  top.thmNames = [];

  top.numsInductions = [];
}


abstract production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 ons::InductionOns rest::ExtThms
{
  top.pps = (name.pp ++ text(" : forall ") ++
             ppImplode(text(" "), bindings.pps) ++ text(",") ++
             nest(3, realLine() ++ body.pp) ++ realLine() ++
             text("on ") ++ ons.pp)::rest.pps;
  top.abella_pp =
      name.abella_pp ++ " : forall " ++ bindings.abella_pp ++ ", " ++
      body.abella_pp ++ " on " ++ ons.abella_pp ++
      if rest.abella_pp == "" then "" else ", " ++ rest.abella_pp;

  top.len = 1 + rest.len;

  production fullName::QName =
      if name.isQualified
      then ^name
      else addQNameBase(top.currentModule, name.shortName);

  top.toAbella =
      case rest of
      | endExtThms() ->
        bindingMetaterm(forallBinder(), bindings.toAbella, body.toAbella)
      | _ ->
        andMetaterm(
           bindingMetaterm(forallBinder(), bindings.toAbella, body.toAbella),
           rest.toAbella)
      end;

  body.boundNames = bindings.usedNames;

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
      generateExtIntrosNames(labels, body.premises);

  top.inductionNums = ons.premiseNums::rest.inductionNums;
  top.keyRels =
      if keyRelFound
      then keyRel.name::rest.keyRels
      else rest.keyRels;
  top.numsInductions = ons.len::rest.numsInductions;

  top.specialKeyRels =
      case foundKeyRelPremise of
      | just(extSizeMetaterm(_, _, _)) -> true
      | just(projRelMetaterm(_, _, _)) -> true
      | _ -> false
      end::rest.specialKeyRels;

  ons.thmPremises = body.premises;
  ons.thmName = ^name;

  --the premise we declared for the key relation
  local keyRelPremiseName::String =
      case ons.keyRelLabelCandidates of
      | lbl::_ -> lbl
      | [] when ons.len == 1 -> head(ons.toList).1
      | [] -> "" --won't actually use; just a crash-safe filler
      end;
  local foundKeyRelPremise::Maybe<Metaterm> =
      case ons.keyRelLabelCandidates of
      | [lbl] ->
        lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                   a.isJust && b.isJust && a.fromJust == b.fromJust,
                 just(lbl), body.premises)
      | [] when ons.len == 1 -> --first one
        lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                   a.isJust && b.isJust && a.fromJust == b.fromJust,
                 just(head(ons.toList).1), body.premises)
      | _ -> nothing()
      end;
  --errors around key relation
  top.toAbellaMsgs <-
      case foundKeyRelPremise of
      | _ when !top.shouldBeExtensible ->
        [] --only check for key rel errors for extensible thms
      | nothing() ->
        --check why it wasn't found
        case ons.keyRelLabelCandidates of
        | [] when ons.len != 1 -> --none chosen, multiple inductions
          [errorMsg("No key relation indicated for extensible " ++
                    "theorem " ++ justShow(name.pp))]
        | _::_::_ ->
          [errorMsg("Multiple key relations indicated for " ++
                    "extensible theorem " ++ justShow(name.pp))]
        | _ -> [] --premise not known; error generated by ons
        end
      | just(relationMetaterm(rel, args, r)) ->
        --need to check the metaterm is built by an extensible relation
        let decRel::Decorated QName with {relationEnv} =
            decorate ^rel with {relationEnv = top.relationEnv;}
        in
          if !decRel.relFound
          then [] --covered by other errors
          else if !keyRel.isExtensible
               then [errorMsg("Key relation for extensible theorem " ++
                        justShow(name.pp) ++ " must be extensible; " ++
                        justShow(keyRel.name.pp) ++ " is not")]
               else case head(drop(keyRel.pcIndex, args.toList)) of
                    | nameTerm(q, _) when !q.isQualified -> [] --var
                    | _ -> --anything else is structured
                      [errorMsg("Primary component of key " ++
                          "relation cannot be structured but is " ++
                          "in theorem " ++ justShow(name.pp))]
                      --ban structured PC for key rel because it can't
                      --   actually be extended, so it can be a
                      --   non-extensible theorem
                    end ++
                    --check for ExtInd
                    if sameModule(top.currentModule, keyRel.name)
                    then [] --don't need one
                    else case thisExtInd of
                         | just(_) -> [] --found
                         | nothing() ->
                           [errorMsg("Cannot find ExtInd for relation " ++
                               justShow(keyRel.name.pp) ++
                               " for extensible theorem " ++ justShow(name.pp))]
                         end
        end
      | just(extSizeMetaterm(rel, args, r)) ->
        let decRel::Decorated QName with {relationEnv} =
            decorate ^rel with {relationEnv = top.relationEnv;}
        in
          if !decRel.relFound
          then [] --covered by other errors
          else case head(drop(keyRel.pcIndex, args.toList)) of
               | nameTerm(q, _) when !q.isQualified -> [] --var
               | _ -> --anything else is structured
                 [errorMsg("Primary component of key " ++
                     "relation cannot be structured but is in " ++
                     "theorem " ++ justShow(name.pp))]
                 --ban structured PC for key rel because it can't
                 --   actually be extended, so it can be a
                 --   non-extensible theorem
               end ++
               --check for same module; cannot have ExtInd for ExtSize
               (if sameModule(top.currentModule, decRel.fullRel.name)
                then []
                else [errorMsg("Cannot have <" ++
                         justShow(decRel.fullRel.name.pp) ++
                         " {ES}> as key relation outside of " ++
                         "module introducing it")]) ++
               --check for number being a variable
               case last(args.toList) of
               | nameTerm(q, _) when !q.isQualified -> [] --var
               | _ -> --anything else is structured
                 [errorMsg("Cannot have <" ++
                     justShow(decRel.fullRel.name.pp) ++ " {ES}> " ++
                     "as key relation when size is not a variable")]
                 --because we are checking applicability of rules for the
                 --   underlying relation that doesn't know the size, not
                 --   the actual relation (so we don't know the subgoals
                 --   where we need skips); otherwise it would be fine
                 --I can't imagine any reason to have a specific number
                 --   other than maybe 0 (only host rules)
               end
        end
      | just(projRelMetaterm(rel, args, r)) ->
        let decRel::Decorated QName with {relationEnv} =
            decorate ^rel with {relationEnv = top.relationEnv;}
        in
          if !decRel.relFound
          then [] --covered by other errors
          else case head(drop(keyRel.pcIndex, args.toList)) of
               | nameTerm(q, _) when !q.isQualified -> [] --var
               | _ -> --anything else is structured
                 [errorMsg("Primary component of key " ++
                     "relation cannot be structured but is in " ++
                     "theorem " ++ justShow(name.pp))]
                 --ban structured PC for key rel because it can't
                 --   actually be extended, so it can be a
                 --   non-extensible theorem
               end ++
               --check for same module; cannot have ExtInd for ProjRel
               (if sameModule(top.currentModule, decRel.fullRel.name)
                then []
                else [errorMsg("Cannot have <" ++
                         justShow(decRel.fullRel.name.pp) ++
                         " {P}> as key relation outside of " ++
                         "module introducing it")])
        end
      | just(m) ->
        [errorMsg("Can only induct on extensible relations for " ++
            "extensible theorem " ++ justShow(name.pp) ++
            ", not " ++ justShow(m.pp))]
      end;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared theorem name " ++ justShow(name.pp) ++
                    " does not have correct module (expected " ++
                    justShow(top.currentModule.pp) ++ ")")]
      else [];
  --check there are no existing theorems with this full name
  top.toAbellaMsgs <-
      if null(findTheorem(^fullName, top.proverState))
      then []
      else [errorMsg("Theorem named " ++ justShow(fullName.pp) ++
                     " already exists")];

  --check the body is well-typed
  top.toAbellaMsgs <-
      case body.upSubst of
      | right(_) ->
        if any(map(\ v::String ->
                     substituteTy(varType(v), body.upSubst).containsVars,
                     allTyVars))
        then [errorMsg("Cannot determine types of all bound " ++
                       "variables in " ++ justShow(name.pp))]
        else []
      | left(errs) ->
        map(add_message_tag(_, "Type error in " ++ justShow(name.pp)), errs)
      end;
  --all type variables in the body
  local allTyVars::[String] =
      body.tyVars ++
      flatMap(\ p::(String, Either<Type String>) ->
                case p.2 of
                | left(_) -> []
                | right(s) -> [s]
                end,
              boundVarTys);
  --save the names for var types here
  local boundVarTys::[(String, Either<Type String>)] =
      map(\ p::(String, MaybeType) ->
            (p.1, case p.2 of
                  | justType(t) -> left(^t)
                  | nothingType() ->
                    right("__Bound" ++ toString(genInt()))
                  end),
          bindings.toList);
  body.downVarTys =
      map(\ p::(String, Either<Type String>) ->
            (p.1, case p.2 of
                  | left(t) -> t
                  | right(s) -> varType(s)
                  end),
          boundVarTys);
  body.downSubst = emptySubst();

  top.provingTheorems =
      (^fullName, if bindings.len > 0
                 then bindingMetaterm(forallBinder(),
                         bindings.toAbella, body.thm)
                 else body.thm)::rest.provingTheorems;

  rest.startingGoalNum =
       init(top.startingGoalNum) ++ [last(top.startingGoalNum) + 1];

  local keyRelFound::Boolean =
      case foundKeyRelPremise of
      | just(relationMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.relFound
      | just(extSizeMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.relFound
      | just(projRelMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.relFound
      | _ -> false
      end;
  local keyRel::RelationEnvItem =
      case foundKeyRelPremise of
      | just(relationMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.fullRel
      | just(extSizeMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.fullRel
      | just(projRelMetaterm(rel, _, _)) ->
        decorate ^rel with {relationEnv = top.relationEnv;}.fullRel
      | _ -> error("Should not access keyRel")
      end;
  local usesProjRel::Boolean =
      case foundKeyRelPremise of
      | just(projRelMetaterm(_, _, _)) -> true
      | _ -> false
      end;

  local thisExtInd::Maybe<(QName, [String], Bindings, ExtIndPremiseList)> =
      if keyRelFound --guard against out-of-order access
      then case lookup(keyRel.name, top.useExtInd) of
           | just(p) -> just((keyRel.name, p))
           | nothing() -> nothing()
           end
      else nothing();
  --
  local relArgs::[Term] =
      case foundKeyRelPremise of
      --take full of these to turn constructor names into constructor
      --   terms, not vars that will unify with anything
      | just(relationMetaterm(_, a, _)) ->
        decorate ^a with {
          typeEnv = top.typeEnv;
          relationEnv = top.relationEnv;
          constructorEnv = top.constructorEnv;
          boundNames = bindings.usedNames;
        }.full.toList
      | just(extSizeMetaterm(_, a, _)) ->
        init(decorate ^a with {
               typeEnv = top.typeEnv;
               relationEnv = top.relationEnv;
               constructorEnv = top.constructorEnv;
               boundNames = bindings.usedNames;
             }.full.toList) --drop num
      | just(projRelMetaterm(_, a, _)) ->
        decorate ^a with {
          typeEnv = top.typeEnv;
          relationEnv = top.relationEnv;
          constructorEnv = top.constructorEnv;
          boundNames = bindings.usedNames;
        }.full.toList
      | _ -> [] --should not need in this case
      end;


  --for the subgoals that should arise, the last digit of the subgoal
  --number, whether we need to prove it, name to clear for unknownTermK
  --for DefR preventer ("" if nothing to clear)
  local expectedSubgoals::[(Integer, Boolean, String)] =
      if !keyRelFound then [] --guard against out-of-order access
      else
      foldl(
         \ thusFar::(Integer, [(Integer, Boolean, String)])
           now::([Term], Maybe<Metaterm>) ->
           let pc::Decorated Term with {relationEnv, constructorEnv,
                                        typeEnv} =
               decorate rulePrimaryComponent(now, keyRel) with {
                  relationEnv = top.relationEnv;
                  constructorEnv = top.constructorEnv;
                  typeEnv = top.typeEnv;
               }
           in
           let pcMod::QName =
               if pc.isStructured
               then pc.headConstructor.moduleName
               else keyRel.name.moduleName
           in
           let pcThisK::Boolean =
               pc.isUnknownTermK &&          --unknownTermK
               case pc.unknownId of
               | just(i) -> i == keyRel.name --for this rel
               | nothing() -> error("pcThisK")
               end
           in
           let premBaseName::String = dropNums(keyRelPremiseName)
           in
           let prems::[Metaterm] = splitRulePrems(now.2)
           in
           let falsePremName::String =
               head(foldr(\ m::Metaterm rest::[String] ->
                            case m of
                            | eqMetaterm(_, _) -> rest
                            | _ -> freshName(premBaseName, rest)::rest
                            end,
                          catMaybes(map(fst, body.premises)),
                          prems))
           in
           --freshen rule to check if it unifies
           let existingVars::[String] =
               nub(flatMap((.usedNames), now.1) ++
                   flatMap((.usedNames), prems))
           in
           let freshVars::[String] =
               foldr(\ x::String rest::[String] ->
                       freshName(x, rest ++ bindings.usedNames)::rest,
                     [], existingVars)
           in
           let newTerms::[Term] =
               map(\ x::String -> nameTerm(toQName(x), nothingType()),
                   freshVars)
           in
           let premUnifyPairs::([Term], [Term]) =
               premiseUnificationPairs(
                  safeReplace(prems, existingVars, newTerms))
           in
           let unifySides::([Term], [Term]) =
               (premUnifyPairs.1 ++ safeReplace(now.1, existingVars, newTerms),
                premUnifyPairs.2 ++ relArgs)
           in
           let unifies::Boolean =
               unifyTermsSuccess(unifySides.1, unifySides.2) &&
               --R_P doesn't have any generic rules, so rule doesn't
               --   actually exist
               !(usesProjRel &&
                 (pc.isUnknownTermK || pc.isUnknownTermI))
           in
           let needToProve::Boolean =
               (fullName.moduleName == top.currentModule || --new thm
                pcMod == top.currentModule) && --new constr
               (!pc.isUnknownTermK || --not unknownTermK
                case pc.unknownId of
                | just(i) -> i == --for this relation
                             keyRel.name
                | nothing() -> error("needToProve")
                end)
           in
             if unifies --rule applies
             then (thusFar.1 + 1,
                   thusFar.2 ++ [(thusFar.1, needToProve,
                                  if pcThisK then falsePremName else "")])
             else thusFar --doesn't apply:  just continue with next
           end end end end end end end end end end end end end,
         (1, []), keyRel.defsList).2;
  --group consecutive skips; leave non-skips alone
  local groupedExpectedSubgoals::[[(Integer, Boolean, String)]] =
      foldr(\ p::(Integer, Boolean, String)
              rest::[[(Integer, Boolean, String)]] ->
              if p.2 || null(rest) || head(head(rest)).2
              then [p]::rest
              else (p::head(rest))::tail(rest), [], expectedSubgoals);
  --last digit of subgoal and skips needed
  local subgoalDurings::[(Integer, [ProofCommand])] =
      flatMap(\ l::[(Integer, Boolean, String)] ->
                if !null(l) && !head(l).2 --things we don't do we skip
                then [(head(l).1,
                       map(\ x::(Integer, Boolean, String) ->
                             skipTactic(), l))]
                else if !null(l) && head(l).3 != ""
                then [(head(l).1, [clearCommand([head(l).3], false)])]
                else [], --nothing for things we need to prove other than K
              groupedExpectedSubgoals);
  --turned into full subgoals
  local subgoalDuringCommands::[(SubgoalNum, [ProofCommand])] =
      map(\ p::(Integer, [ProofCommand]) ->
            (top.startingGoalNum ++ [p.1], p.2),
          subgoalDurings);
  {-
    The first thing in ExtThm.duringCommands is always for the first
    subgoal for the goal because we need intros.  If we skip the last
    subgoal here, we need to add the starting commands from the next
    to the last group of commands here.
  -}
  local combinedCommands::[(SubgoalNum, [ProofCommand])] =
      if top.shouldBeExtensible
      then if !null(expectedSubgoals) && !last(expectedSubgoals).2 &&
              !null(rest.duringCommands) && !null(subgoalDuringCommands)
           then let lastSubgoal::(SubgoalNum, [ProofCommand]) =
                    last(subgoalDuringCommands)
                in
                  init(subgoalDuringCommands) ++
                  [(lastSubgoal.1,
                    lastSubgoal.2 ++ head(rest.duringCommands).2)] ++
                  tail(rest.duringCommands)
                end
           else subgoalDuringCommands ++ rest.duringCommands
      else rest.duringCommands;
  top.duringCommands =
      if top.shouldBeExtensible
      then extensibleDuringCommands
      else alsoDuringCommands;
  --during commands for an extensible theorem, where we do case and
  --   may not have any subgoals after that
  local extensibleDuringCommands::[(SubgoalNum, [ProofCommand])] =
      --intros and case immediately
      [(top.startingGoalNum,
        [introsTactic(introsNames),
         caseTactic(nameHint(keyRelPremiseName), keyRelPremiseName,
                    true)] ++
         --add first group of skips if they happen right away
         (if !null(combinedCommands) && !null(subgoalDurings) &&
             head(subgoalDurings).1 == 1
          then head(combinedCommands).2
          else []))] ++
      if !null(combinedCommands) && !null(subgoalDurings) &&
          head(subgoalDurings).1 == 1
      then tail(combinedCommands)
      else combinedCommands;
  --during commands for a non-extensible theorem, where we do not do
  --   case automatically and thus must have a subgoal to solve
  local alsoDuringCommands::[(SubgoalNum, [ProofCommand])] =
      if fullName.moduleName == top.currentModule
         --new theorem:  solve, intros immediately
      then [(top.startingGoalNum, [introsTactic(introsNames)])] ++
           combinedCommands
         --imported theorem:  skip it
      else if !null(combinedCommands)
           then (top.startingGoalNum,
                 skipTactic()::head(combinedCommands).2)::tail(combinedCommands)
           else [(top.startingGoalNum, [skipTactic()])];

  {-Build the metaterm for checking the ExtInd use is valid-}
  --full metaterm to prove to show this use of ExtInd is valid
  local extIndUseCheck::Metaterm =
      case thisExtInd of
      | just((_, args, binds, prems)) ->
        generateExtIndCheck(args, binds, prems,
                            relArgs, ^bindings, body)
      | nothing() -> error("extIndUseCheck")
      end;
  --
  top.extIndChecks =
      if !null(top.useExtInd) && --sameModule(top.currentModule, keyRel.name) &&
         --if premises are empty, nothing to show
         thisExtInd.isJust && thisExtInd.fromJust.4.len != 0
      then (^extIndUseCheck, [introsTactic(introsNames)])::rest.extIndChecks
      else rest.extIndChecks;

  top.keyRelModules =
      (top.startingGoalNum, keyRel.name.moduleName)::rest.keyRelModules;

  ons.expectedIHNum = top.expectedIHNum;
  top.renamedIHs = ons.renamedIHs ++ rest.renamedIHs;

  --next number
  rest.expectedIHNum = top.expectedIHNum + 1;

  --pass it up
  top.nextGoalNum = rest.nextGoalNum;
  top.thmNames = ^fullName::rest.thmNames;
}

--generate names for intros
--must be determined entirely by arguments (no using genInt())
function generateExtIntrosNames
[String] ::= knownLabels::[String]
             premiseInfo::[(Maybe<String>, Metaterm)]
{
  return
      foldl(\ rest::[String] p::(Maybe<String>, Metaterm) ->
              case p.1 of
              | just(x) -> rest ++ [x]
              | nothing() -> rest ++
                --using "H" as base triggers an Abella error
                [freshName("Hyp", rest ++ knownLabels)]
              end,
            [], premiseInfo);
}

--build the theorem statement for checking ExtInd use is valid
function generateExtIndCheck
Metaterm ::= extIndArgs::[String] extIndBinds::Bindings
             extIndPrems::ExtIndPremiseList
             thmRelArgs::[Term] thmBindings::Bindings
             thmBody::Decorated ExtBody with {boundNames,
                         relationEnv, constructorEnv, typeEnv}
{
  --names left in ExtInd bindings after removing arguments to R
  local extIndRemainingNames::[String] =
      removeAll(extIndArgs, extIndBinds.usedNames);
  --fresh names for those to avoid capture with args for relation here
  local extIndUseCheckBinds::[String] =
      let alreadyUsed::[String] = flatMap((.usedNames), thmRelArgs)
      in
        foldl(\ rest::[String] x::String ->
                if contains(x, rest ++ alreadyUsed)
                then freshName(x, rest ++ alreadyUsed)::rest
                else x::rest,
              [], extIndRemainingNames)
      end;
  --things to go in the conclusion
  local extIndUseCheckConcs::[Metaterm] =
      safeReplace(map(snd, extIndPrems.toList),
         extIndArgs ++ extIndRemainingNames,
         thmRelArgs ++ map(\ x::String ->
                             nameTerm(toQName(x), nothingType()),
                           extIndUseCheckBinds));
  --full metaterm to prove to show this use of ExtInd is valid
  local extIndUseCheck::Metaterm =
      bindingMetaterm(forallBinder(), @thmBindings,
         foldr1(impliesMetaterm,
            metatermPremises(thmBody.toAbella) ++
            [if null(extIndUseCheckBinds)
             then foldr1(andMetaterm, extIndUseCheckConcs)
             else bindingMetaterm(existsBinder(), ^thmBindings,
                     foldr1(andMetaterm, extIndUseCheckConcs))]));
  return ^extIndUseCheck;
}





nonterminal InductionOns with
   pp, abella_pp,
   len, toList<(String, Boolean, Maybe<String>)>,
   toAbellaMsgs,
   keyRelLabelCandidates,
   premiseNums,
   expectedIHNum, numMutualThms, renamedIHs,
   thmPremises, thmName;
propagate toAbellaMsgs, thmPremises, thmName, numMutualThms
   on InductionOns;

--things claiming to be the key relation label
synthesized attribute keyRelLabelCandidates::[String];
--1-indexed premise numbers for induction
synthesized attribute premiseNums::[Integer];

inherited attribute thmPremises::[(Maybe<String>, Metaterm)];
inherited attribute thmName::QName;

abstract production endInductionOns
top::InductionOns ::=
{
  top.pp = text("");
  top.abella_pp = "";

  top.len = 0;
  top.toList = [];

  top.keyRelLabelCandidates = [];

  top.premiseNums = [];

  top.renamedIHs = [];
}


abstract production addInductionOns
top::InductionOns ::=
        label::String isKeyRel::Boolean asName::Maybe<String>
        rest::InductionOns
{
  top.pp =
      text(label) ++ (if isKeyRel then text(" *") else text("")) ++
      (case asName of
       | nothing() -> text("")
       | just(ih) -> text(" as " ++ ih)
       end) ++
      (if rest.len == 0 then text("") else text(", ") ++ rest.pp);
  top.abella_pp =
      label ++ (if isKeyRel then " *" else "") ++
      (case asName of
       | nothing() -> ""
       | just(ih) -> " as " ++ ih
       end) ++
      (if rest.len == 0 then "" else ", " ++ rest.abella_pp);

  top.len = 1 + rest.len;
  top.toList = (label, isKeyRel, asName)::rest.toList;

  top.keyRelLabelCandidates =
      if isKeyRel
      then label::rest.keyRelLabelCandidates
      else rest.keyRelLabelCandidates;

  --only correct if label exists, but it had better if we access this
  top.premiseNums =  --(index,   already found)
      foldl(\ thusFar::(Integer, Boolean)
              here::(Maybe<String>, Metaterm) ->
              if thusFar.2
              then thusFar
              else case here.1 of
                   | just(x) when x == label -> (thusFar.1, true)
                   | _ -> (thusFar.1 + 1, false)
                   end,
            (1, false), top.thmPremises).1::rest.premiseNums;

  top.renamedIHs =
      case asName of
      | nothing() -> []
      | just(n) ->
        [(numToIHName(top.expectedIHNum), n, top.thmName.shortName)]
      end ++ rest.renamedIHs;
  rest.expectedIHNum = top.expectedIHNum + top.numMutualThms;

  --can't name IH to something that might be an Abella-generated IH name
  top.toAbellaMsgs <-
      case asName of
      | just(n) when matches_IH_form(n) ->
        [errorMsg("Cannot have IH name in as clause of form \"IH<num>\"")]
      | _ -> []
      end;
  --check label is declared as a premise
  top.toAbellaMsgs <-
      if contains(label, filterMap(\ a -> a, map(fst, top.thmPremises)))
      then []
      else [errorMsg("Unknown label " ++ label ++ " for theorem " ++
                     top.thmName.shortName)];
}

--Turn an IH index into the name Abella will give it
function numToIHName
String ::= n::Integer
{
  return if n == 0 then "IH" else "IH" ++ toString(n);
}





nonterminal ExtBody with
   pp, abella_pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises, thm,
   boundNames, usedNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState,
   upSubst, downSubst, downVarTys, tyVars,
   specialIHNames;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs,
          downVarTys, tyVars, usedNames, specialIHNames on ExtBody;

--premises should have full version of premise
synthesized attribute premises::[(Maybe<String>, Metaterm)];
--Metaterm underlying the body
synthesized attribute thm::Metaterm;

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;
  top.abella_pp = conc.abella_pp;

  top.thm = ^conc;

  top.toAbella = conc.toAbella;

  conc.boundNames = top.boundNames;

  --take everything from before the final implication
  top.premises =
      map(\ a -> (nothing(), a),
         take(length(conc.splitImplies) - 1, conc.splitImplies));

  conc.downSubst = top.downSubst;
  top.upSubst = conc.upSubst;
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = text(label ++ " : ") ++
           (if m.isAtomic then m.pp else parens(m.pp))++
           text(" ->") ++ realLine() ++ rest.pp;
  top.abella_pp =
      label ++ " : (" ++ m.abella_pp ++ ") -> " ++ rest.abella_pp;

  top.thm = impliesMetaterm(^m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (just(label), ^m)::rest.premises;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  --labels of the form H<num> cause Abella errors
  top.toAbellaMsgs <-
      if startsWith("H", label) &&
         isDigit(substring(1, length(label), label))
      then [errorMsg("Cannot declare label of form \"H<num>\"")]
      else [];
  --labels of the form IH<num> may interfere with inductive hypotheses
  top.toAbellaMsgs <-
      if matches_IH_form(label)
      then [errorMsg("Cannot declare label of form \"IH<num>\"")]
      else [];
  --cannot have names of other IH's
  top.toAbellaMsgs <-
      let whichThm::Maybe<String> =
          lookup(label, map(snd, top.specialIHNames))
      in
        case whichThm of
        | nothing() -> []
        | just(thm) ->
          [errorMsg("Label " ++ label ++ " is the name of an IH " ++
                    "for " ++ thm ++ " and cannot be used as a " ++
                    "premise label")]
        end
      end;
}


abstract production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.pp = (if m.isAtomic then m.pp else parens(m.pp)) ++
           text(" ->") ++ realLine() ++ rest.pp;
  top.abella_pp =
      (if m.isAtomic then m.abella_pp else "(" ++ m.abella_pp ++ ")") ++
      " -> " ++ rest.abella_pp;

  top.thm = impliesMetaterm(^m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (nothing(), m.full)::rest.premises;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;
}




--check if it is IH[0-9]*
function matches_IH_form
Boolean ::= n::String
{
  return n == "IH" ||
         startsWith(n, "IH") && isDigit(substring(2, length(n), n));
}
