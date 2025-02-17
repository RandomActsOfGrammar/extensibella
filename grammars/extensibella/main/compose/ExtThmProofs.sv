grammar extensibella:main:compose;

function buildExtThmProofs
IOVal<[String]> ::=
   --[(thm name, key relation, property is host-y, property needed R_P,
   --  bindings, body, key relation intros name)]
   thmsInfo::[(QName, RelationEnvItem, Boolean, Boolean, Bindings,
               ExtBody, String)]
       --[(mod name, proof stuff grouped by all subgoals)]
   topGoalProofInfo::[(QName, [[(ProofState, [AnyCommand])]])]
   currentSubgoalNum::SubgoalNum groupUsesR_P::Boolean
   allThms::[(QName, Metaterm)] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   abella::ProcessHandle config::Configuration
   parsers::AllParsers keyRels::[QName]
   --[(module name, [properties in group known], count ExtInds proven)]
   moduleThmInfo::[(QName, [QName], Integer)]
   ioin::IOToken
{
  local fstThm::(QName, RelationEnvItem, Boolean, Boolean, Bindings,
                 ExtBody, String) = head(thmsInfo);
  local fstThmMod::QName = fstThm.1.moduleName;

  local intros_case::String =
      let prems::[(Maybe<String>, Metaterm)] =
        decorate fstThm.6 with {
           typeEnv = error("typeEnv not needed");
           relationEnv = error("relationEnv not needed");
           constructorEnv = error("constructorEnv not needed");
           boundNames = fstThm.5.usedNames;
        }.premises
      in
        "intros " ++
        implode(" ",
           generateExtIntrosNames(catMaybes(map(fst, prems)),
              prems)) ++ ". " ++
        fstThm.7 ++ ": case " ++ fstThm.7 ++ " (keep)."
      end;
  local intros_case_to_abella::IOVal<String> =
      sendBlockToAbella(intros_case, abella, ioin, config);

  --get commands/states for current property, update rest
  --([current property proofs], [remaining for later])
  local splitProofs::([(QName, [[[(ProofState, [AnyCommand])]]])],
                      [(QName, [[(ProofState, [AnyCommand])]])]) =
      foldr(\ here::(QName, [[(ProofState, [AnyCommand])]])
              rest::([(QName, [[[(ProofState, [AnyCommand])]]])],
                     [(QName, [[(ProofState, [AnyCommand])]])]) ->
                --([properties being proven], num ExtInd checks)
              let modInfo::([QName], Integer) =
                  case lookup(here.1, moduleThmInfo) of
                  | just(x) -> x
                  | nothing() ->
                    error("splitProofs.modInfo:  lookup(" ++ justShow(here.1.pp) ++
                          ", [" ++ implode(", ", map(justShow, map((.pp), map(fst,
                                                       moduleThmInfo)))) ++ "])")
                  end
              in
              let propNum::Integer = positionOf(fstThm.1, modInfo.1)
              in --basic subgoal number for property
              let basicSubgoal::SubgoalNum =
                  if length(modInfo.1) == 1
                  then [] --subgoals will be 1, 2, ...
                  else [propNum + 1] --subgoals will be x.1, x.2, ...
              in --sumboal number adjusted for ExtInd checks
              let subgoalNum::SubgoalNum =
                  if modInfo.2 > 0
                  then --nested under a new subgoal after ExtInd checks
                       (modInfo.2 + 1)::basicSubgoal
                  else basicSubgoal
              in
                if propNum < 0 --property not known in this module
                then (rest.1, here::rest.2)
                else case here.2 of
                     | ((s, _)::_)::_ when subgoalStartsWith(subgoalNum,
                                              s.currentSubgoal) ->
                       let sub::([[[(ProofState, [AnyCommand])]]],
                                 [[(ProofState, [AnyCommand])]]) =
                           getFullRootedBySubgoal(here.2, subgoalNum)
                       in
                          ((here.1, sub.1)::rest.1,
                           (here.1, sub.2)::rest.2)
                       end
                     | ((s, _)::_)::_ ->
                       (rest.1, here::rest.2)
                     | _ -> (rest.1, here::rest.2) --no proof here
                     end
              end end end end,
            ([], []), topGoalProofInfo);
  local firstPropProofs::[(QName, [[[(ProofState, [AnyCommand])]]])] =
      splitProofs.1;
  local remainingProofs::[(QName, [[(ProofState, [AnyCommand])]])] =
      splitProofs.2;

  --split into basic and generic cases
  local splitGeneric::([[[(ProofState, [AnyCommand])]]],
                       [[[(ProofState, [AnyCommand])]]]) =
      partition(\ l::[[(ProofState, [AnyCommand])]] ->
                  let p::ProofState = head(head(l)).1 in
                      !p.containsUnknownK && !p.containsUnknownI
                  end,
          case lookup(^fstThmMod, firstPropProofs) of
          | just(x) -> x
          | nothing() ->
            error("buildExtThmProofs.splitGeneric:  lookup(" ++
               justShow(fstThmMod.pp) ++ ", [" ++
               implode(", ", map(justShow, map((.pp), map(fst,
                                 firstPropProofs)))) ++ "])")
          end);
  --generic cases (i, k):  either (or both) may not exist
  local genericCases::(Maybe<[[(ProofState, [AnyCommand])]]>,
                       Maybe<[[(ProofState, [AnyCommand])]]>)=
      case splitGeneric.2 of
      | [] -> (nothing(), nothing())
      | [l] -> if head(head(l)).1.containsUnknownI
               then (just(l), nothing())
               else (nothing(), just(l))
      | [l1, l2] -> if head(head(l1)).1.containsUnknownI
                    then (just(l1), just(l2)) --l2 must be k
                    else (just(l2), just(l1))
      | _ -> error("Cannot have more than two generic cases")
      end;
  --known cases for all modules; drop generic from introducing module
  local knownCases::[[[(ProofState, [AnyCommand])]]] =
      flatMap(\ p::(QName, [[[(ProofState, [AnyCommand])]]]) ->
                if p.1 == ^fstThmMod
                then splitGeneric.1
                else p.2,
              firstPropProofs);
  --proof state after thm set-up
  local initProofState::ProofState =
      fullStateProcessing(intros_case_to_abella.iovalue, typeEnv,
         relEnv, constrEnv, parsers);
  --run through the case commands, building the proof
  local runProof::IOVal<([[String]], ProofState)> =
      buildExtThmProof(knownCases, genericCases.1, genericCases.2,
         currentSubgoalNum, abella, config, parsers, ^initProofState,
         allThms, keyRels, typeEnv, relEnv, constrEnv,
         intros_case_to_abella.io);
  --put the commands together into a single string
  local proofString::String =
      intros_case ++ "\n  " ++
      implode("\n  ",
          map(\ l::[String] -> implode(" ", l), runProof.iovalue.1));
  local rest::IOVal<[String]> =
      buildExtThmProofs(tail(thmsInfo), remainingProofs,
         incrementSubgoalNum(currentSubgoalNum), groupUsesR_P,
         allThms, typeEnv, relEnv, constrEnv, abella, config, parsers,
         keyRels, moduleThmInfo, runProof.io);


  return
      case thmsInfo of
      | [] -> ioval(ioin, [])
      | _::_ -> ioval(rest.io, proofString::rest.iovalue)
      end;
}


--get all the commands starting with a certain subgoal number, but
--   group them by subgoals under that
function takeAllRootedBySubgoal
([[String]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   root::SubgoalNum
{
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        let sub::([String], [[(ProofState, [AnyCommand])]]) =
            takeAllRooted(cmdStates, head(l).1.currentSubgoal)
        in
        let again::([[String]], [[(ProofState, [AnyCommand])]]) =
            takeAllRootedBySubgoal(sub.2, root)
        in
          (sub.1::again.1, again.2)
        end end
      | _ -> ([], cmdStates)
      end;
}


--get all the commands starting with a certain subgoal number, as well
--   as the remnant
--e.g. for numRoot = 1.1, gets commands for 1.1, 1.1.1, 1.1.3.1, but
--     not 1, 1.2, 3
function takeAllRooted
([String], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   numRoot::SubgoalNum
{
  local sub::([String], [[(ProofState, [AnyCommand])]]) =
      takeAllRooted(tail(cmdStates), numRoot);
  return
      case cmdStates of
      | x::rest when
        subgoalStartsWith(numRoot, head(x).1.currentSubgoal) ->
        (implode(" ", map((.abella_pp), flatMap(snd, x)))::sub.1,
         sub.2)
      | _ -> ([], cmdStates)
      end;
}


--get all the command states starting with a certain subgoal number,
--   but group them by subgoals under that
function getFullRootedBySubgoal
([[[(ProofState, [AnyCommand])]]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   root::SubgoalNum
{
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        let sub::([[(ProofState, [AnyCommand])]],
                  [[(ProofState, [AnyCommand])]]) =
            getFullRooted(cmdStates, head(l).1.currentSubgoal)
        in
        let again::([[[(ProofState, [AnyCommand])]]],
                    [[(ProofState, [AnyCommand])]]) =
            getFullRootedBySubgoal(sub.2, root)
        in
          (sub.1::again.1, again.2)
        end end
      | _ -> ([], cmdStates)
      end;
}


--get all the command states starting with a certain subgoal number,
--   and the remnant
function getFullRooted
([[(ProofState, [AnyCommand])]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]] root::SubgoalNum
{
  local sub::([[(ProofState, [AnyCommand])]],
              [[(ProofState, [AnyCommand])]]) =
      getFullRooted(tail(cmdStates), root);
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        (l::sub.1, sub.2)
      | _ -> ([], cmdStates)
      end;
}




function updateAssoc
Eq a => [(a, b)] ::= l::[(a, b)] key::a value::b
{
  return if head(l).1 == key then (key, value)::tail(l)
                             else updateAssoc(tail(l), key, value);
}



--while the Abella state is rooted in rootSubgoal, apply either the
--next known case or the preservability case
function buildExtThmProof
IOVal<([[String]], ProofState)> ::=
   knownCases::[[[(ProofState, [AnyCommand])]]]
   genericCaseI::Maybe<[[(ProofState, [AnyCommand])]]>
   genericCaseK::Maybe<[[(ProofState, [AnyCommand])]]>
   rootSubgoal::SubgoalNum abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  local origState::ProofState = head(head(head(knownCases))).1;
  origState.mapTo = ^incomingState;
  origState.typeEnv = typeEnv;
  origState.relationEnv = relEnv;
  origState.constructorEnv = constrEnv;

  local kState::ProofState = head(head(genericCaseK.fromJust)).1;
  kState.mapTo = ^incomingState;
  kState.typeEnv = typeEnv;
  kState.relationEnv = relEnv;
  kState.constructorEnv = constrEnv;

  local isKnown::Boolean = !null(knownCases) && origState.mapSuccess;
  local isK::Boolean = genericCaseK.isJust && kState.mapSuccess;
  --if not known or K, must be I

  --when the current composed case is one of the known cases
  local runKnown::IOVal<([String], ProofState)> =
      runKnownCase(head(knownCases), abella, config, parsers,
         ^incomingState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, ioin);

  --when the current composed case is one of the K unknown cases
  local runK::IOVal<([String], ProofState)> =
      runPreservabilityCase(genericCaseK.fromJust, abella, config,
         parsers, ^incomingState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, ioin);

  --when the current composed case is one of the I unknown cases
  --note genericCaseI must be just() if we ever access this
  local runI::IOVal<([String], ProofState)> =
  if !genericCaseI.isJust
  then error("Tried to run nothing I;\n" ++
          "Initial proof state:\n" ++ justShow(incomingState.pp) ++
          "\nOrig state:\n" ++ (if null(knownCases) then "<null>"
                                else justShow(origState.pp)) ++
          "\nK state:\n" ++ (if !genericCaseK.isJust then "<null>"
                             else justShow(kState.pp)))
  else
      runPreservabilityCase(genericCaseI.fromJust, abella, config,
         parsers, ^incomingState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, ioin);

  --select the correct run
  local run::IOVal<([String], ProofState)> =
      if isKnown then runKnown else if isK then runK else runI;
  local sub::IOVal<([[String]], ProofState)> =
      buildExtThmProof(
         if isKnown then tail(knownCases) else knownCases,
         genericCaseI, genericCaseK, rootSubgoal, abella, config,
         parsers, run.iovalue.2, allThms, keyRels, typeEnv, relEnv,
         constrEnv, run.io);

  return
      if !incomingState.inProof ||
         !subgoalStartsWith(rootSubgoal,
                            incomingState.currentSubgoal)
      then ioval(ioin, ([], ^incomingState))
      else {-
             Taking known proof cases whenever they fit guarantees we
             can build the proof.  All the host cases come first, and
             in the same order as in the modular proofs, so we clear
             them first.

             The remaining cases are those introduced by extensions.
             These must have a constructor for the primary component.
             Then the proof states for known extension cases can only
             unify with the composed proof states for the same cases;
             those for other extensions cannot unify because they have
             a different PC constructor.

             Thus taking a known case whenever it unifies guarantees
             we map each of the known proofs to the correct known
             case in the composed proof, and each known proof case is
             at the front of the list when it comes up.  Then if the
             head of the known cases does not unify, one of the
             generic cases must be applicable.

             We try the K case first because its applicability is a
             bit more general than the I case, as only relations
             introduced by the module introducing the property can be
             analyzed for <unknown K>.  Thus if both the I and K cases
             appear applicable by mapping, the K case is guaranteed to
             be applicable, whereas the I case might contain a case
             analysis that wouldn't be fine in cases corresponding to
             K directly.

             An alternative approach, which we do not take here, would
             be to check the term in kState.unknownMap to see if its
             head constructor is from a module building on the one
             introducing the key relation or not to determine if it
             should be I or K.  This would require passing around the
             module structure, so taking K as safe in all cases where
             it appears to apply is easier.
           -}
           ioval(sub.io,
                 (run.iovalue.1::sub.iovalue.1,
                  sub.iovalue.2));
}


--For known cases, no branches are pruned, and therefore we just need
--   to map the hyp and var names
--Don't need the case broken into separate blocks because of this
function runKnownCase
IOVal<([String], ProofState)> ::=
   caseInfo::[[(ProofState, [AnyCommand])]] abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  return runKnownCase_help(flatMap(\ l -> l, caseInfo), abella,
            config, parsers, ^incomingState, allThms, keyRels,
            typeEnv, relEnv, constrEnv, ioin);
}
function runKnownCase_help
IOVal<([String], ProofState)> ::=
   caseInfo::[(ProofState, [AnyCommand])] abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  --get commands and run them in Abella to get new proof state
  local run::IOVal<([String], ProofState)> =
      runCmds(head(caseInfo), allThms, ^incomingState, keyRels,
         typeEnv, relEnv, constrEnv, abella, config, parsers, ioin);

  --run it with the rest of the case
  local sub::IOVal<([String], ProofState)> =
      runKnownCase_help(tail(caseInfo), abella, config, parsers,
         run.iovalue.2, allThms, keyRels, typeEnv, relEnv,
         constrEnv, run.io);

  return
      case caseInfo of
      | [] -> ioval(ioin, ([], ^incomingState))
      | _::_ ->
        ioval(sub.io, (run.iovalue.1 ++ sub.iovalue.1, sub.iovalue.2))
      end;
}


--In preservability cases, each subgoal from the original may or may
--   not be present in the composition, as branches may prune.  Then
--   we need to check the current original state matches the current
--   composed state before using the commands.
function runPreservabilityCase
IOVal<([String], ProofState)> ::=
   preservabilityCase::[[(ProofState, [AnyCommand])]]
   abella::ProcessHandle config::Configuration parsers::AllParsers
   incomingState::ProofState allThms::[(QName, Metaterm)]
   keyRels::[QName] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   ioin::IOToken
{
  --get the mapping from old to new
  local unifyMap::ProofState = head(head(preservabilityCase)).1;
  unifyMap.mapTo = ^incomingState;
  unifyMap.typeEnv = typeEnv;
  unifyMap.relationEnv = relEnv;
  unifyMap.constructorEnv = constrEnv;

  --run the commands here
  local run::IOVal<([String], ProofState)> =
      foldl(\ rest::IOVal<([String], ProofState)>
              here::(ProofState, [AnyCommand]) ->
              let runThis::IOVal<([String], ProofState)> =
                  runCmds(here, allThms, rest.iovalue.2, keyRels,
                     typeEnv, relEnv, constrEnv, abella, config,
                     parsers, rest.io)
              in
                ioval(runThis.io,
                   (rest.iovalue.1 ++ runThis.iovalue.1,
                    runThis.iovalue.2))
              end,
            ioval(ioin, ([], ^incomingState)),
            head(preservabilityCase));

  --condition arguments to next bit on whether we run this part
  local nextState::ProofState =
      if unifyMap.mapSuccess then run.iovalue.2 else @incomingState;
  local nextIO::IOToken =
      if unifyMap.mapSuccess then run.io else ioin;

  --run it with the rest of the case
  local sub::IOVal<([String], ProofState)> =
      runPreservabilityCase(tail(preservabilityCase), abella, config,
         parsers, ^nextState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, nextIO);

  return
      case preservabilityCase of
      | [] -> ioval(ioin, ([], ^incomingState))
      | _::_ ->
        if unifyMap.mapSuccess
        then ioval(sub.io, (run.iovalue.1 ++ sub.iovalue.1,
                            sub.iovalue.2))
        else sub --skip this command as a pruned branch
      end;
}





--run the commands for a particular original proof state
function runCmds
IOVal<([String], ProofState)> ::= cmd::(ProofState, [AnyCommand])
   allThms::[(QName, Metaterm)] incomingState::ProofState
   keyRels::[QName] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   abella::ProcessHandle config::Configuration parsers::AllParsers
   ioin::IOToken
{
  --get the mapping from old to new
  local unifyMap::ProofState = cmd.1;
  unifyMap.mapTo = ^incomingState;
  unifyMap.typeEnv = typeEnv;
  unifyMap.relationEnv = relEnv;
  unifyMap.constructorEnv = constrEnv;

  --get the commands
  local cmds::[ProofCommand] =
      flatMap(
         \ c::AnyCommand ->
           decorate c with {
              mapHyps = unifyMap.hypMap;
              mapVars = unifyMap.varMap;
              allThms = allThms;
              oldHyps =
                 unifyMap.extensibella:common:abstractSyntax:hypList;
              newHyps =
                 incomingState.extensibella:common:abstractSyntax:hypList;
              keyRels = keyRels;
           }.mappedCmds,
         cmd.2);
  local cmdStrings::[String] = map((.abella_pp), cmds);

  local abellaOutput::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), cmds), abella, ioin, config);

  --send them to Abella and read the new proof state
  local newState::ProofState =
      fullStateProcessing(abellaOutput.iovalue, typeEnv,
         relEnv, constrEnv, parsers);

  --condition this on cmds being null because passing null cmds gives
  --   blank output back, interpreted as proof being done
  return if null(cmds)
         then ioval(ioin, ([], ^incomingState))
         else ioval(abellaOutput.io, (cmdStrings, ^newState));
}


--full processing for reading a proof state from Abella output, in
--   Extensibella but full names form
function fullStateProcessing
ProofState ::= stateStr::String typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   parsers::AllParsers
{
  local readState::ProofState =
      parsers.from_parse(stateStr,
         "<<Abella output>>").parseTree.ast.proof;
  local fromState::ProofState =
      decorate @readState with {
         typeEnv = typeEnv;
         relationEnv = relEnv;
         constructorEnv = constrEnv;
      }.fromAbella;
  return decorate @fromState with {
            typeEnv = typeEnv;
            relationEnv = relEnv;
            constructorEnv = constrEnv;
         }.full;
}
