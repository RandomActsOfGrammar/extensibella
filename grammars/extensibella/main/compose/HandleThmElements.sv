grammar extensibella:main:compose;

--modules and their remaining commands before handling this element
inherited attribute incomingMods::[(QName, DecCmds)] occurs on ThmElement;
--modules and their remaining commands after handling this element
synthesized attribute outgoingMods::[(QName, DecCmds)] occurs on ThmElement;
--commands to handle this element
synthesized attribute composedCmds::String occurs on ThmElement;

--pass in environments in MWDA-approved ways
inherited attribute relEnv::Env<RelationEnvItem> occurs on ThmElement;
inherited attribute constrEnv::Env<ConstructorEnvItem> occurs on ThmElement;
inherited attribute tyEnv::Env<TypeEnvItem> occurs on ThmElement;

--pass in stand-in rules for building R_P definition
inherited attribute standInRules_down::[(QName, Def)] occurs on ThmElement;

--pass in module builds-on information
inherited attribute buildsOns_down::[(QName, [QName])] occurs on ThmElement;

--pass down the ExtSize groups for determining how to build R -> R_P
inherited attribute knownExtSizes_down::[[QName]] occurs on ThmElement;
--pass up new ones
synthesized attribute newExtSizes::[[QName]] occurs on ThmElement;

--pass down the ExtInd information
--note we don't need groups in composition, unlike in proving, because
--   we don't check for valid grouping, so we only need information
--   about one at a time, not a full set
inherited attribute knownExtInds_down::[(QName, [String], Bindings,
                                         ExtIndPremiseList)] occurs on ThmElement;
--pass up new ones
synthesized attribute newExtInds::[(QName, [String], Bindings,
                                    ExtIndPremiseList)] occurs on ThmElement;

--pass in all thms known at this point:  theorem names and statements
inherited attribute allThms::[(QName, Metaterm)] occurs on ThmElement;
--gather new ones, but only ones that might be used in modular prfs
synthesized attribute newThms::[(QName, Metaterm)] occurs on ThmElement;

{-
  For some properties, we need to have a live version of Abella going
  to compare against to get names mapped correctly.  This is what will
  permit us to do so.

  Assumption:  ThmElement.runAbella_out is the IOToken after running
  the commands contained in ThmElement.composedCmds.
-}
inherited attribute liveAbella::ProcessHandle occurs on ThmElement;
inherited attribute runAbella::IOToken occurs on ThmElement;
inherited attribute allParsers::AllParsers occurs on ThmElement;
inherited attribute configuration::Configuration occurs on ThmElement;
synthesized attribute runAbella_out::IOToken occurs on ThmElement;

--build the definitions for R_ES and R_P
synthesized attribute extIndDefs::[String] occurs on ThmElement;


aspect default production
top::ThmElement ::=
{
  top.extIndDefs = [];

  top.runAbella_out =
      sendBlockToAbella(top.composedCmds, top.liveAbella,
                        top.runAbella, top.configuration).io;
  top.newExtSizes = [];
  top.newExtInds = [];
}

aspect production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, var bindings, thm statement, induction info)]
   thms::[(QName, Bindings, ExtBody, InductionOns)]
   alsos::[(QName, Bindings, ExtBody, InductionOns)]
   tag::Tag
{
  local extThms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
              rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, rest),
            endExtThms(), thms ++ alsos);
  extThms.relationEnv = top.relEnv;
  extThms.constructorEnv = top.constrEnv;
  extThms.typeEnv = top.tyEnv;
  extThms.expectedIHNum = 0;
  extThms.numMutualThms = length(thms) + length(alsos);

  --[(thm name, key relation, is host-y or not, requires R_P or not,
  --  bindings, body, intros name for key relation)] for thms
  local thmsInfo::[(QName, RelationEnvItem, Boolean, Boolean,
                    Bindings, ExtBody, String)] =
      map(--(induction rel, thm name, ...)
         \ p::(QName, QName, Bindings, ExtBody, InductionOns) ->
           let rei::RelationEnvItem =
               decorate p.1 with {relationEnv=top.relEnv;}.fullRel
           in
             (p.2, rei,
              --host-y if thm, rel, and pc all from same mod
              sameModule(p.2.moduleName, rei.name) &&
                 sameModule(p.2.moduleName, rei.pcType.name),
              --uses R_P if thm and rel from different mods
              !sameModule(p.2.moduleName, p.1),
              p.3, p.4,
              case p.5.keyRelLabelCandidates of
              | lbl::_ -> lbl
              | [] -> head(p.5.toList).1 --must be only one premise
              end)
           end,
         zip(extThms.keyRels, thms)); --cuts off the alsos part

  local multiple::Boolean = length(thms) + length(alsos) > 1;
  local extName::QName = --multiple theorems or the one uses R_P
      if multiple || !null(thmsInfo) && head(thmsInfo).4
      then toQName("$extThm_" ++ toString(genInt()))
      else fst(head(thms));

  --build the thm statements we need to declare and prove
  local proveThmStmts::[Metaterm] =
      --thms
      map(\ p::(QName, RelationEnvItem, Boolean, Boolean, Bindings,
                ExtBody, String) ->
            bindingMetaterm(forallBinder(),
               decorate p.5 with {
                  typeEnv = top.tyEnv;
               }.toAbella,
               decorate if useR_P --everything uses it if anything does
                        then decorate p.6 with {
                                makeProjRel = p.7;
                             }.projRelMade
                        else p.6 with {
                  relationEnv = top.relEnv;
                  constructorEnv = top.constrEnv;
                  typeEnv = top.tyEnv;
                  boundNames = p.5.usedNames;
               }.toAbella),
          thmsInfo) ++
      --alsos
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            bindingMetaterm(forallBinder(),
               decorate p.2 with {
                  typeEnv = top.tyEnv;
               }.toAbella,
               decorate p.3 with {
                  relationEnv = top.relEnv;
                  constructorEnv = top.constrEnv;
                  typeEnv = top.tyEnv;
                  boundNames = p.2.usedNames;
               }.toAbella),
          alsos);

  local declare::String =
      "Theorem " ++ extName.abella_pp ++ " : " ++
      foldr1(andMetaterm, proveThmStmts).abella_pp ++ ".\n";
  local inductions::String =
      implode("",
         map(\ l::[Integer] ->
               "induction on " ++ implode(" ", map(toString, l)) ++
               ". ", transpose(extThms.inductionNums)));
  local renames::String =
      implode(" ",
         map(\ p::(String, String, String) ->
               "rename " ++ p.1 ++ " to " ++ p.2 ++ ".",
             extThms.renamedIHs));
  local splitter::String =
      if length(thms) + length(alsos) == 1
      then ""
      else " split.";
  local proofStart::String =
      declare ++ inductions ++ renames ++ splitter;
  --send the first part to Abella
  local proofStart_abella::IOVal<String> =
      sendBlockToAbella(proofStart, top.liveAbella, top.runAbella,
                        top.configuration);


  --[(module name, [(property in group known in module,
  --                 R_P needed for property regardless of others,
  --                 using R_P requires a check)])]
  local knownPropsByModule::[(QName, [(QName, Boolean, Boolean)])] =
             --(module name, [builds ons])
      map(\ p::(QName, [QName]) ->
            (p.1,
             filterMap(
                \ prop::(QName, RelationEnvItem, Boolean, Boolean,
                         Bindings, ExtBody, String) ->
                  if contains(prop.1.moduleName, p.1::p.2)
                  then just((prop.1, prop.4, --known in p.1
                             case lookup(prop.2.name, top.knownExtInds_down) of
                             | just((args, binds, prems)) -> prems.len > 0
                             | nothing() -> error("ExtInd must exist")
                             end))
                  else nothing(), --not known there
                thmsInfo)),
          top.buildsOns_down);
  --the ExtInd validity checks given by each module
  --[(module name, [properties given checks in it])]
  local extIndsProvenByModule::[(QName, [QName])] =
               --(module, [(property, needed ExtInd when introduced,
               --           ExtInd use requires check)])
      map(\ p::(QName, [(QName, Boolean, Boolean)]) ->
              --anything requires R_P
            let extIndNeeded::Boolean = any(map(fst, map(snd, p.2)))
            in --anything old required R_P
            let importedNeededExtInd::Boolean =
                any(map(\ prop::(QName, Boolean, Boolean) ->
                          !sameModule(p.1, prop.1) && prop.2, p.2))
            in
              if !extIndNeeded
              then (p.1, []) --no ExtInd checks based on these properties
              else if importedNeededExtInd
              then (p.1,
                    --imported already checked ExtInd, so just new checks
                    filterMap(\ prop::(QName, Boolean, Boolean) ->
                                if sameModule(p.1, prop.1) --new prop
                                then just(prop.1) else nothing(), p.2))
              else --need for all but nothing checked already
                   (p.1,
                    filterMap(\ prop::(QName, Boolean, Boolean) ->
                                if prop.3 --requires check for using ExtInd
                                then just(prop.1) else nothing(), p.2))
            end end,
          knownPropsByModule);

  --[(module name, [properties in group known],
  --  count of ext ind checks proven)]
  local moduleThmInfo::[(QName, [QName], Integer)] =
     map(\ p::(QName, [(QName, Boolean, Boolean)]) ->
           (p.1, map(fst, p.2),
            length(lookup(p.1, extIndsProvenByModule).fromJust)),
         knownPropsByModule);

  --whether some property forces us to use ExtInd and R_P
  local useR_P::Boolean =
      any(map(\ p::(QName, RelationEnvItem, Boolean, Boolean,
                    Bindings, ExtBody, String) -> p.4, thmsInfo));

  --proof steps for thms and alsos; introducing module is first
  local basicProofInfo::[(QName, [(ProofState, [AnyCommand])])] =
      getThmProofSteps(top.incomingMods, map(fst, thms));
  --proof steps grouped by top goals, then goals inside
  local topGoalProofInfo::[(QName, [[(ProofState, [AnyCommand])]])] =
      map(\ p::(QName, [(ProofState, [AnyCommand])]) ->
            (p.1, splitAtAllGoals(p.2)),
          basicProofInfo);

  --proof steps for ExtInd checks by name
  --                               [(prop name, proof stuff)]
  local extIndCheckProofInfoNames::[(QName, [(ProofState, [AnyCommand])])] =
      flatMap(     --(module name, proof states and commands)
          \ modInfo::(QName, [[(ProofState, [AnyCommand])]]) ->
            let extIndChecks::[QName] = --must exist, even if empty
                lookup(modInfo.1, extIndsProvenByModule).fromJust
            in
            let numChecks::Integer = length(extIndChecks)
            in
            let cmds::[[(ProofState, [AnyCommand])]] =
                takeWhile(\ x::[(ProofState, [AnyCommand])] ->
                            head(head(x).1.currentSubgoal) <= numChecks,
                          modInfo.2)
            in
            let groups::[[[(ProofState, [AnyCommand])]]] =
                groupBy(\ l1::[(ProofState, [AnyCommand])]
                          l2::[(ProofState, [AnyCommand])] ->
                          head(head(l1).1.currentSubgoal) ==
                          head(head(l2).1.currentSubgoal),
                        cmds)
            in
              zip(extIndChecks,
                  --flatten each group
                  map(\ l::[[(ProofState, [AnyCommand])]] ->
                        flatMap(\ x -> x, l), groups))
            end end end end,
          topGoalProofInfo);
  --proof steps for ExtInd checks in order of the theorems
  --top-level groups are for separate ExtInd checks
  local extIndCheckProofInfo::[[(ProofState, [AnyCommand])]] =
      filterMap(lookup(_, extIndCheckProofInfoNames),
                map(fst, thmsInfo));

  --update the list of proof steps to drop the ones for the ExtInd checks
  local topGoalExtThmsProofInfo::[(QName, [[(ProofState, [AnyCommand])]])] =
      map(\ modInfo::(QName, [[(ProofState, [AnyCommand])]]) ->
            let extIndChecks::[QName] = --must exist, even if empty
                lookup(modInfo.1, extIndsProvenByModule).fromJust
            in
            let numChecks::Integer = length(extIndChecks)
            in
            let remainingCmds::[[(ProofState, [AnyCommand])]] =
                dropWhile(\ x::[(ProofState, [AnyCommand])] ->
                            if numChecks == 0
                            then false --don't drop anything for no checks
                            else head(head(x).1.currentSubgoal) <= numChecks,
                          modInfo.2)
            in
            let modAlsos::[QName] =
                filter(sameModule(modInfo.1, _), map(fst, alsos))
            in
            let nonAlsoCmds::[[(ProofState, [AnyCommand])]] =
                --number of subgoals before alsos
                case lookup(modInfo.1, numNotNewAlsosByModule) of
                          --when there are new alsos in this module
                | just(num) when length(modAlsos) > 0 ->
                  --take everything from non-also subgoals
                  takeWhile(\ l::[(ProofState, [AnyCommand])] ->
                              !subgoalStartsWith([num + 1],
                                  head(l).1.currentSubgoal),
                            remainingCmds)
                | _ -> remainingCmds
                end
            in
              (modInfo.1, nonAlsoCmds)
            end end end end end,
          topGoalProofInfo);





  --Commands for proving thms
  local thmProofs::IOVal<[String]> =
      buildExtThmProofs(thmsInfo, topGoalExtThmsProofInfo,
         if length(thms ++ alsos) == 1 then [] else [1], useR_P,
         top.allThms, top.tyEnv, top.relEnv, top.constrEnv,
         top.liveAbella, top.configuration, top.allParsers,
         map(\ p::(QName, RelationEnvItem, Boolean, Boolean, Bindings,
                   ExtBody, String) -> p.2.name, thmsInfo),
         moduleThmInfo, proofStart_abella.io);
  --Commands for proving alsos
  local alsosIntros::[String] =
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            let prems::[(Maybe<String>, Metaterm)] =
                decorate p.3 with {
                  typeEnv = top.tyEnv; relationEnv = top.relEnv;
                  constructorEnv = top.constrEnv;
                  boundNames = p.2.usedNames;
                }.premises
            in
              "intros " ++
              implode(" ",
                 generateExtIntrosNames(catMaybes(map(fst, prems)),
                                        prems)) ++ "."
            end,
          alsos);
  --count number of thms and old alsos known in each module
  local numNotNewAlsosByModule::[(QName, Integer)] =
      let checkNames::[QName] = map(fst, thms)
      in
      let checkAlsos::[QName] = map(fst, alsos)
      in
        map(\ b::(QName, [QName]) ->
              (b.1,
               length(filter(\ q::QName ->
                               --b.1::b.2 for old + new
                               contains(q.moduleName, b.1::b.2),
                             checkNames)) +
               length(filter(\ q::QName ->
                               --just b.2, not b.1, for old
                               contains(q.moduleName, b.2),
                             checkAlsos))),
            top.buildsOns_down)
      end end;
  local alsosCmds::[String] =
          --get down to the ones for alsos
      let justAlsoCmds::[[(ProofState, [AnyCommand])]] =
          flatMap(\ modInfo::(QName, [[(ProofState, [AnyCommand])]]) ->
                    --number of subgoals before alsos
                    case lookup(modInfo.1, numNotNewAlsosByModule) of
                    | just(num) ->
                      --drop everything from non-also subgoals
                      dropWhile(
                         \ l::[(ProofState, [AnyCommand])] ->
                           !subgoalStartsWith([num + 1],
                               head(l).1.currentSubgoal),
                         modInfo.2)
                    | nothing() -> []
                    end,
                  topGoalProofInfo)
      in --group commands for same also
      let groupedCmds::[[(ProofState, [AnyCommand])]] =
          map(\ l::[[(ProofState, [AnyCommand])]] ->
                flatMap(\ x::[(ProofState, [AnyCommand])] -> x, l),
              groupBy(\ l1::[(ProofState, [AnyCommand])]
                        l2::[(ProofState, [AnyCommand])] ->
                        head(head(l1).1.currentSubgoal) ==
                        head(head(l2).1.currentSubgoal),
                      justAlsoCmds))
      in
        map(\ full::[(ProofState, [AnyCommand])] ->
              implode("\n  ",
                 map(\ l::[(ProofState, [AnyCommand])] ->
                       implode("",
                          flatMap(\ a::[AnyCommand] ->
                                    map((.abella_pp), a),
                             map(snd, l))),
                   --group into commands for each also
                   groupBy(\ p1::(ProofState, [AnyCommand])
                             p2::(ProofState, [AnyCommand]) ->
                             subgoalRoot(p1.1.currentSubgoal) ==
                             subgoalRoot(p2.1.currentSubgoal),
                           full))),
            groupedCmds)
      end end;
  local fullAlsos::[String] =
      map(\ p::(String, String) -> p.1 ++ " " ++ p.2,
          zip(alsosIntros, alsosCmds));
  --send alsos to Abella
  local alsos_abella::IOVal<String> =
      sendBlockToAbella(implode(" ", fullAlsos), top.liveAbella,
         thmProofs.io, top.configuration);

  --After the main proof:
  local thmSplitNames::[String] =
      map(\ p::(QName, RelationEnvItem, Boolean, Boolean,
                Bindings, ExtBody, String) ->
            if p.4 --uses R_P
            then "$extSplit" ++ toString(genInt())
            else p.1.abella_pp,
          thmsInfo);
  local splitThm::String =
      if multiple
      then "\nSplit " ++ extName.abella_pp ++ " as " ++
           implode(", ", thmSplitNames ++
                   map((.abella_pp), map(fst, alsos))) ++ ".\n"
      else "\n";
  --turn all the R_P -> F thms into R -> F
  local buildFullProof::(String ::= String QName RelationEnvItem
                            Bindings ExtBody String [AnyCommand]) =
      \ partialName::String thmName::QName keyRel::RelationEnvItem
        bindings::Bindings body::ExtBody keyRelName::String
        extIndPremCmds::[AnyCommand] ->
        let decBody::Decorated ExtBody with {
               relationEnv, typeEnv, constructorEnv, boundNames} =
           decorate body with {
              relationEnv = top.relEnv; typeEnv = top.tyEnv;
              constructorEnv = top.constrEnv;
              boundNames = bindings.usedNames;
           }
        in
        let introsNames::[String] =
            generateExtIntrosNames(catMaybes(map(fst,
                                                 decBody.premises)),
               decBody.premises)
        in
        let extInd::([String], Bindings, ExtIndPremiseList) =
            lookup(keyRel.name, top.knownExtInds_down).fromJust
        in
        let premLen::Integer = extInd.3.len
        in
        let extIndValidName::String =
            "$extIndValid_" ++ toString(genInt())
        in
        let extIndValidPrf::String =
            "\nTheorem " ++ extIndValidName ++ " : " ++
            generateExtIndCheck(extInd.1, extInd.2, extInd.3,
               case lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                               a.isJust && b.isJust &&
                               a.fromJust == b.fromJust,
                             just(keyRelName), decBody.premises) of
               | just(relationMetaterm(_, args, _)) -> args.toList
               | _ -> error("Anything else impossible (extIndValidPrf)")
               end,
               bindings, decBody).abella_pp ++ ".\n" ++
            "intros " ++ implode(" ", introsNames) ++ ".\n" ++
            implode("\n", map((.abella_pp), extIndPremCmds))
        in
        let finalThm::String =
            "Theorem " ++ thmName.abella_pp ++ " : forall " ++
               bindings.abella_pp ++ ", " ++
               decBody.toAbella.abella_pp ++ ".\n" ++
            "intros " ++ implode(" ", introsNames) ++ ". " ++
            --build premises for ExtInd, if necessary
            (if premLen > 0
             then "$A: apply " ++ extIndValidName ++ " to " ++
                     implode(" ", introsNames) ++ ". "
             else "") ++
            --apply ExtInd to key rel and any other necessary args
            "$R: apply " ++ addP_name(keyRel.name).abella_pp ++
               " to " ++ implode(" ",
                            keyRelName::map(\ i::Integer ->
                                              if i == 0
                                              then "$A"
                                              else "$A" ++ toString(i),
                                            range(0, premLen))
                            ) ++ ". " ++
            --apply proven theorem using R_P to args
            "apply " ++ partialName ++ " to " ++
               implode(" ", map(\ x::String -> if x == keyRelName
                                               then "$R" else x,
                                introsNames)) ++ ". " ++
            "search."
        in
          if premLen > 0
          then extIndValidPrf ++ "\n\n" ++ finalThm
          else finalThm
        end end end end end end end;
  local applyExtInds::String =
      if multiple
      then let lst::[(String, QName, RelationEnvItem, Boolean, Boolean,
                      Bindings, ExtBody, String, [AnyCommand])] =
               foldl(\ --(extInd check proofs, built so far)
                       thusFar::([[(ProofState, [AnyCommand])]],
                          [(String, QName, RelationEnvItem, Boolean,
                            Boolean, Bindings, ExtBody, String,
                            [AnyCommand])])
                       p::(String, QName, RelationEnvItem, Boolean,
                           Boolean, Bindings, ExtBody, String) ->
                       let extIndPremLen::Integer =
                           case lookup(p.3.name, top.knownExtInds_down) of
                           | just((_, _, prems)) -> prems.len
                           | _ -> 0
                           end
                       in
                         if p.5 && extIndPremLen > 0
                         then case thusFar.1 of
                              | [] -> error("ThusFar.1 empty; for " ++
                                         justShow(p.2.pp))
                              | h::t ->
                                (t,
                                 thusFar.2 ++
                                 [(p.1, p.2, p.3, p.4, p.5, p.6, p.7, p.8,
                                   flatMap(snd, h))])
                              end
                         else (thusFar.1,
                               thusFar.2 ++ [(p.1, p.2, p.3, p.4, p.5,
                                              p.6, p.7, p.8, [])])
                       end,
                     (extIndCheckProofInfo, []),
                     zip(thmSplitNames, thmsInfo)).2
           in
             implode("\n",
               filterMap(\ p::(String, QName, RelationEnvItem, Boolean,
                               Boolean, Bindings, ExtBody, String,
                               [AnyCommand]) ->
                           if p.5 --uses R_P
                           then just(buildFullProof(p.1, p.2, p.3, p.6,
                                                    p.7, p.8, p.9))
                           else nothing(),
                         lst))
           end
      else if head(thmsInfo).4 --single thm, but uses R_P
      then let p::(QName, RelationEnvItem, Boolean, Boolean,
                   Bindings, ExtBody, String) = head(thmsInfo)
           in
             buildFullProof(extName.abella_pp,
                p.1, p.2, p.5, p.6, p.7,
                if null(extIndCheckProofInfo)
                then []
                else flatMap(snd,
                        case extIndCheckProofInfo of
                        | h::_ -> h
                        | [] ->
                          error("Expected proof of ExtInd validity; " ++
                                justShow(p.1.pp) ++ ", " ++
                                justShow(p.2.name.pp))
                        end))
           end
      else ""; --single thm that doesn't use R_P
  local after::String = splitThm ++ applyExtInds;
  --send after to Abella
  local after_abella::IOVal<String> =
      sendBlockToAbella(after, top.liveAbella, alsos_abella.io,
         top.configuration);

  local names::String =
      implode(", ", map(justShow, map((.pp), map(fst, thms) ++ map(fst, alsos))));
  top.composedCmds =
      "/*Start Extensible_Theorem " ++ names ++ "*/\n" ++
      proofStart ++ "\n " ++
      implode("\n ", thmProofs.iovalue ++ fullAlsos) ++
      after ++ "\n" ++
      "/*End " ++ names ++ "*/\n\n\n";


  top.outgoingMods =
      dropAllOccurrences(top.incomingMods, map(fst, thms));


  top.runAbella_out = after_abella.io;

  top.newThms =
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            (p.1, bindingMetaterm(forallBinder(), p.2,
             decorate p.3 with {
                relationEnv = top.relEnv; boundNames = p.2.usedNames;
                typeEnv = top.tyEnv; constructorEnv = top.constrEnv;
             }.toAbella)),
          thms ++ alsos);
}


aspect production projectionConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
                    tag::Tag
{
  --MWDA copy of body
  local bodyC::ExtBody = ^body;
  bodyC.relationEnv = top.relEnv;
  bodyC.constructorEnv = top.constrEnv;
  bodyC.typeEnv = top.tyEnv;
  bodyC.boundNames = binds.usedNames;

  local tcMods::[(QName, DecCmds)] =
      getAllOccurrences(top.incomingMods, [^name]);
  --first contains declaration and set-up
  local startPrf::String =
      case head(tcMods).2 of
      | addRunCommands(c, _) ->
        --set-up for projection constraint, including declaration
        implode("", map((.abella_pp), c.toAbella))
      | _ -> error("Must be projectionConstraint first")
      end;
  --rest of list provides the rest of the proof
  local restPrf::String =
      implode("", map(\ p::(QName, DecCmds) -> getProof(p.2).2,
                      tail(tcMods)));
  top.composedCmds =
      "/*Start Projection Constraint " ++ justShow(name.pp) ++ "*/\n" ++
      startPrf ++ " " ++ restPrf ++ "\n" ++
      "/*End " ++ justShow(name.pp) ++ "*/\n\n\n";

  --took these proofs, so drop them
  top.outgoingMods = dropAllOccurrences(top.incomingMods, [^name]);

  top.newThms =
      [(^name, bindingMetaterm(forallBinder(), ^binds, body.thm))];
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  --We need to decorate stmt with these inh attrs to get .toAbella
  --as stmt is not necessarily fully Abella (e.g. there can be strings
  --in it), but decorating stmt itself requires orphaned equations.
  --Thus we make a copy of it here.
  local cstmt::Metaterm = ^stmt;
  cstmt.typeEnv = top.tyEnv;
  cstmt.relationEnv = top.relEnv;
  cstmt.constructorEnv = top.constrEnv;
  cstmt.boundNames = [];

  local declaration::String =
      "Theorem " ++ name.abella_pp ++
      (if null(params) then ""
                       else "[" ++ implode(", ", params) ++ "]") ++
      " : " ++ cstmt.toAbella.abella_pp ++ ".\n";

  local updatePair::([(QName, DecCmds)], String) =
      updateMod(top.incomingMods, name.moduleName, getProof);

  top.outgoingMods = updatePair.1;
  top.composedCmds =
      "/*Start Theorem " ++ justShow(name.pp) ++ "*/\n" ++
      declaration ++ updatePair.2 ++ "\n" ++
      "/*End " ++ justShow(name.pp) ++ "*/\n\n\n";

  top.newThms = [(^name, ^stmt)];
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.composedCmds =
      "Split " ++ toSplit.abella_pp ++ " as " ++
      implode(", ", map((.abella_pp), newNames)) ++ ".\n\n";
  top.outgoingMods =
      updateMod(top.incomingMods, head(newNames).moduleName,
                \ c::DecCmds -> (dropFirstTopCommand(c), "")).1;

  top.newThms =
      zip(newNames,
          lookup(^toSplit, top.allThms).fromJust.splitConjunctions);
}


aspect production extIndElement
top::ThmElement ::=
   --[(rel name, rel arg names, all bindings, extra premises, IH names)]
   rels::[(QName, [String], Bindings, ExtIndPremiseList, [String])]
   --[(thm name, var bindings, thm statement, induction info)]
   thms::[(QName, Bindings, ExtBody, InductionOns)]
   alsos::[(QName, Bindings, ExtBody, InductionOns)]
   tag::Tag
{
  top.extIndDefs = [];

  top.newExtInds =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            (p.1, p.2, p.3, p.4),
          rels);

  --lemma names are used for proofs
  local lemmaStatements::[[(QName, Metaterm)]] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            buildExtSizeLemmas(p.1, p.2),
          rels);



  --whether or not this should use the extension size version of the
  --relation as a step between R and R_P
  local useES::Boolean =
      !null(filter(contains(head(rels).1, _), top.knownExtSizes_down));

  {-
    Initial Proof:  R_{ES} or R to R_P plus mutual theorems proof
  -}
  local extThms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
              rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, rest),
            endExtThms(), thms ++ alsos);
  extThms.relationEnv = top.relEnv;
  extThms.constructorEnv = top.constrEnv;
  extThms.typeEnv = top.tyEnv;
  extThms.expectedIHNum = length(rels) + 1;
  extThms.numMutualThms = length(rels) + length(thms) + length(alsos);
  --[(thm name, key relation, is host-y or not, requires R_P or not,
  --  bindings, body, intros name for key relation)] for thms
  local thmsInfo::[(QName, RelationEnvItem, Boolean, Boolean,
                    Bindings, ExtBody, String)] =
      map(--(induction rel, thm name, ...)
         \ p::(QName, QName, Bindings, ExtBody, InductionOns) ->
           let rei::RelationEnvItem =
               decorate p.1 with {relationEnv=top.relEnv;}.fullRel
           in
             (p.2, rei,
              --host-y if thm, rel, and pc all from same mod
              sameModule(p.2.moduleName, rei.name) &&
                 sameModule(p.2.moduleName, rei.pcType.name),
              --uses R_P if thm and rel from different mods
              !sameModule(p.2.moduleName, p.1),
              p.3, p.4,
              case p.5.keyRelLabelCandidates of
              | lbl::_ -> lbl
              | [] -> head(p.5.toList).1 --must be only one premise
              end)
           end,
         zip(extThms.keyRels, thms)); --cuts off the alsos part

  local toProjRelStatements::[Metaterm] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            buildExtIndThm(p.3, p.1, p.2, p.4.toList, useES),
          rels);
  local mutThmStatements::[Metaterm] =
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            bindingMetaterm(forallBinder(),
               decorate p.2 with {
                  typeEnv = top.tyEnv;
               }.toAbella,
               decorate p.3 with {
                  relationEnv = top.relEnv;
                  constructorEnv = top.constrEnv;
                  typeEnv = top.tyEnv;
                  boundNames = p.2.usedNames;
               }.toAbella),
          thms ++ alsos);
  local toProjRelStatement::Metaterm =
      foldr1(andMetaterm, toProjRelStatements ++ mutThmStatements);
  local toProjRelNames::[String] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            "$toProjRel__" ++ p.1.abella_pp,
          rels);
  local toProjRelInfo::[(QName, RelationEnvItem, Boolean, Boolean,
                         Bindings, ExtBody, String)] =
      map(\ p::(String, QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            let rei::RelationEnvItem =
                decorate p.2 with {relationEnv = top.relEnv;}.fullRel
            in
            let relName::String =
                freshName("R", filterMap(fst, p.5.toList))
            in
            let body::ExtBody =
                buildExtIndThmExtBody(p.4, p.2, p.3, p.5.toList,
                                      useES, relName)
            in --thm name is used only for the module, so rel name works
              (p.2, rei,
               --thm and rel always from same mod in ExtInd, so only check pc
               sameModule(rei.name, rei.pcType.name),
               false, p.4, body, relName)
            end end end,
          zip(toProjRelNames, rels));
  local toProjRelProveName::String =
      if length(toProjRelNames) == 1 && length(mutThmStatements) == 0
      then head(toProjRelNames)
      else "$toProjRel_" ++ toString(genInt());
  local bodyIndNums::[[Integer]] =
      if useES
      then repeat([2, 1], length(rels)) --acc and rel
      else repeat([1], length(rels));   --just rel
  local toProjRelProofStart::String =
      implode(" ",
         map(\ l::[Integer] ->
               "induction on " ++ implode(" ", map(toString, l)) ++
               ".",
             transpose(bodyIndNums ++ extThms.inductionNums))) ++
      if length(rels) > 1 then " split.\n" else "\n";
  local toProjRelSetups::[String] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            let givenLabels::[String] = filterMap(fst, p.4.toList)
            in
            let rName::String = freshName("R", givenLabels)
            in
            let names::[String] =
                [rName] ++
                (if useES then [freshName("Acc", givenLabels)]
                          else []) ++
                map(fromMaybe("_", _), map(fst, p.4.toList))
            in
              "intros " ++ implode(" ", names) ++ ". " ++
              rName ++ ": case " ++ rName ++ " (keep)."
            end end end,
          rels);
  --proof information from all the modules where this occurs
  --filter out the ones where there are no proofs
  local toProjRelProofInfo::[(QName, [(ProofState, [AnyCommand])])] =
      filter(\ p::(QName, [(ProofState, [AnyCommand])]) -> !null(p.2),
             getExtIndProofSteps(top.incomingMods, map(fst, rels)));
  local toProjRelSplitProofInfo::[(QName, [[(ProofState, [AnyCommand])]])] =
      if length(rels) == 1
         --only one proof, so all go together
      then map(\ p::(QName, [(ProofState, [AnyCommand])]) -> (p.1, [p.2]),
               toProjRelProofInfo)
         --multiple proofs, so top-level goals are the splits
      else map(\ p::(QName, [(ProofState, [AnyCommand])]) ->
                 (p.1, splitAtTopGoals(p.2)),
               toProjRelProofInfo);
  --
  local toProjRelProofInit::String =
      "Theorem " ++ toProjRelProveName ++ " : " ++
      toProjRelStatement.abella_pp ++ ".\n" ++
      toProjRelProofStart;
  local toProjRelProofInit_abella::IOVal<String> =
      sendBlockToAbella(toProjRelProofInit, top.liveAbella,
                        top.runAbella, top.configuration);
  --information about which relations are proven in which modules
  local toProjRelModuleThmInfo::[(QName, [QName], Integer)] =
      map(\ modInfo::(QName, [QName]) ->
            (modInfo.1,
             filter(\ rel::QName ->
                      --modInfo.1::modInfo.2 to include current one
                      contains(rel.moduleName, modInfo.1::modInfo.2),
                    map(fst, rels) ++ map(fst, thms ++ alsos)),
             0),
          top.buildsOns_down);
  --joining the set-up and proofs into one
  local toProjRelProofContents::IOVal<[String]> =
      buildExtThmProofs(toProjRelInfo ++ thmsInfo,
         map(\ p::(QName, [(ProofState, [AnyCommand])]) ->
               (p.1, splitAtAllGoals(p.2)),
             toProjRelProofInfo),
         if length(rels) == 1 && extThms.len == 0
         then [] else [1], false,
         top.allThms, top.tyEnv, top.relEnv, top.constrEnv,
         top.liveAbella, top.configuration, top.allParsers,
         map(fst, rels), toProjRelModuleThmInfo,
         toProjRelProofInit_abella.io);
  --Commands for proving alsos
  local alsosIntros::[String] =
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            let prems::[(Maybe<String>, Metaterm)] =
                decorate p.3 with {
                  typeEnv = top.tyEnv; relationEnv = top.relEnv;
                  constructorEnv = top.constrEnv;
                  boundNames = p.2.usedNames;
                }.premises
            in
              "intros " ++
              implode(" ",
                 generateExtIntrosNames(catMaybes(map(fst, prems)),
                                        prems)) ++ "."
            end,
          alsos);
  --count number of rels, thms, and old alsos known in each module
  local numNotNewAlsosByModule::[(QName, Integer)] =
      let checkNames::[QName] = map(fst, rels) ++ map(fst, thms)
      in
      let checkAlsos::[QName] = map(fst, alsos)
      in
        map(\ b::(QName, [QName]) ->
              (b.1,
               length(filter(\ q::QName ->
                               --b.1::b.2 for old + new
                               contains(q.moduleName, b.1::b.2),
                             checkNames)) +
               length(filter(\ q::QName ->
                               --just b.2, not b.1, for old
                               contains(q.moduleName, b.2),
                             checkAlsos))),
            top.buildsOns_down)
      end end;
  local alsosCmds::[String] =
      map(\ full::[(ProofState, [AnyCommand])] ->
            implode("\n  ",
               map(\ l::[(ProofState, [AnyCommand])] ->
                     implode("",
                        flatMap(\ a::[AnyCommand] ->
                                  map((.abella_pp), a),
                           map(snd, l))),
                 --group into commands for each also
                 groupBy(\ p1::(ProofState, [AnyCommand])
                           p2::(ProofState, [AnyCommand]) ->
                           subgoalRoot(p1.1.currentSubgoal) ==
                           subgoalRoot(p2.1.currentSubgoal),
                         full))),
          --get down to the ones for alsos
          flatMap(\ modInfo::(QName, [[(ProofState, [AnyCommand])]]) ->
                    --number of subgoals before alsos
                    case lookup(modInfo.1, numNotNewAlsosByModule) of
                    | just(num) ->
                      --drop everything from non-also subgoals
                      dropWhile(
                         \ l::[(ProofState, [AnyCommand])] ->
                           !subgoalStartsWith([num + 1],
                               head(l).1.currentSubgoal),
                         modInfo.2)
                    | nothing() -> []
                    end,
                  toProjRelSplitProofInfo));
  local fullAlsos::[String] =
      map(\ p::(String, String) -> p.1 ++ " " ++ p.2,
          zip(alsosIntros, alsosCmds));
  --send alsos to Abella
  local alsos_abella::IOVal<String> =
      sendBlockToAbella(implode(" ", fullAlsos), top.liveAbella,
         toProjRelProofContents.io, top.configuration);
  local afterToProjRel::String =
      if length(toProjRelNames) == 1 && extThms.len == 0
      then "" --nothing to split
      else "Split " ++ toProjRelProveName ++ " as " ++
           implode(", ", toProjRelNames ++
              map((.abella_pp), map(fst, thms ++ alsos))) ++ ".\n";
  local toProjRelAfter_abella::IOVal<String> =
      sendBlockToAbella(afterToProjRel, top.liveAbella,
         alsos_abella.io, top.configuration);
  local fullToProjRel::String =
      toProjRelProofInit ++
      implode(" ", toProjRelProofContents.iovalue) ++ "\n" ++
      implode("\n ", fullAlsos) ++
      afterToProjRel;

  {-
    Final Proof:  R to R_P proof
  -}
  --Note that if we don't use R_ES, this is exactly the same as what
  --was proved modularly; however, it is easier to use that here than
  --to adjust the naming elsewhere.
  local extIndProofs::[String] =
      map(\ p::(Integer, QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            let stmt::Metaterm = buildExtIndLemma(p.2, p.3, p.4, p.5).2
            in
            let introsNames::[String] =
                map(\ i::Integer -> "A" ++ toString(i),
                    range(1, p.5.len + 1))
            in
            let premNames::[String] =
                if useES then "ES"::"Acc"::introsNames
                         else "R"::introsNames
            in
              "Theorem " ++ addP_name(p.2).abella_pp ++ " : " ++
                 stmt.abella_pp ++ ".\n " ++
              "intros R " ++ implode(" ", introsNames) ++ ". " ++
              (if useES
               then
                 --make R_{ES}
                 "ES: apply " ++
                    head(tail(tail(tail(elemAtIndex(lemmaStatements,
                                           p.1))))).1.abella_pp ++
                    " to R.\n" ++
                 --make acc N
                 let lemmas::[(QName, Metaterm)] =
                     elemAtIndex(lemmaStatements, p.1)
                 in
                   "P: apply " ++ head(lemmas).1.abella_pp ++
                      " to ES. " ++
                   "Is: apply " ++ head(tail(lemmas)).1.abella_pp ++
                      " to ES. " ++
                   "Acc: apply extensibella-$-stdLib-$-all_acc to Is P.\n"
                 end
               else "") ++
              --make R_P
              "apply " ++ elemAtIndex(toProjRelNames, p.1) ++
                 " to " ++ implode(" ", premNames) ++ ". search."
            end end end,
          enumerate(rels));


  local displayNames::String =
      implode(", ", map(justShow, map((.pp), map(fst, rels)))) ++
      if length(thms) > 0
      then " and_thms " ++
           implode(", ", map(justShow, map((.pp), map(fst, thms))))
      else "";
  top.composedCmds =
      "/*Start Ext_Ind for " ++ displayNames ++ "*/\n" ++
      fullToProjRel ++ "\n" ++
      implode("\n", extIndProofs) ++ "\n" ++
      "/*End Ext_Ind for " ++ displayNames ++ "*/\n\n\n";

  top.runAbella_out =
      sendBlockToAbella(implode("\n", extIndProofs), top.liveAbella,
         toProjRelAfter_abella.io, top.configuration).io;

  top.outgoingMods =
      dropExtInd(top.incomingMods, map(fst, rels));

  top.newThms =
      --addP lemma for each relation
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            buildExtIndLemma(p.1, p.2, p.3, p.4),
          rels) ++
      --mutual theorems
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            (p.1, bindingMetaterm(forallBinder(), p.2,
             decorate p.3 with {
                relationEnv = top.relEnv; boundNames = p.2.usedNames;
                typeEnv = top.tyEnv; constructorEnv = top.constrEnv;
             }.toAbella)),
          thms ++ alsos);
}

function buildExtIndThmExtBody
ExtBody ::= boundVars::Bindings rel::QName relArgs::[String]
            premises::[(Maybe<String>, Metaterm)] useExtSize::Boolean
            relPremName::String
{
  local args::[Term] =
      map(\ x::String -> nameTerm(toQName(x), nothingType()), relArgs);
  local n::String = freshName("N", boundVars.usedNames);
  local relPrem::Metaterm =
      relationMetaterm(@rel,
         toTermList(args ++
            if useExtSize
            then [nameTerm(toQName(n), nothingType())]
            else []),
         emptyRestriction());
  local extSize::Metaterm =
      relationMetaterm(extSizeQName(rel.sub),
         toTermList(args ++
            if useExtSize
            then [nameTerm(toQName(n), nothingType())]
            else []),
         emptyRestriction());
  local accPremName::String =
      freshName("Acc", filterMap(fst, premises));
  local acc::Metaterm =
      relationMetaterm(toQName("acc"),
         toTermList([nameTerm(toQName(n), nothingType())]),
         emptyRestriction());
  local conc::Metaterm =
      relationMetaterm(projRelQName(rel.sub), toTermList(args),
                       emptyRestriction());
  local base::ExtBody =
      foldr(\ p::(Maybe<String>, Metaterm) rest::ExtBody ->
              addLabelExtBody(
                 case p.1 of
                 | just(n) -> n
                 | nothing() -> "_"
                 end, p.2, rest),
            endExtBody(^conc), premises);
  return
      if useExtSize
      then addLabelExtBody(relPremName, ^relPrem,
              addLabelExtBody(accPremName, ^acc, ^base))
      else addLabelExtBody(relPremName, ^relPrem, ^base);
}

function buildProjRel_standInRules
TopCommand ::= rels::[(QName, [String])] standInRules::[(QName, Def)]
               env::Env<RelationEnvItem> cenv::Env<ConstructorEnvItem>
               buildsOns::[(QName, [QName])]
{
  return buildProjRelDef(buildDefInfo(rels, standInRules, env),
                         buildsOns, env, cenv);
}
function buildDefInfo
[(QName, ([String], [String], Maybe<Metaterm>),
  [([Term], Maybe<Metaterm>)], RelationEnvItem)] ::=
     rels::[(QName, [String])] standInRules::[(QName, Def)]
     env::Env<RelationEnvItem>
{
  local r::(QName, [String]) =
      head(rels);
  local rei::RelationEnvItem = head(lookupEnv(r.1, env));

  --must exist if modular proof checked out
  local qRuleDef::Def = lookup(r.1, standInRules).fromJust;
  local qRule::([String], [String], Maybe<Metaterm>) =
      case qRuleDef of
      | factDef(rel, args) ->
        --args must be vars and usedNames contains vars, so mapping
        --(.usedNames) should get just the names
        (flatMap((.usedNames), args.toList), [], nothing())
      | ruleDef(rel, args,
                bindingMetaterm(existsBinder(), binds, body)) ->
        (flatMap((.usedNames), args.toList),
         map(fst, binds.toList), just(^body))
      | ruleDef(rel, args, body) ->
        (flatMap((.usedNames), args.toList), [], just(^body))
      end;

  local first::(QName, ([String], [String], Maybe<Metaterm>),
                [([Term], Maybe<Metaterm>)], RelationEnvItem) =
      (r.1, qRule, rei.defsList, rei);
  return case rels of
         | [] -> []
         | _::t -> first::buildDefInfo(t, standInRules, env)
         end;
}


function indexOfName
Integer ::= q::QName l::[(QName, a)]
{
  return case l of
         | [] -> error("not in list")
         | (x, _)::_ when x == ^q -> 0
         | _::rest -> indexOfName(^q, rest) + 1
         end;
}


aspect production extSizeElement
top::ThmElement ::= rels::[(QName, [String])] tag::Tag
{
  {-
    Definition of R_{ES} relation
  -}
  local extSizeDef::String =
      buildExtSize(map(fst, rels), top.relEnv, top.constrEnv,
                   top.buildsOns_down).abella_pp;
  top.extIndDefs = [extSizeDef];

  top.newExtSizes = [map(fst, rels)];


  --get the information we need about the relation clauses to build
  --   the individual proofs
  --[[(number of adds, [(1-based indices for R_{ES} premises,
  --                     0-based IH indices)], is host)]]
  --inner list is grouped by relation
  --   (e.g. [[rel 1 clauses], [rel 2 clauses], ...])
  local clauseInfo::[[(Integer, [(Integer, Integer)], Boolean)]] =
      map(\ q::QName ->
            let rel::RelationEnvItem =
                decorate q with {relationEnv=top.relEnv;}.fullRel
            in --[(extension clause or not, split-up body)]
            let splits::[(Boolean, [Metaterm])] =
                filterMap(
                    \ d::([Term], Maybe<Metaterm>) ->
                      let prems::[Metaterm] = splitRulePrems(d.2)
                      in
                      --check the rule isn't impossible
                      let unifyPrems::([Term], [Term]) =
                          premiseUnificationPairs(prems)
                      in
                      let unifies::Boolean =
                          unifyTermsSuccess(unifyPrems.1, unifyPrems.2)
                      in
                      let pc::Decorated Term with {relationEnv, constructorEnv} =
                          decorate elemAtIndex(d.1, rel.pcIndex) with {
                             relationEnv = top.relEnv;
                             constructorEnv = top.constrEnv;
                          }
                      in
                      let constr::QName = pc.headConstructor
                      in
                      let isExtRule::Boolean =
                          --if not structured, must be from host
                          pc.isStructured &&
                          --check if PC module builds on rel module
                          contains(rel.name.moduleName,
                             lookup(constr.moduleName,
                                    top.buildsOns_down).fromJust)
                      in
                        if unifies
                        then just((isExtRule, prems))
                        else nothing()
                      end end end end end end,
                    rel.defsList)
            in --premises that are part of this group of rels
            let hereRels::[(Boolean, [Integer])] =
                map(\ l::(Boolean, [Metaterm]) ->
                      (l.1,
                       map(\ m::Metaterm ->
                             case m of
                             | relationMetaterm(q, _, _)
                               when contains(^q, map(fst, rels)) ->
                               indexOfName(^q, rels) --index of IH
                             | _ -> -1
                             end,
                          l.2)),
                    splits)
            in
              map(\ l::(Boolean, [Integer]) ->
                    let plusCount::Integer =
                        length(filter(\ x -> x >= 0, l.2)
                              ) - if !l.1 then 1 else 0
                    in
                      (plusCount,
                       filterMap(\ p::(Integer, Integer) ->
                                   if p.2 >= 0
                                   then just(p)
                                   else nothing(),
                          enumerateFrom(plusCount + 1, l.2)),
                       !l.1)
                    end,
                  hereRels)
            end end end,
          map(fst, rels));

  {-
    Lemmas about R_{ES}
  -}
  local lemmaStatements::[[(QName, Metaterm)]] =
      map(\ p::(QName, [String]) -> buildExtSizeLemmas(p.1, p.2), rels);
  local jointLemmaNames::(String, String, String, String) =
      --first make a sanity/extension check
      if length(head(lemmaStatements)) != 4
      then error("Number of ExtSize lemmas must be 4")
      else case lemmaStatements of
           | [[a, b, c, d]] -> --only one rel, so use actual names
             (a.1.abella_pp, b.1.abella_pp, c.1.abella_pp, d.1.abella_pp)
           | _ -> --multiple rels together, so use fake then split
             ("$extSizeThm_" ++ toString(genInt()),
              "$extSizeThm_" ++ toString(genInt()),
              "$extSizeThm_" ++ toString(genInt()),
              "$extSizeThm_" ++ toString(genInt()))
           end;
  --leave it as a list because Silver pairs of pairs don't really work
  local provingLemmaStatements::[(String, Metaterm)] =
      [
       (jointLemmaNames.1,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(l).2,
                   lemmaStatements))),
       (jointLemmaNames.2,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(tail(l)).2,
                   lemmaStatements))),
       (jointLemmaNames.3,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(tail(tail(l))).2,
                   lemmaStatements))),
       (jointLemmaNames.4,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(tail(tail(tail(l)))).2,
                   lemmaStatements)))
      ];
  local lemmaInduction::String =
      "induction on " ++
      implode(" ", repeat("1",
                      length(lemmaStatements))) ++ "." ++
      if length(lemmaStatements) == 1
      then "\n" else " split.\n";
  local lemmaPrfParts::[[(String, String, String)]] =
      map(--[(plus count, [(ES premise, IH num)], is host)]
        \ l::[(Integer, [(Integer, Integer)], Boolean)] ->
          map(
            \ p::(Integer, [(Integer, Integer)], Boolean) ->
              let basicPrf::String =
                  implode("",
                     map(\ ip::(Integer, Integer) ->
                           " apply IH" ++ (if ip.2 == 0 then ""
                                           else toString(ip.2)) ++
                           " to ES" ++ toString(ip.1) ++ ".",
                         p.2))
              in
              let r::[Integer] = range(1, p.1 + 1)
              in
                 --non-negative
                (basicPrf ++
                 foldr(\ i::Integer rest::String ->
                         rest ++ " apply extensibella-$-stdLib-$-" ++
                         "lesseq_integer__add_positive to _ _ ES" ++
                         toString(i) ++ ".", "",
                       r) ++ " search.\n",
                 --is_integer
                 basicPrf ++
                 foldr(\ i::Integer rest::String ->
                         rest ++ " apply extensibella-$-stdLib-$-" ++
                         "plus_integer_is_integer to _ _ ES" ++
                         toString(i) ++ ".", "",
                       r) ++ " search.\n",
                 --dropP
                 basicPrf ++ " search.\n")
                end end,
            l),
          clauseInfo);
  local lemmaPrfs::(String, String, String) =
      foldr(\ l::[(String, String, String)]
              rest::(String, String, String) ->
              let sub::(String, String, String) =
                foldr(\ here::(String, String, String)
                        rest::(String, String, String) ->
                        (here.1 ++ rest.1, here.2 ++ rest.2,
                         here.3 ++ rest.3),
                      rest, l)
              in
                ("intros ES. ES1: case ES.\n" ++ sub.1,
                 "intros ES. ES1: case ES.\n" ++ sub.2,
                 "intros ES. ES1: case ES.\n" ++ sub.3)
              end,
            ("", "", ""), lemmaPrfParts);
  local endLemmaCommands::String =
      if length(lemmaStatements) == 1
      then "" --nothing to split
      else "\n" ++
           "Split " ++ jointLemmaNames.1 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] -> head(l).1,
                         lemmaStatements))) ++ ".\n" ++
           "Split " ++ jointLemmaNames.2 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] -> head(tail(l)).1,
                         lemmaStatements))) ++ ".\n" ++
           "Split " ++ jointLemmaNames.3 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] ->
                           head(tail(tail(l))).1,
                         lemmaStatements))) ++ ".\n";
  --this is actually only the first 3 because the last one is R -> R_ES,
  --and starting from R instead of from R_ES gives it a different nature
  local fullLemmas::String =
      "Theorem " ++ head(provingLemmaStatements).1 ++ " : " ++
         head(provingLemmaStatements).2.abella_pp ++ ".\n" ++
         lemmaInduction ++ lemmaPrfs.1 ++ "\n" ++
      "Theorem " ++ head(tail(provingLemmaStatements)).1 ++ " : " ++
         head(tail(provingLemmaStatements)).2.abella_pp ++ ".\n" ++
         lemmaInduction ++ lemmaPrfs.2 ++ "\n" ++
      "Theorem " ++ head(tail(tail(provingLemmaStatements))).1 ++
         " : " ++ head(tail(tail(provingLemmaStatements))
                                ).2.abella_pp ++
         ".\n" ++ lemmaInduction ++ lemmaPrfs.3 ++
       endLemmaCommands;

  {-
    R to R_{ES} proof
  -}
  local toExtSizeStatement::Metaterm =
      foldr1(andMetaterm,
         map(\ p::(QName, [String]) ->
               let num::String = freshName("N", p.2)
               in
                 bindingMetaterm(forallBinder(),
                    toBindings(p.2),
                    impliesMetaterm(
                       relationMetaterm(p.1,
                          toTermList(map(basicNameTerm, p.2)),
                          emptyRestriction()),
                       bindingMetaterm(existsBinder(),
                          toBindings([num]),
                          relationMetaterm(extSizeQName(p.1.sub),
                             toTermList(map(basicNameTerm, p.2 ++ [num])),
                             emptyRestriction()))))
               end,
             rels));
  local toExtSizeProveName::String = jointLemmaNames.4;
  local toExtSizeProofStart::String =
      "induction on " ++ implode(" ", repeat("1", length(rels))) ++
      ". rename IH to IH0." ++ --simplifies building the proof code
      if length(rels) > 1 then " split." else "";
  local toExtSizeProofs::[String] =
      map(
        \ l::[(Integer, [(Integer, Integer)], Boolean)] ->
          " intros R. R1: case R.\n  " ++
          implode("\n  ",
             map(--(plus count, [(R premise, IH num)], is host)
               \ p::(Integer, [(Integer, Integer)], Boolean) ->
                         --[(hyp name, application, IH num)]
                 let appIHs::[(String, String, Integer)] =
                     map(\ ip::(Integer, Integer) ->
                           let hyp::String =
                               "ES" ++ toString(genInt())
                           in
                             (hyp,
                              hyp ++ ": apply IH" ++ toString(ip.2) ++
                              --subtract to get back to R indices from
                              --R_{ES} indices
                              " to R" ++ toString(ip.1 - p.1) ++ ".",
                              ip.2)
                           end, p.2)
                 in       --[(hyp name, application)]
                 let appIses::[(String, String)] =
                     map(\ ep::(String, String, Integer) ->
                           let hyp::String =
                               "Is" ++ toString(genInt())
                           in
                             (hyp,
                              hyp ++ ": apply " ++
                              head(tail(elemAtIndex(lemmaStatements,
                                           ep.3))).1.abella_pp ++
                              " to " ++ ep.1 ++ ".")
                           end, appIHs)
                 in
                 let adds::(String, String) =
                     foldr(                  --(hyp name, application)
                        \ isp::(String, String) rest::(String, String) ->
                          let plusHyp::String =
                              "Plus" ++ toString(genInt())
                          in
                          let isHyp::String =
                              "Is" ++ toString(genInt())
                          in
                            (isHyp,
                             rest.2 ++ " " ++
                             plusHyp ++ ": apply " ++
                                "extensibella-$-stdLib-$-" ++
                                "plus_integer_total to " ++ isp.1 ++
                                " " ++ rest.1 ++ ". " ++
                             isHyp ++ ": apply " ++
                                "extensibella-$-stdLib-$-" ++
                                "plus_integer_is_integer to _ _ " ++
                                plusHyp ++ ".")
                          end end,
                        (last(appIses).1, ""), init(appIses))
                 in
                 let finalAdd::String =
                     if p.3
                     then "" --host, so don't add 1
                     else " apply extensibella-$-stdLib-$-" ++
                            "plus_integer_total to _ " ++ adds.1 ++
                            " with N1 = $posInt ($succ $zero)."
                 in
                   if null(p.2) then "search."
                   else
                     implode(" ",
                        map(\ p::(String, String, Integer) -> p.2,
                            appIHs)) ++ " " ++
                     implode(" ", map(\ p::(String, String) -> p.2,
                                      appIses)) ++ " " ++
                     adds.2 ++ finalAdd ++ " search."
                 end end end end, l)),
        clauseInfo);
  local afterToExtSize::String =
      if length(rels) == 1
      then "" --nothing to split
      else "Split " ++ toExtSizeProveName ++ " as " ++
           implode(", ",
              map((.abella_pp),
                  map(\ l::[(QName, Metaterm)] ->
                        head(tail(tail(tail(l)))).1,
                      lemmaStatements))) ++ ".\n";
  local fullToExtSize::String =
      "Theorem " ++ toExtSizeProveName ++ " : " ++
      toExtSizeStatement.abella_pp ++ ".\n" ++
      toExtSizeProofStart ++ "\n" ++
      implode("\n", toExtSizeProofs) ++ "\n" ++
      afterToExtSize;


  local displayNames::String =
      implode(", ", map(justShow, map((.pp), map(fst, rels))));
  top.composedCmds =
      "/*Start Ext_Size for " ++ displayNames ++ "*/\n" ++
      fullLemmas ++ "\n" ++ fullToExtSize ++ "\n" ++
      "/*End Ext_Size for " ++ displayNames ++ "*/\n\n\n";

  top.outgoingMods =
      dropExtSize(top.incomingMods, map(fst, rels));


  --these are the only relevant new things
  top.newThms = flatMap(\ l -> l, lemmaStatements);
}


aspect production projRelElement
top::ThmElement ::= rels::[(QName, [String])] tag::Tag
{
  {-
    Definition of R_P relation
  -}
  local projRelDef::String =
      buildProjRel_standInRules(rels, top.standInRules_down,
         top.relEnv, top.constrEnv, top.buildsOns_down).abella_pp;
  top.extIndDefs = [projRelDef];


  --get the information we need about the relation clauses to build
  --   the individual proofs
  --[[(number of adds, [(1-based indices for R_{ES} premises,
  --                     0-based IH indices)], is host)]]
  --inner list is grouped by relation
  --   (e.g. [[rel 1 clauses], [rel 2 clauses], ...])
  local clauseInfo::[[(Integer, [(Integer, Integer)], Boolean)]] =
      map(\ q::QName ->
            let rel::RelationEnvItem =
                decorate q with {relationEnv=top.relEnv;}.fullRel
            in --[(extension clause or not, split-up body)]
            let splits::[(Boolean, [Metaterm])] =
                filterMap(
                    \ d::([Term], Maybe<Metaterm>) ->
                      let prems::[Metaterm] = splitRulePrems(d.2)
                      in
                      --check the rule isn't impossible
                      let unifyPrems::([Term], [Term]) =
                          premiseUnificationPairs(prems)
                      in
                      let unifies::Boolean =
                          unifyTermsSuccess(unifyPrems.1, unifyPrems.2)
                      in
                        if unifies
                        then just((!sameModule(q.moduleName,
                                      elemAtIndex(d.1, rel.pcIndex
                                                 ).headConstructor),
                                   prems))
                        else nothing()
                      end end end,
                    rel.defsList)
            in --premises that are part of this group of rels
            let hereRels::[(Boolean, [Integer])] =
                map(\ l::(Boolean, [Metaterm]) ->
                      (l.1,
                       map(\ m::Metaterm ->
                             case m of
                             | relationMetaterm(q, _, _)
                               when contains(^q, map(fst, rels)) ->
                               indexOfName(^q, rels) --index of IH
                             | _ -> -1
                             end,
                          l.2)),
                    splits)
            in
              map(\ l::(Boolean, [Integer]) ->
                    let plusCount::Integer =
                        length(filter(\ x -> x >= 0, l.2)
                              ) - if !l.1 then 1 else 0
                    in
                      (plusCount,
                       filterMap(\ p::(Integer, Integer) ->
                                   if p.2 >= 0
                                   then just(p)
                                   else nothing(),
                          enumerateFrom(plusCount + 1, l.2)),
                       !l.1)
                    end,
                  hereRels)
            end end end,
          map(fst, rels));

  {-
    R_P to R proof
  -}
  local lemmaStatements::[[(QName, Metaterm)]] =
      map(\ p::(QName, [String]) -> buildProjRelLemmas(p.1, p.2),
          rels);
  local jointDropPName::String =
      --first make a sanity/extension check
      if length(head(lemmaStatements)) != 1
      then error("Number of ProjRel lemmas must be 4")
      else case lemmaStatements of
           | [[a]] -> --only one rel, so use actual name
             a.1.abella_pp
           | _ -> --multiple rels together, use fake then split
             "$dropP_" ++ toString(genInt())
           end;
  local jointDropPStmt::Metaterm =
      foldr1(andMetaterm,
             map(\ l::[(QName, Metaterm)] -> head(l).2,
                 lemmaStatements));
  local dropPProofStart::String =
      "induction on " ++ implode(" ", repeat("1", length(rels))) ++
      "." ++ if length(rels) == 1 then "\n" else " split.\n ";
  local dropPProofs::[String] =
      map(--[(plus count, [(ES premise, IH num)], is host)]
        \ l::[(Integer, [(Integer, Integer)], Boolean)] ->
          "intros R. R: case R (keep).\n " ++
          implode("\n ",
             map(\ p::(Integer, [(Integer, Integer)], Boolean) ->
                   implode("",
                      map(\ ip::(Integer, Integer) ->
                            let rnum::String =
                                toString(ip.1 - p.1)
                            in
                              " apply IH" ++ (if ip.2 == 0 then ""
                                              else toString(ip.2)) ++
                                 " to R" ++ rnum ++ "."
                            end,
                          p.2)) ++ " search.",
                 l)),
        clauseInfo);
  local dropPAfter::String =
      if length(rels) == 1 then ""
      else "Split " ++ jointDropPName ++ " as " ++
           implode(", ", map((.abella_pp),
                         map(dropP_name, map(fst, rels)))) ++ ".\n";
  local dropPFull::String =
      "Theorem " ++ jointDropPName ++ " : " ++
          jointDropPStmt.abella_pp ++
          ".\n" ++ dropPProofStart ++
      implode("\n ", dropPProofs) ++ "\n" ++
      dropPAfter;

  local dropP_abella::IOVal<String> =
      sendBlockToAbella(dropPFull, top.liveAbella, top.runAbella,
                        top.configuration);



  top.outgoingMods = dropProjRel(top.incomingMods, map(fst, rels));

  local displayNames::String =
      implode(", ", map(justShow, map((.pp), map(fst, rels))));
  top.composedCmds =
      "/*Start Proj_Rel for " ++ displayNames ++ "*/\n" ++
      dropPFull ++ "\n" ++
      "/*End Proj_Rel for " ++ displayNames ++ "*/\n\n\n";

  top.newThms = flatMap(\ l -> l, lemmaStatements);
}





----------------------------------------------------------------------
-- Helper functions
----------------------------------------------------------------------

--update a module in the list with the update function, returning the
--   produced string
--does not change the order of modules, just updates one
function updateMod
([(QName, DecCmds)], String) ::= mods::[(QName, DecCmds)] mod::QName
                                 update::((DecCmds, String) ::= DecCmds)
{
  return case mods of
         | [] -> error("Module not in module map")
         | (q, c)::rest when q == ^mod ->
           let p::(DecCmds, String) = update(c)
           in
             ((q, p.1)::rest, p.2)
           end
         | (q, c)::rest ->
           let p::([(QName, DecCmds)], String) =
               updateMod(rest, ^mod, update)
           in
             ((q, c)::p.1, p.2)
           end
         end;
}


--drop the first top command in a sequence of commands, including its
--   proof if it has one
--assumes the commands start with a top command
function dropFirstTopCommand
DecCmds ::= c::DecCmds
{
  return
      case c of
      | addRunCommands(a, r) -> dropFirstTopCommand_help(r)
      | emptyRunCommands() -> error("dropFirstTopCommand(empty)")
      end;
}
function dropFirstTopCommand_help
DecCmds ::= c::DecCmds
{
  return case c of
         | addRunCommands(anyTopCommand(t), r) -> c
         | addRunCommands(_, r) ->
           dropFirstTopCommand_help(r)
         | emptyRunCommands() -> c
         end;
}


--get the next proof, dropping it from the cmds
--assumes it starts with one top command
function getProof
(DecCmds, String) ::= c::DecCmds
{
  return
      case c of
      | addRunCommands(a, r) -> getProof_help(r)
      | emptyRunCommands() -> error("getProof(empty)")
      end;
}
function getProof_help
(DecCmds, String) ::= c::DecCmds
{
  return case c of
         | addRunCommands(anyTopCommand(t), r) -> (c, "")
         | addRunCommands(anyProofCommand(p), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
           let f::[ProofCommand] = p.toAbella
           in
             (rest.1, implode("", map((.abella_pp), f)) ++ rest.2)
           end end
         | addRunCommands(anyNoOpCommand(n), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
             (rest.1, n.full.abella_pp ++ rest.2)
           end
         | addRunCommands(anyParseFailure(e), r) ->
           error("How did this get here?")
         | emptyRunCommands() -> (c, "")
         end;
}


--get all the modules where thms is the first thing
function getAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, c)::getAllOccurrences(r, thms)
           | _ -> getAllOccurrences(r, thms)
           end
         end;
}


--drop the declaration and proof of thms in every module starting with them
function dropAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, dropFirstTopCommand(c))::dropAllOccurrences(r, thms)
           | addRunCommands(a, _) ->
             (q, c)::dropAllOccurrences(r, thms)
           | emptyRunCommands() ->
             (q, c)::dropAllOccurrences(r, thms)
           end
         end;
}
--same, but for Ext_Ind and Prove_Ext_Ind
function dropExtInd
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] rels::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesRels(rels) ->
             (q, dropFirstTopCommand(c))::dropExtInd(r, rels)
           | addRunCommands(a, _) ->
             (q, c)::dropExtInd(r, rels)
           | emptyRunCommands() ->
             (q, c)::dropExtInd(r, rels)
           end
         end;
}
--
function dropExtSize
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] rels::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesRels(rels) ->
             (q, dropFirstTopCommand(c))::dropExtSize(r, rels)
           | addRunCommands(a, _) ->
             (q, c)::dropExtSize(r, rels)
           | emptyRunCommands() ->
             (q, c)::dropExtSize(r, rels)
           end
         end;
}
--
function dropProjRel
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] rels::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesRels(rels) ->
             (q, dropFirstTopCommand(c))::dropProjRel(r, rels)
           | addRunCommands(a, _) ->
             (q, c)::dropProjRel(r, rels)
           | emptyRunCommands() ->
             (q, c)::dropProjRel(r, rels)
           end
         end;
}

--get the information about the commands for the proof of thms
--[(module, [(state before command, toAbella cmds)])]
function getThmProofSteps
[(QName, [(ProofState, [AnyCommand])])] ::=
   mods::[(QName, DecCmds)] thms::[QName]
{
  return
      case mods of
      | [] -> []
      | (q, c)::r ->
        case c of
        | addRunCommands(anyTopCommand(t), rc)
          when t.matchesNames(thms) ->
          (q, getProofSteps(rc))::getThmProofSteps(r, thms)
        | _ -> getThmProofSteps(r, thms)
        end
      end;
}

--get the information about the commands for the proof of Ext_Ind for
--   the given rels
--[(module, [(state before command, toAbella cmds)])]
function getExtIndProofSteps
[(QName, [(ProofState, [AnyCommand])])] ::=
   mods::[(QName, DecCmds)] rels::[QName]
{
  return
      case mods of
      | [] -> []
      | (q, c)::r ->
        case c of
        | addRunCommands(anyTopCommand(t), rc)
          when t.matchesRels(rels) ->
          (q, getProofSteps(rc))::getExtIndProofSteps(r, rels)
        | addRunCommands(anyTopCommand(t), rc) ->
          (q, getProofSteps(rc))::getExtIndProofSteps(r, rels)
        | _ -> getExtIndProofSteps(r, rels)
        end
      end;
}


--clear out all the non-proof things at the front of files
function dropNonProof
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)]
{
  return case mods of
         | [] -> []
         | (q, c)::r -> (q, dropNonProof_oneMod(c))::dropNonProof(r)
         end;
}
function dropNonProof_oneMod
DecCmds ::= c::DecCmds
{
  return case c of
         | addRunCommands(anyTopCommand(t), r) when t.isNotProof ->
           dropNonProof_oneMod(dropFirstTopCommand(c))
         | addRunCommands(_, _) -> c
         | emptyRunCommands() -> c
         end;
}


--get the information about the commands for the rest of the proof
--assumes the TopCommand has already been dropped
--[(state before command, toAbella cmds)]
function getProofSteps
[(ProofState, [AnyCommand])] ::= cmds::DecCmds
{
  return
      case cmds of
      | addRunCommands(anyTopCommand(_), _) -> []
      | addRunCommands(c, rest) ->
        (cmds.proverState.state, c.toAbella)::getProofSteps(rest)
      | emptyRunCommands() -> []
      end;
}


--split into groups for goals 1, 2, 3, ...
--e.g. [[1.1, 1.1, 1.2, 1], [2, 2.1, 2.2, 2.2.1, ...], ...]
--assumes they are in order, as they really should be
function splitAtTopGoals
[[(ProofState, [AnyCommand])]] ::= cmds::[(ProofState, [AnyCommand])]
{
  return groupBy(\ p1::(ProofState, [AnyCommand])
                   p2::(ProofState, [AnyCommand]) ->
                   subgoalTopNum(p1.1.currentSubgoal) ==
                   subgoalTopNum(p2.1.currentSubgoal),
                 cmds);
}

--split into groups for all different subgoals
--e.g. [[1.1, 1.1], [1.2], [1], [2], [2.1], [2.2], [2.2.1], ...]
--assumes they are in order, as they really should be
function splitAtAllGoals
[[(ProofState, [AnyCommand])]] ::= cmds::[(ProofState, [AnyCommand])]
{
  return groupBy(\ p1::(ProofState, [AnyCommand])
                   p2::(ProofState, [AnyCommand]) ->
                   p1.1.currentSubgoal == p2.1.currentSubgoal,
                 cmds);
}

--group a list of states and commands into groups with the same first
--   n digits in the subgoal
function groupGoals
[[(ProofState, [AnyCommand])]] ::= cmds::[(ProofState, [AnyCommand])]
                                   n::Integer
{
  return groupBy(\ p1::(ProofState, [AnyCommand])
                   p2::(ProofState, [AnyCommand]) ->
                    take(n, p1.1.currentSubgoal) ==
                    take(n, p2.1.currentSubgoal),
                 cmds);
}


--join the given proofs into one
--outer list is grouped by module, each module has proofs for related thms
--e.g. [ [mod 1 thm a, mod 1 thm b], [mod 2 thm a, mod 2 thm b], ... ]
function joinProofGroups
String ::= prfs::[(QName, [String])]
{
  return case prfs of
         | [] -> ""
         | _::_ ->
           implode("\n",
              filterMap(\ l::(QName, [String]) ->
                          case l.2 of
                          | h::_ -> just(h)
                          | [] -> nothing()
                          end,
                  prfs)) ++ "\n" ++
           joinProofGroups(
              filterMap(\ l::(QName, [String]) ->
                          case l.2 of
                          | _::t -> just((l.1, t))
                          | [] -> nothing()
                          end,
                        prfs))
         end;
}





--make the appropriate premise into the R_P version
inherited attribute makeProjRel::String occurs on ExtBody;
synthesized attribute projRelMade::ExtBody occurs on ExtBody;

aspect production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.projRelMade =
      error("Should not access endExtBody.projRelMade");
}


aspect production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  rest.makeProjRel = top.makeProjRel;
  top.projRelMade =
      if label == top.makeProjRel
      then case m of
           | relationMetaterm(q, a, r) ->
             addLabelExtBody(label, projRelMetaterm(^q, ^a, ^r), ^rest)
           | _ -> error("Should not access projRelMade")
           end
      else addLabelExtBody(label, ^m, rest.projRelMade);
}


aspect production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  rest.makeProjRel = top.makeProjRel;
  top.projRelMade = addBasicExtBody(^m, rest.projRelMade);
}





{-
  Why an attribute pointing to a function instead of a set of
  attributes?  We're accessing this on decorated trees.  We cannot
  redecorate them to give them inherited attributes with the original
  map, so we use the functions to handle the actual work.
-}
--checks whether the given names are part of this one
synthesized attribute matchesNames::(Boolean ::= [QName])
   occurs on TopCommand;
--checks whether the given relations are part of this ExtInd
synthesized attribute matchesRels::(Boolean ::= [QName])
   occurs on TopCommand;

--false if a proof element, true otherwise
synthesized attribute isNotProof::Boolean occurs on TopCommand;

aspect default production
top::TopCommand ::=
{
  top.matchesRels = \ _ -> false;
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.matchesNames =
      \ l::[QName] ->
        !null(intersect(l, map(fst, thms.provingTheorems)));

  top.isNotProof = false;
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.matchesNames =
      \ l::[QName] -> !null(intersect(l, names ++ map(fst, newThms.provingTheorems)));

  top.isNotProof = false;
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.matchesNames = \ l::[QName] -> head(l) == ^fullName;

  top.isNotProof = false;
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.matchesNames = \ l::[QName] -> head(l) == ^name;

  top.isNotProof = false;
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels =
      \ l::[QName] -> !null(intersect(l, body.relations));

  top.isNotProof = false;
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels = \ l::[QName] -> !null(intersect(l, rels ++ newRels.relations));

  top.isNotProof = false;
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.matchesNames = \ l::[QName] -> false;

  local fullNames::[QName] = map(\ p::(Decorated QName with {relationEnv}, [String]) ->
                                   p.1.fullRel.name, decRels);
  top.matchesRels = \ l::[QName] -> !null(intersect(fullNames, l));

  top.isNotProof = false;
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels = \ l::[QName] -> !null(intersect(oldRels, l));

  top.isNotProof = false;
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.matchesNames = \ l::[QName] -> false;

  local fullNames::[QName] = map(\ p::(Decorated QName with {relationEnv}, [String]) ->
                                   p.1.fullRel.name, decRels);
  top.matchesRels = \ l::[QName] -> !null(intersect(fullNames, l));

  top.isNotProof = false;
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels = \ l::[QName] -> !null(intersect(oldRels, l));

  top.isNotProof = false;
}


aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.matchesNames = \ l::[QName] -> head(l) == ^fullName;

  top.isNotProof = false;
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  --won't use this for split, since that isn't distributed
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = false;
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}
