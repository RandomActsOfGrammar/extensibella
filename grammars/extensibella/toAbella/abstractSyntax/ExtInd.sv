grammar extensibella:toAbella:abstractSyntax;


abstract production extIndDeclaration
top::TopCommand ::= body::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.pp = text("Ext_Ind ") ++ ppImplode(text(";") ++ realLine(),
                                  map(\ d::Document ->
                                        docGroup(nest(9, d)),
                                      body.pps)) ++
           (if thms.len > 0
            then text(" and ") ++ ppImplode(text(", "), thms.pps)
            else text("")) ++
           (if alsos.len > 0
            then text(" also ") ++ ppImplode(text(", "), alsos.pps)
            else text("")) ++
           text(".") ++ realLine();
  top.abella_pp = "Ext_Ind " ++ body.abella_pp ++
      (if thms.len > 0 then " and " ++ thms.abella_pp else "") ++
      (if alsos.len > 0 then " also " ++ alsos.abella_pp else "") ++
      ".\n";

  top.provingTheorems = thms.provingTheorems ++ alsos.provingTheorems;
  top.provingExtInds =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            (p.1, p.2, p.3, p.4),
          body.extIndInfo);

  body.startingGoalNum =
      if body.len + thms.len + alsos.len > 1
      then [1]
      else []; --only one, so subgoals are 1, 2, ...

  local extIndName::String = "$Ext_Ind_" ++ toString(genInt());
  local fullThm::Metaterm =
      case thms.len, alsos.len of
      | 0, 0 -> body.toAbella
      | _, 0 -> andMetaterm(body.toAbella, thms.toAbella)
      | 0, _ -> andMetaterm(body.toAbella, alsos.toAbella)
      | _, _ -> andMetaterm(body.toAbella,
                andMetaterm(thms.toAbella, alsos.toAbella))
      end;
  local bodyIndNums::[[Integer]] =
      if useExtSize
      then repeat([2, 1], body.len) --acc and rel
      else repeat([1], body.len);   --just rel
  top.toAbella =
       --declare theorem
      [anyTopCommand(theoremDeclaration(toQName(extIndName), [],
                        ^fullThm))] ++
       --declare inductions
      map(\ l::[Integer] ->
            anyProofCommand(inductionTactic(noHint(), l)),
          transpose(bodyIndNums ++ thms.inductionNums ++ alsos.inductionNums)) ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          totalRenames) ++
       --split
      (if body.len + thms.len + alsos.len > 1
       then [anyProofCommand(splitTactic())]
       else []) ++
       --initial set of during commands, which is at least intros
      map(anyProofCommand, head(body.duringCommands).2);

  body.downDuringCommands = thms.duringCommands;
  top.duringCommands = tail(body.duringCommands) ++
      thms.duringCommands ++ alsos.duringCommands;

  local totalRenames::[(String, String, String)] =
      body.renamedIHs ++ thms.renamedIHs ++ alsos.renamedIHs;
  body.specialIHNames = totalRenames;
  body.expectedIHNum = 0;
  body.numMutualThms = body.len + thms.len + alsos.len;
  --
  thms.useExtInd = [];
  thms.startingGoalNum = [body.len + 1];
  thms.specialIHNames = totalRenames;
  thms.expectedIHNum = body.len;
  thms.numMutualThms = body.len + thms.len + alsos.len;
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  --
  alsos.useExtInd = [];
  alsos.startingGoalNum = [body.len + 1 + thms.len];
  alsos.specialIHNames = totalRenames;
  alsos.expectedIHNum = body.len + thms.len;
  alsos.numMutualThms = body.len + thms.len + alsos.len;
  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];

  local fullRelInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                       [String], RelationEnvItem)] =
      zipWith(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String])
                e::RelationEnvItem ->
                (e.name, p.2, p.3, p.4, p.5, e),
              body.extIndInfo, body.relationEnvItems);

  --whether or not to use ExtSize for the proof, or just the relation
  local useExtSize::Boolean =
      case fullRelInfo of
      | [] -> true
      | (q, _, _, _, _)::rest ->
        case findExtSizeGroup(q, top.proverState) of
        | nothing() -> false
        | just(g) -> subset(map(fst, rest), g)
        end
      end;
  body.useExtSize = useExtSize;

  top.newTheorems = addPLemmas;
  top.afterCommands =
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [],
                    decorate p.2 with {
                      typeEnv = top.typeEnv;
                      relationEnv = top.relationEnv;
                      constructorEnv = top.constructorEnv;
                      boundNames = [];
                    }.toAbella)),
                 anyProofCommand(skipTactic())],
              addPLemmas ++ thms.provingTheorems ++
              alsos.provingTheorems);

  local addPLemmas::[(QName, Metaterm)] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList,
                [String], RelationEnvItem) ->
            buildExtIndLemma(p.1, p.2, p.3, p.4),
          fullRelInfo);

  --Check each relation occurs at most once
  top.toAbellaMsgs <- --([duplicated], [seen])
      let split::([QName], [QName]) =
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if contains(q, rest.2) && !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), body.relations)
      in
        map(\ q::QName ->
              errorMsg("Duplicate definitions of extension " ++
                 "induction for relation " ++ justShow(q.pp)), split.1)
      end;
  --Check no relation has a pre-existing ExtInd
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                case findExtIndGroup(q, top.proverState) of
                | just(_) ->
                  [errorMsg("Pre-existing Ext Ind for " ++
                      justShow(q.pp) ++ "; cannot redefine it")]
                | nothing() -> []
                end,
              body.relations);
  --Check all the relations have R_P declared together
  top.toAbellaMsgs <-
      case body.extIndInfo of
      | [] ->
        [errorMsg("Must have some relations for Ext Ind declaration")]
      | (q, _, _, _)::rest ->
        case findProjRelGroup(q, top.proverState) of
        | nothing() -> [errorMsg("No definition of Proj Rel for " ++
                           "all relations in Ext Ind")]
        | just(g) ->
          if subset(map(fst, rest), g)
          then [] --everything is included
          else [errorMsg("No definition of Proj Rel for all " ++
                   "relations in Ext Ind")]
        end
      end;
  --Check if the relations have ExtSize and have it together
  --Not an error, but something possibly unintended, so warn
  top.toAbellaMsgs <-
      if useExtSize
      then []
      else [warningMsg("No definition of Ext Size for all " ++
               "relations in Ext Ind; defaulting to proving " ++
               "Ext Ind without Ext Size")];

  {-
    Cannot use Ext_Ind for induction for properties mutual with
    proving Ext_Ind because we need to use Ext_Ind for *all* mutual
    properties, and we cannot do that when proving it is valid.  Thus
    mutual properties need to have new, non-imported key relations.
  -}
  --need extInd for all if any relations are imported
  local importedKeyRels::[QName] =
      filter(\ r::QName -> !sameModule(top.currentModule, r),
             thms.keyRels);
  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else [errorMsg("Theorems declared mutually with Ext_Ind must " ++
               "use new key relations; found imported key relations " ++
               implode(", ",
                  map(justShow, map((.pp), nub(importedKeyRels)))))];

  --check for naming IH's the same thing
  top.toAbellaMsgs <-
      foldl(\ rest::([(String, String)], [Message])
              p::(String, String, String) ->
              case lookup(p.2, rest.1) of
              | just(thm) ->
                (rest.1, errorMsg("IH name " ++ p.2 ++
                            " already used by " ++ thm)::rest.2)
              | nothing() -> ((p.2, p.3)::rest.1, rest.2)
              end, ([], []), totalRenames).2;

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
      case nub(thms.numsInductions ++ alsos.numsInductions ++
               if useExtSize then [2] else [1]) of
      | [_] -> [] --all are the same
      | _ -> --at least two different numbers of inductions
        [errorMsg("Not all mutual theorems declare the same number" ++
            " of inductions; expected " ++ if useExtSize
                                           then "2" else "1")]
      end;

  top.is_nonextensible = false;
}


nonterminal ExtIndBody with
   pps, abella_pp,
   len,
   proverState,
   toAbella<Metaterm>, toAbellaMsgs,
   useExtSize,
   downDuringCommands, duringCommands, startingGoalNum, nextGoalNum,
   expectedIHNum, nextIHNum, renamedIHs, specialIHNames,
   numMutualThms,
   relations, extIndInfo, relationEnvItems,
   currentModule, typeEnv, constructorEnv, relationEnv;
propagate constructorEnv, relationEnv, typeEnv, currentModule,
          toAbellaMsgs, useExtSize, proverState, numMutualThms,
          specialIHNames on ExtIndBody;

synthesized attribute relations::[QName];
                --[(rel, args, total bound vars, premises, IH names)]
synthesized attribute extIndInfo::[(QName, [String], Bindings,
                                    ExtIndPremiseList, [String])];
synthesized attribute relationEnvItems::[RelationEnvItem];
--thread commands around, since we might need to combine them
inherited attribute downDuringCommands::[(SubgoalNum, [ProofCommand])];
--whether to use ExtSize in thm statement, or just relation itself
inherited attribute useExtSize::Boolean;
--thread expectedIHNum through branching with this
synthesized attribute nextIHNum::Integer;

abstract production branchExtIndBody
top::ExtIndBody ::= e1::ExtIndBody e2::ExtIndBody
{
  top.pps = e1.pps ++ e2.pps;
  top.abella_pp = if e1.len == 0
                  then e2.abella_pp
                  else if e2.len == 0
                  then e1.abella_pp
                  else e1.abella_pp ++ ";\n        " ++ e2.abella_pp;

  top.len = e1.len + e2.len;

  top.relations = e1.relations ++ e2.relations;

  top.extIndInfo = e1.extIndInfo ++ e2.extIndInfo;

  top.relationEnvItems = e1.relationEnvItems ++ e2.relationEnvItems;

  e1.startingGoalNum = top.startingGoalNum;
  e2.startingGoalNum = e1.nextGoalNum;
  top.nextGoalNum = e2.nextGoalNum;

  e1.expectedIHNum = top.expectedIHNum;
  e2.expectedIHNum = e1.nextIHNum;
  top.nextIHNum = e2.nextIHNum;

  top.renamedIHs = e1.renamedIHs ++ e2.renamedIHs;

  e2.downDuringCommands = top.downDuringCommands;
  e1.downDuringCommands = e2.duringCommands;
  top.duringCommands = e1.duringCommands;

  top.toAbella = if e1.len == 0
                 then e2.toAbella
                 else if e2.len == 0
                 then e1.toAbella
                 else andMetaterm(e1.toAbella, e2.toAbella);
}


abstract production emptyExtIndBody
top::ExtIndBody ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.len = 0;

  top.relations = [];
  top.extIndInfo = [];
  top.relationEnvItems = [];

  top.nextGoalNum = top.startingGoalNum;
  top.nextIHNum = top.expectedIHNum;
  top.renamedIHs = [];
  top.duringCommands = top.downDuringCommands;
  top.toAbella = error("Should not access (emptyExtIndBody.toAbella)");
}


abstract production oneExtIndBody
top::ExtIndBody ::= boundVars::Bindings rel::QName relArgs::[String]
                    premises::ExtIndPremiseList ihNames::[String]
{
  top.pps = [text("forall ") ++ ppImplode(text(" "), boundVars.pps) ++
             text(", ") ++
             ppImplode(text(" "), rel.pp::map(text, relArgs)) ++
             (if premises.len > 0
              then ( text(" with") ++ line() ++
                     nest(3, ppImplode(text(", "), premises.pps)) )
              else text("")) ++
             (if length(ihNames) == 0
              then text("")
              else text(" as ") ++
                   ppImplode(text(", "), map(text, ihNames)))];
  top.abella_pp =
      "forall " ++ boundVars.abella_pp ++ ", " ++
      implode(" ", rel.abella_pp::relArgs) ++
      (if premises.len > 0
       then (" with " ++ premises.abella_pp)
       else "") ++
      (if length(ihNames) > 0
       then " as " ++ implode(", ", ihNames)
       else "");

  top.len = 1;

  local fullRel::RelationEnvItem = rel.fullRel;

  premises.boundNames = boundVars.usedNames ++ relArgs;

  top.relations = if rel.relFound then [fullRel.name] else [];

  top.extIndInfo = [(if rel.relFound then fullRel.name else ^rel,
                     relArgs, ^boundVars, premises.full, ihNames)];

  top.relationEnvItems = if rel.relFound then [fullRel] else [];

  top.nextGoalNum = [head(top.startingGoalNum) + 1];

  top.nextIHNum = top.expectedIHNum + 1;

  --only two can be used legitimately, so hardcode that here
  top.renamedIHs =
      let thmName::String = "relation " ++ rel.shortName
      in
        case ihNames of
        | [ih] ->
          [(numToIHName(top.expectedIHNum), ih, thmName)]
        | [ih1, ih2] ->
          [(numToIHName(top.expectedIHNum), ih1, thmName),
           (numToIHName(top.expectedIHNum + top.numMutualThms),
            ih2, thmName)]
        | _ -> [] --too many or none
        end
      end;

  local givenLabels::[String] = filterMap(fst, premises.toList);
  local relLabel::String = freshName("R", givenLabels);
  local introsNames::[String] =
      [relLabel] ++
      (if top.useExtSize then [freshName("Acc", givenLabels)]
                         else []) ++
      map(fromMaybe("_", _), map(fst, premises.toList)); 

  --[(last element of subgoal number, whether to prove it)]
  local expectedSubgoals::[(Integer, Boolean)] =
      if !rel.relFound
      then [] --no cases without known relation
      else foldl(\ thusFar::(Integer, [(Integer, Boolean)])
                   now::([Term], Maybe<Metaterm>) ->
                   let pc::Term = rulePrimaryComponent(now, fullRel)
                   in
                   let pcMod::QName =
                       if decorate pc with {
                             relationEnv = top.relationEnv;
                             constructorEnv = top.constructorEnv;
                          }.isStructured
                       then pc.headConstructor.moduleName
                       else fullRel.name.moduleName
                   in
                   let prems::[Metaterm] = splitRulePrems(now.2)
                   in
                   --we know the rule's conclusion unifies with the
                   --derivation in the property because that is just
                   --variables, so we only need to check the rule's
                   --premises
                   let unifySides::([Term], [Term]) =
                       premiseUnificationPairs(prems)
                   in
                   let unifies::Boolean =
                       unifyTermsSuccess(unifySides.1, unifySides.2)
                   in
                   let shouldProve::Boolean =
                        --prove everything known in introducing module
                       (top.currentModule == fullRel.name.moduleName ||
                        --prove only new things in other modules
                        pcMod == top.currentModule) &&
                       --but never prove for unknown K, which is only
                       --   present as holders for other relations
                       !pc.isUnknownTermK
                   in
                     if unifies --rule isn't cleared automatically by Abella
                     then (thusFar.1 + 1,
                           thusFar.2 ++ [(thusFar.1, shouldProve)])
                     else thusFar --cleared automatically
                   end end end end end end,
                 (1, []), fullRel.defsList).2;
  --group consecutive skips
  local groupedExpectedSubgoals::[[(Integer, Boolean)]] =
      groupBy(\ p1::(Integer, Boolean) p2::(Integer, Boolean) ->
                p1.2 == p2.2, expectedSubgoals);
  --last element of subgoal and skips needed
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
      map(\ p::(Integer, [ProofCommand]) ->
            (top.startingGoalNum ++ [p.1], p.2),
          subgoalDurings);
  --combine with the first one of downDuringCommands if we skip the
  --   last thing here
  local combinedCommands::[(SubgoalNum, [ProofCommand])] =
      if !null(expectedSubgoals) && !last(expectedSubgoals).2 &&
         !null(top.downDuringCommands) && !null(subgoalDuringCommands)
      then let lastSubgoal::(SubgoalNum, [ProofCommand]) =
               last(subgoalDuringCommands)
           in
             init(subgoalDuringCommands) ++
             [(lastSubgoal.1,
               lastSubgoal.2 ++ head(top.downDuringCommands).2)] ++
             tail(top.downDuringCommands)
           end
      else subgoalDuringCommands ++ top.downDuringCommands;

  top.duringCommands =
      [(top.startingGoalNum,
        [introsTactic(introsNames),
         caseTactic(nameHint(relLabel), relLabel, true)] ++
        --add first skips if they happen right away
        (if !null(combinedCommands) && !null(subgoalDurings) &&
            head(subgoalDurings).1 == 1
         then head(combinedCommands).2
         else []))] ++
      --add rest of during commands, dropping head if we took it
      if !null(combinedCommands) && !null(subgoalDurings) &&
         head(subgoalDurings).1 == 1
      then tail(combinedCommands)
      else combinedCommands;

  top.toAbella = buildExtIndThm(boundVars.toAbella, rel.fullRel.name,
                    relArgs, premises.toAbella, top.useExtSize);

  --Check relation is an extensible relation from this module
  top.toAbellaMsgs <-
      if !rel.relFound
      then rel.relErrors
      else if !sameModule(top.currentModule, rel.fullRel.name)
      then [errorMsg("Cannot declare extension induction for " ++
                     "relation " ++ justShow(rel.fullRel.name.pp) ++
                     " not declared in this module")]
      else if !rel.fullRel.isExtensible
      then [errorMsg("Cannot declare extension induction for " ++
               " non-extensible relation " ++
               justShow(rel.fullRel.name.pp))]
      else [];
  --Check the arguments to the relation are variables (capitalized)
  top.toAbellaMsgs <-
      flatMap(\ x::String ->
                if isCapitalized(x) then []
                else [errorMsg("Arguments to relation " ++
                         justShow(rel.pp) ++
                         " must be capitalized, but found " ++ x)],
              relArgs);
  --Check the arguments to the relation are unique
  top.toAbellaMsgs <-
      if length(relArgs) != length(nub(relArgs))
      then [errorMsg("Arguments to " ++ justShow(rel.pp) ++
               " must be unique variables; found duplicates")]
      else [];
  --Check names given to premises are unique
  top.toAbellaMsgs <-
      foldr(\ x::String rest::([String], [Message]) ->
              if contains(x, rest.1)
              then (rest.1,
                    errorMsg("Repeated premise name " ++ x ++
                       " for relation " ++ justShow(rel.pp))::rest.2)
              else (x::rest.1, rest.2),
            ([], []), filterMap(fst, premises.toList)).2;
  --Check the number of IH names is valid
  top.toAbellaMsgs <-
      case ihNames of
      | [] -> [] --always fine not to name them
      | [ih] -> [] --fine to name just one
      | [ih1, ih2] ->
        if top.useExtSize
        then [] --there are two inductions, so valid
        else [errorMsg("Too many IH names for relation " ++
                 justShow(rel.pp) ++ "; not using Ext_Size, so " ++
                 "there is only one induction")]
      | l -> [errorMsg("Too many IH names for relation " ++
                 justShow(rel.pp) ++ "; expected at most " ++
                 (if top.useExtSize then "2" else "1") ++
                 " but found " ++ toString(length(l)))]
      end;
  --Check the IH names do not have conflict-causing shapes
  top.toAbellaMsgs <-
      flatMap(\ name::String ->
                if name == "H" ||
                   (startsWith("H", name) &&
                    isDigit(substring(1, length(name), name)))
                then [errorMsg("Cannot declare label of form \"H<num>\"")]
                else if matches_IH_form(name)
                then [errorMsg("Cannot declare label of form \"IH<num>\"")]
                else [],
              ihNames);

  --Check it is well-typed
  top.toAbellaMsgs <-
      case unifyRelArgs.upSubst of
      | right(_) -> []
      | left(_) ->
        --given the messages are not terribly useful:
        [errorMsg("Type error in Ext_Ind for " ++ justShow(rel.pp))]
      end;

  --typing
  local relArgTys::[(String, Type)] =
      map(\ x::String ->
            (x, varType("__RelArg" ++ toString(genInt()))),
          relArgs);
  local unifyRelArgs::TypeUnify =
      if rel.relFound && rel.fullRel.isExtensible
      then typeUnify(
              freshenType(
                 foldr1(arrowType, rel.fullRel.types.toList)),
              foldr(arrowType, propType, map(snd, relArgTys)))
      else blankUnify();
  premises.downVarTys = relArgTys ++
      map(\ p::(String, MaybeType) ->
            (p.1,
             case p.2 of
             | justType(t) -> ^t
             | nothingType() -> varType("__X" ++ toString(genInt()))
             end), boundVars.toList);
  premises.downSubst = emptySubst();
  unifyRelArgs.downSubst = premises.upSubst;
}

function buildExtIndThm
Metaterm ::= boundVars::Bindings rel::QName relArgs::[String]
             premises::[(Maybe<String>, Metaterm)] useExtSize::Boolean
{
  local args::[Term] =
      map(\ x::String -> nameTerm(toQName(x), nothingType()), relArgs);
  local n::String = freshName("N", boundVars.usedNames);
  local relPrem::Metaterm =
      relationMetaterm(^rel,
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
  local acc::Metaterm =
      relationMetaterm(toQName("extensibella:stdLib:acc"),
         toTermList([nameTerm(toQName(n), nothingType())]),
         emptyRestriction());
  local conc::Metaterm =
      relationMetaterm(projRelQName(rel.sub), toTermList(args),
                       emptyRestriction());
  return
      bindingMetaterm(forallBinder(),
         if useExtSize
         then addBindings(n, nothingType(), ^boundVars)
         else ^boundVars,
         foldr(impliesMetaterm, ^conc,
               if useExtSize
               then ^extSize::^acc::map(snd, premises)
               else ^relPrem::map(snd, premises)));
}


nonterminal ExtIndPremiseList with
   pps, abella_pp,
   toList<(Maybe<String>, Metaterm)>, len,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames,
   specialIHNames,
   upSubst, downSubst, downVarTys, tyVars,
   toAbella<[(Maybe<String>, Metaterm)]>, toAbellaMsgs, proverState;
propagate typeEnv, constructorEnv, relationEnv, boundNames, downVarTys,
          tyVars, usedNames, proverState, toAbellaMsgs, specialIHNames
   on ExtIndPremiseList;

abstract production emptyExtIndPremiseList
top::ExtIndPremiseList ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.upSubst = top.downSubst;

  top.toAbella = [];
}


abstract production addNameExtIndPremiseList
top::ExtIndPremiseList ::= name::String m::Metaterm
                           rest::ExtIndPremiseList
{
  top.pps = (text(name ++ " : ") ++ nest(3, m.pp))::rest.pps;
  top.abella_pp = name ++ " : " ++ m.abella_pp ++
                  if rest.abella_pp == "" then ""
                  else ", " ++ rest.abella_pp;

  top.toList = (just(name), ^m)::rest.toList;
  top.len = 1 + rest.len;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  top.toAbella = (just(name), m.toAbella)::rest.toAbella;

  --labels of the form H<num> cause Abella errors
  top.toAbellaMsgs <-
      if startsWith("H", name) &&
         isDigit(substring(1, length(name), name))
      then [errorMsg("Cannot declare label of form \"H<num>\"")]
      else [];
  --labels of the form IH<num> may interfere with inductive hypotheses
  top.toAbellaMsgs <-
      if matches_IH_form(name)
      then [errorMsg("Cannot declare label of form \"IH<num>\"")]
      else [];
  --cannot have names of other IH's
  top.toAbellaMsgs <-
      let whichThm::Maybe<String> =
          lookup(name, map(snd, top.specialIHNames))
      in
        case whichThm of
        | nothing() -> []
        | just(thm) ->
          [errorMsg("Label " ++ name ++ " is the name of an IH " ++
                    "for " ++ thm ++ " and cannot be used as a " ++
                    "premise label")]
        end
      end;
}


abstract production addExtIndPremiseList
top::ExtIndPremiseList ::= m::Metaterm rest::ExtIndPremiseList
{
  top.pps = (m.pp)::rest.pps;
  top.abella_pp = m.abella_pp ++ if rest.abella_pp == "" then ""
                                 else ", " ++ rest.abella_pp;

  top.toList = (nothing(), ^m)::rest.toList;
  top.len = 1 + rest.len;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  top.toAbella = (nothing(), m.toAbella)::rest.toAbella;
}


abstract production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.pp = text("Prove_Ext_Ind ") ++ ppImplode(text(",") ++ line(),
                                        map((.pp), rels)) ++
           (if length(oldThms) > 0
            then realLine() ++ text("and_thms ") ++
                 ppImplode(text(",") ++ line(),
                    map(\ d::Document -> docGroup(nest(8, d)),
                        map((.pp), oldThms)))
            else text("")) ++
           (if newRels.len > 0
            then realLine() ++ text("with ") ++
                 ppImplode(text(";") ++ realLine(),
                    map(\ d::Document -> docGroup(nest(9, d)),
                        newRels.pps))
            else text("")) ++
           text(".") ++ realLine();
  top.abella_pp =
      error("proveExtInd.abella_pp should not be accessed");

  --check for the expected obligation
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | extIndElement(relInfo, importedThms, oldAlsos, _)::_ ->
        let expectedRelNames::[QName] = map(fst, relInfo)
        in
        let expectedThmNames::[QName] = map(fst, importedThms)
        in
          if !subset(rels, expectedRelNames) &&
             !subset(expectedRelNames, rels)
          then [errorMsg("Expected ExtInd obligation " ++
                   " " ++ implode(", ",
                             map(justShow, map((.pp), expectedRelNames))) ++
                   if length(importedThms) > 0
                   then " and_thms " ++
                        implode(", ",
                           map(justShow, map((.pp), map(fst, importedThms))))
                   else "")]
          else (if setEq(rels, expectedRelNames)
                then []
                else if subset(rels, expectedRelNames)
                then let missing::[QName] = removeAll(rels, expectedRelNames)
                     in
                       [errorMsg("Missing relation" ++
                           (if length(missing) == 1 then " " else "s ") ++
                           implode(", ", map(justShow,
                              map((.pp), removeAll(rels, expectedRelNames)))))]
                     end
                else --subset(expectedRelNames, rels)
                     [errorMsg("Too many relations; should not have " ++
                         implode(", ", map(justShow,
                            map((.pp), removeAll(expectedRelNames, rels)))))]) ++
                --thm errors
                if setEq(oldThms, expectedThmNames)
                then []
                else if subset(oldThms, expectedThmNames)
                then let missing::[QName] = removeAll(rels, expectedThmNames)
                     in
                       [errorMsg("Missing imported theorem" ++
                           (if length(missing) == 1 then " " else "s ") ++
                           implode(", ", map(justShow,
                              map((.pp), removeAll(oldThms, expectedThmNames)))))]
                     end
                else if subset(expectedThmNames, oldThms)
                then [errorMsg("Too many imported theorems; should not have " ++
                         implode(", ", map(justShow,
                            map((.pp), removeAll(expectedThmNames, oldThms)))))]
                else [errorMsg("Expected imported theorem" ++
                         (if length(importedThms) > 1 then "s " else " ") ++
                         implode(", ",
                            map(justShow, map((.pp), map(fst, importedThms)))))]
        end end
      | l -> [wrongObligation(l)]
      end;
  --Check each relation occurs at most once
  top.toAbellaMsgs <- --([duplicated], [seen])
      let split::([QName], [QName]) =
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if contains(q, rest.2) && !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), newRels.relations)
      in
        map(\ q::QName ->
              errorMsg("Duplicate definitions of extension " ++
                 "induction for relation " ++ justShow(q.pp)), split.1)
      end;
  --Check no relation has a pre-existing ExtInd
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                case findExtIndGroup(q, top.proverState) of
                | just(_) ->
                  [errorMsg("Pre-existing ExtInd for " ++
                      justShow(q.pp) ++ "; cannot redefine it")]
                | nothing() -> []
                end,
              newRels.relations);
  --Check all the relations have R_P declared together
  top.toAbellaMsgs <-
      if !obligationsFound
      then []
      else case head(top.proverState.remainingObligations) of
           | extIndElement(_, _, _, _) ->
             case fullRelInfo of
             | (q, _, _, _)::rest ->
               case findProjRelGroup(q, top.proverState) of
               | nothing() -> [errorMsg("No definition of Proj Rel" ++
                                  " for all relations in Ext Ind")]
               | just(g) ->
                 if subset(map(fst, rest), g)
                 then [] --everything is included
                 else [errorMsg("No definition of Proj Rel for all" ++
                          " relations in Ext Ind")]
               end
             | [] -> [] --not actually possible
             end
           | _ -> [] --error given elsewhere
           end;
  --Check if the relations have ExtSize and have it together
  --Not an error, but something possibly unintended, so warn
  top.toAbellaMsgs <-
      if !obligationsFound
      then []
      else if useExtSize --existing ones use Ext Size
      then case fullRelInfo of
           | (q, _, _, _, _)::rest ->
             case findExtSizeGroup(q, top.proverState) of
             | just(g) when !subset(map(fst, rest), g) ->
               --found group and it does not include all new rels
               [errorMsg("Existing relations use Ext Size for " ++
                   "proving Ext Ind; must include new relations " ++
                   "in same Ext Size declaration")]
             | _ -> []
             end
           | _ -> []
           end
      else [warningMsg("No definition of Ext Size for all " ++
               "relations in Ext Ind; defaulting to proving " ++
               "Ext Ind without Ext Size")];

  {-
    Cannot use Ext_Ind for induction for properties mutual with
    proving Ext_Ind because we need to use Ext_Ind for *all* mutual
    properties, and we cannot do that when proving it is valid.  Thus
    mutual properties need to have new, non-imported key relations.
  -}
  --need extInd for all if any relations are imported
  local importedKeyRels::[QName] =
      filter(\ r::QName -> !sameModule(top.currentModule, r),
             newThms.keyRels);
  top.toAbellaMsgs <-
      if null(importedKeyRels)
      then []
      else [errorMsg("Theorems declared mutually with Ext_Ind must " ++
               "use new key relations; found imported key relations " ++
               implode(", ",
                  map(justShow, map((.pp), nub(importedKeyRels)))))];

  --check for naming IH's the same thing
  top.toAbellaMsgs <-
      foldl(\ rest::([(String, String)], [Message])
              p::(String, String, String) ->
              case lookup(p.2, rest.1) of
              | just(thm) ->
                (rest.1, errorMsg("IH name " ++ p.2 ++
                            " already used by " ++ thm)::rest.2)
              | nothing() -> ((p.2, p.3)::rest.1, rest.2)
              end, ([], []), totalRenames).2;

  --check for naming thms the same thing
  --only check new ones because imported ones must be unique and
  --   qualified with a different module name
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
                ([], []), newThms.thmNames ++ newAlsos.thmNames).2);

  --check all use the same number of inductions
  top.toAbellaMsgs <-
      if !obligationsFound then [] else --guard
      case nub(thms.numsInductions ++ alsos.numsInductions ++
               if useExtSize then [2] else [1]) of
      | [_] -> [] --all are the same
      | _ -> --at least two different numbers of inductions
        [errorMsg("Not all mutual theorems declare the same number" ++
            " of inductions; expected " ++ if useExtSize
                                           then "2" else "1")]
      end;

  local obligationsFound::Boolean =
      case top.proverState.remainingObligations of
      | extIndElement(relInfo, _, _, _)::_ ->
        setEq(rels, map(fst, relInfo))
      | _ -> false
      end;
  local obligations::[(QName, [String], Bindings, ExtIndPremiseList,
                       [String])] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(r, _, _, _) -> r
      | _ -> error("Not possible (proveExtInd.obligations)")
      end;
  local importedThms::[(QName, Bindings, ExtBody, InductionOns)] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(_, t, _, _) -> t
      | _ -> error("Not possible (proveExtInd.importedThms)")
      end;
  local importedAlsos::[(QName, Bindings, ExtBody, InductionOns)] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(_, _, a, _) -> a
      | _ -> error("Not possible (proveExtInd.importedAlsos)")
      end;
  --This should only be accessed if there are no errors
  top.provingExtInds =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            (p.1, p.2, p.3, p.4),
          obligations ++ newRels.extIndInfo);
  top.provingTheorems =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
            --don't need the actual metaterm, only the name
            (extIndThmName(p.1), trueMetaterm()),
          obligations ++ newRels.extIndInfo) ++
      thms.provingTheorems ++ alsos.provingTheorems;

  --get the environment entry for each relation as well
  local fullRelInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                       [String], RelationEnvItem)] =
      zipWith(\ p::(QName, [String], Bindings, ExtIndPremiseList,
                    [String]) e::RelationEnvItem ->
                (e.name, p.2, p.3, p.4, p.5, e),
              body.extIndInfo, body.relationEnvItems);

  --whether or not to use ExtSize for the proof, or just the relation
  --because new ExtSize can only be declared for new relations, this
  --   matches what is done in other modules
  local useExtSize::Boolean =
      case rels of
      | [] -> true
      | q::rest ->
        case findExtSizeGroup(q, top.proverState) of
        | nothing() -> false
        | just(g) -> subset(rest, g)
        end
      end;
  body.useExtSize = useExtSize;

  local body::ExtIndBody =
      foldr(branchExtIndBody, ^newRels,
         map(\ here::(QName, [String], Bindings, ExtIndPremiseList,
                      [String]) ->
               oneExtIndBody(here.3, here.1, here.2, here.4, here.5),
             obligations));
  body.startingGoalNum =
       if body.len > 1 then [1] else [];
  body.typeEnv = top.typeEnv;
  body.relationEnv = top.relationEnv;
  body.currentModule = top.currentModule;
  body.constructorEnv = top.constructorEnv;
  body.downDuringCommands = thms.duringCommands;
  body.expectedIHNum = 0;
  body.numMutualThms = body.len + thms.len + alsos.len;

  local thms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, InductionOns) rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, rest),
            ^newThms, importedThms);
  local alsos::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, InductionOns) rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, rest),
            ^newAlsos, importedAlsos);

  local totalRenames::[(String, String, String)] =
      if obligationsFound
      then body.renamedIHs ++ thms.renamedIHs ++ alsos.renamedIHs
      else newRels.renamedIHs ++ newThms.renamedIHs ++
           newAlsos.renamedIHs;

  thms.useExtInd = [];
  thms.startingGoalNum = [body.len + 1];
  thms.specialIHNames = totalRenames;
  thms.expectedIHNum = body.len;
  thms.numMutualThms = body.len + thms.len + alsos.len;
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  thms.relationEnv = top.relationEnv;
  thms.constructorEnv = top.constructorEnv;
  thms.typeEnv = top.typeEnv;
  thms.currentModule = top.currentModule;
  --
  alsos.useExtInd = [];
  alsos.startingGoalNum = [body.len + 1 + thms.len];
  alsos.specialIHNames = totalRenames;
  alsos.expectedIHNum = body.len + thms.len;
  alsos.numMutualThms = body.len + thms.len + alsos.len;
  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];
  alsos.relationEnv = top.relationEnv;
  alsos.constructorEnv = top.constructorEnv;
  alsos.typeEnv = top.typeEnv;
  alsos.currentModule = top.currentModule;

  --decorate new things only for error checking
  newRels.numMutualThms = 0; --not accurately needed
  newRels.expectedIHNum = 0; --not accurately needed
  newRels.useExtSize = useExtSize;
  newRels.specialIHNames = totalRenames;
  --
  newThms.useExtInd = [];
  newThms.specialIHNames = totalRenames;
  newThms.shouldBeExtensible = true;
  newThms.numMutualThms = 0; --not accurately needed
  newThms.expectedIHNum = 0; --not accurately needed
  --
  newAlsos.useExtInd = [];
  newAlsos.specialIHNames = totalRenames;
  newAlsos.shouldBeExtensible = false;
  newAlsos.numMutualThms = 0; --not accurately needed
  newAlsos.expectedIHNum = 0; --not accurately needed

  top.newTheorems = addPLemmas;
  top.afterCommands =
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [],
                    decorate p.2 with {
                      typeEnv = top.typeEnv;
                      relationEnv = top.relationEnv;
                      constructorEnv = top.constructorEnv;
                      boundNames = [];
                    }.toAbella)),
                 anyProofCommand(skipTactic())],
              addPLemmas ++ thms.provingTheorems ++
              alsos.provingTheorems);

  local addPLemmas::[(QName, Metaterm)] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList,
                [String], RelationEnvItem) ->
            buildExtIndLemma(p.1, p.2, p.3, p.4),
          fullRelInfo);

  local extIndName::String = "$Ext_Ind_" ++ toString(genInt());
  local fullThm::Metaterm =
      case thms.len, alsos.len of
      | 0, 0 -> body.toAbella
      | _, 0 -> andMetaterm(body.toAbella, thms.toAbella)
      | 0, _ -> andMetaterm(body.toAbella, alsos.toAbella)
      | _, _ -> andMetaterm(body.toAbella,
                andMetaterm(thms.toAbella, alsos.toAbella))
      end;
  local bodyIndNums::[[Integer]] =
      if useExtSize
      then repeat([2, 1], body.len) --acc and rel
      else repeat([1], body.len);   --just rel
  top.toAbella =
       --declare theorem
      [anyTopCommand(theoremDeclaration(toQName(extIndName), [],
                        ^fullThm))] ++
       --declare inductions
      map(\ l::[Integer] ->
            anyProofCommand(inductionTactic(noHint(), l)),
          transpose(bodyIndNums ++ thms.inductionNums ++ alsos.inductionNums)) ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          totalRenames) ++
       --split
      (if body.len + thms.len + alsos.len > 1
       then [anyProofCommand(splitTactic())]
       else []) ++
       --initial set of during commands, which is at least intros
      map(anyProofCommand, head(body.duringCommands).2);

  top.duringCommands = tail(body.duringCommands) ++
      thms.duringCommands ++ alsos.duringCommands;

  top.is_nonextensible = false;
}



abstract production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.pp = text("Ext_Size ") ++
           ppImplode(text(",") ++ line(),
              map(\ p::(QName, [String]) ->
                    nest(9, ppImplode(text(" "), p.1.pp::map(text, p.2))),
                  rels)) ++ text(".");
  top.abella_pp =
      "Ext_Size " ++
      implode(", ",
         map(\ p::(QName, [String]) ->
               implode(" ", p.1.abella_pp::p.2), rels)) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = extSizeLemmas;

  top.newExtSizeGroup =
      foldr(\ p::(Decorated QName with {relationEnv}, [String])
              rest::Maybe<[QName]> ->
              bind(rest, \ r::[QName] ->
                           if p.1.relFound then just(p.1.fullRel.name::r)
                                           else nothing()),
            just([]), decRels);

  production decRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), rels);

  top.toAbella =
      anyTopCommand(^extSizeDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas);
  local extSizeDef::TopCommand =
      buildExtSize(map(\ q::Decorated QName with {relationEnv} ->
                         q.fullRel.name, map(fst, decRels)),
                   top.relationEnv, top.constructorEnv,
                   top.proverState.buildsOns);
  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                buildExtSizeLemmas(p.1.fullRel.name, p.2), decRels);

  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Ext Size for " ++
                          justShow(p.1.pp))]
                 else []) ++
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Ext Size " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                (if p.1.relFound &&  --len - 1 to drop prop
                    length(p.2) != p.1.fullRel.types.len - 1
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len - 1) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                p.1.relErrors ++
                if !p.1.relFound
                then []
                else (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     (if findExtSizeGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has Ext Size defined for it")]
                      else []), decRels);

  top.is_nonextensible = false;
}


abstract production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.pp = text("Add_Ext_Size ") ++
           ppImplode(text(",") ++ line(), map((.pp), oldRels)) ++
           (if null(newRels)
            then text("")
            else line() ++ text("with ") ++
                 ppImplode(text(",") ++ line(),
                    map(\ p::(QName, [String]) ->
                          nest(9, ppImplode(text(" "),
                                     p.1.pp::map(text, p.2))),
                        newRels))) ++ text(".");
  top.abella_pp =
      "Add_Ext_Size " ++
      implode(", ", map(justShow, map((.pp), oldRels))) ++
      (if null(newRels)
       then ""
       else " with " ++ implode(", ",
                           map(\ p::(QName, [String]) ->
                                 implode(" ", p.1.abella_pp::p.2),
                               newRels))) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = extSizeLemmas;

  top.newExtSizeGroup =
      bind(
         foldr(\ p::(Decorated QName with {relationEnv}, [String])
                 rest::Maybe<[QName]> ->
                 bind(rest, \ r::[QName] ->
                              if p.1.relFound then just(p.1.fullRel.name::r)
                                              else nothing()),
               just([]), decNewRels),
         \ r::[QName] -> just(oldRels ++ r));

  local decNewRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), newRels);

  top.toAbella =
      anyTopCommand(^extSizeDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas);
  local extSizeDef::TopCommand =
      buildExtSize(map(fst, obligations) ++
                   map(\ q::Decorated QName with {relationEnv} ->
                         q.fullRel.name, map(fst, decNewRels)),
                   top.relationEnv, top.constructorEnv,
                   top.proverState.buildsOns);
  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(QName, [String]) ->
                buildExtSizeLemmas(p.1, p.2),
         obligations ++
         map(\ p::(Decorated QName with {relationEnv}, [String]) ->
               (p.1.fullRel.name, p.2),
             decNewRels));

  local obligations::[(QName, [String])] =
      case head(top.proverState.remainingObligations) of
      | extSizeElement(r, _) -> r
      | _ -> error("Not possible (addExtSize.obligations)")
      end;

  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | extSizeElement(relInfo, _)::_ ->
        let expectedNames::[QName] = map(fst, relInfo)
        in
          if setEq(oldRels, expectedNames)
          then []
          else if subset(oldRels, expectedNames)
          then let missing::[QName] = removeAll(oldRels, expectedNames)
               in
                 [errorMsg("Missing relation" ++
                     (if length(missing) == 1 then " " else "s ") ++
                     implode(", ", map(justShow,
                        map((.pp), removeAll(oldRels, expectedNames)))))]
               end
          else if subset(expectedNames, oldRels)
          then [errorMsg("Too many relations; should not have " ++
                   implode(", ", map(justShow,
                      map((.pp), removeAll(expectedNames, oldRels)))))]
          else [errorMsg("Expected ExtSize addition" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ",
                             map(justShow, map((.pp), expectedNames))))]
        end
      | l -> [wrongObligation(l)]
      end;
  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Ext Size for " ++
                          justShow(p.1.pp))]
                 else []) ++
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Ext Size " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                (if p.1.relFound &&  --len - 1 to drop prop
                    length(p.2) != p.1.fullRel.types.len - 1
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                p.1.relErrors ++
                if !p.1.relFound
                then []
                else (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     (if findExtSizeGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has Ext Size defined for it")]
                      else []), decNewRels);

  top.is_nonextensible = false;
}



abstract production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.pp = text("Proj_Rel ") ++
           ppImplode(text(",") ++ line(),
              map(\ p::(QName, [String]) ->
                    nest(9, ppImplode(text(" "), p.1.pp::map(text, p.2))),
                  rels)) ++ text(".");
  top.abella_pp =
      "Proj_Rel " ++
      implode(", ",
         map(\ p::(QName, [String]) ->
               implode(" ", p.1.abella_pp::p.2), rels)) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = projRelLemmas;

  top.newProjRelGroup =
      foldr(\ p::(Decorated QName with {relationEnv}, [String])
              rest::Maybe<[QName]> ->
              bind(rest, \ r::[QName] ->
                           if p.1.relFound then just(p.1.fullRel.name::r)
                                           else nothing()),
            just([]), decRels);

  production decRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), rels);

  top.toAbella =
      anyTopCommand(^projRelDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              projRelLemmas);
  local projRelDef::TopCommand =
      buildProjRel(map(\ p::(Decorated QName with {relationEnv}, [String]) ->
                         (p.1.fullRel.name, p.2), decRels),
         top.relationEnv, top.constructorEnv, top.proverState.buildsOns);
  local projRelLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                buildProjRelLemmas(p.1.fullRel.name, p.2), decRels);

  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                --check no repeated arguments
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Proj Rel for " ++
                          justShow(p.1.pp))]
                 else []) ++
                --check arguments are capitalized
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Proj Rel " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                --check right number of arguments
                (if p.1.relFound &&  --len - 1 to drop prop
                    length(p.2) != p.1.fullRel.types.len - 1
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len - 1) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                --errors from finding relation
                p.1.relErrors ++
                --
                if !p.1.relFound
                then []
                else --new relations only
                     (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     --only one definition for it
                     (if findProjRelGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has Proj Rel defined for it")]
                      else []) ++
                     --all mutual relations included
                     (case findMutualGroup(p.1.fullRel.name,
                                           top.proverState) of
                      | just(g) ->
                        let allHere::[QName] =
                            filterMap(
                               \ p::(Decorated QName with {relationEnv}, [String]) ->
                                 if p.1.relFound
                                 then just(p.1.fullRel.name)
                                 else nothing(),
                               decRels)
                        in
                        let missing::[QName] = removeAll(allHere, g)
                        in
                          case missing of
                          | [] -> [] --none missing, so fine
                          | l -> [errorMsg("Missing relation" ++
                                     (if length(l) == 1 then " " else "s ") ++
                                     "defined mutually with " ++
                                     justShow(p.1.fullRel.name.pp) ++ ":  " ++
                                     implode(", ", map(justShow, map((.pp), l))))]
                          end
                        end end
                      | nothing() ->
                        error("Should be impossible (projRelDecl.toAbellaMsgs)")
                      end),
              decRels);

  top.is_nonextensible = false;
}


abstract production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.pp = text("Add_Proj_Rel ") ++
           ppImplode(text(",") ++ line(), map((.pp), oldRels)) ++
           (if null(newRels)
            then text("")
            else line() ++ text("with ") ++
                 ppImplode(text(",") ++ line(),
                    map(\ p::(QName, [String]) ->
                          nest(9, ppImplode(text(" "),
                                     p.1.pp::map(text, p.2))),
                        newRels))) ++ text(".");
  top.abella_pp =
      "Add_Proj_Rel " ++
      implode(", ", map(justShow, map((.pp), oldRels))) ++
      (if null(newRels)
       then ""
       else " with " ++ implode(", ",
                           map(\ p::(QName, [String]) ->
                                 implode(" ", p.1.abella_pp::p.2),
                               newRels))) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = projRelLemmas;

  top.newProjRelGroup =
      bind(
         foldr(\ p::(Decorated QName with {relationEnv}, [String])
                 rest::Maybe<[QName]> ->
                 bind(rest, \ r::[QName] ->
                              if p.1.relFound then just(p.1.fullRel.name::r)
                                              else nothing()),
               just([]), decNewRels),
         \ r::[QName] -> just(oldRels ++ r));

  local decNewRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), newRels);

  top.toAbella =
      anyTopCommand(^projRelDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              projRelLemmas);
  local projRelDef::TopCommand =
      buildProjRel(obligations ++
                   map(\ p::(Decorated QName with {relationEnv}, [String]) ->
                         (p.1.fullRel.name, p.2), decNewRels),
         top.relationEnv, top.constructorEnv, top.proverState.buildsOns);
  local projRelLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(QName, [String]) ->
                buildProjRelLemmas(p.1, p.2),
         obligations ++
         map(\ p::(Decorated QName with {relationEnv}, [String]) ->
               (p.1.fullRel.name, p.2),
             decNewRels));

  local obligations::[(QName, [String])] =
      case head(top.proverState.remainingObligations) of
      | projRelElement(r, _) -> r
      | _ -> error("Not possible (addProjRel.obligations)")
      end;

  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | projRelElement(relInfo, _)::_ ->
        let expectedNames::[QName] = map(fst, relInfo)
        in
          if setEq(oldRels, expectedNames)
          then []
          else if subset(oldRels, expectedNames)
          then let missing::[QName] = removeAll(oldRels, expectedNames)
               in
                 [errorMsg("Missing relation" ++
                     (if length(missing) == 1 then " " else "s ") ++
                     implode(", ", map(justShow,
                        map((.pp), removeAll(oldRels, expectedNames)))))]
               end
          else if subset(expectedNames, oldRels)
          then [errorMsg("Too many relations; should not have " ++
                   implode(", ", map(justShow,
                      map((.pp), removeAll(expectedNames, oldRels)))))]
          else [errorMsg("Expected Proj Rel addition" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ",
                             map(justShow, map((.pp), expectedNames))))]
        end
      | l -> [wrongObligation(l)]
      end;
  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                --check no repeated arguments
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Proj Rel for " ++
                          justShow(p.1.pp))]
                 else []) ++
                --check arguments are capitalized
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Proj Rel " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                --check right number of arguments
                (if p.1.relFound &&  --len - 1 to drop prop
                    length(p.2) != p.1.fullRel.types.len - 1
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                --errors from finding relation
                p.1.relErrors ++
                --
                if !p.1.relFound
                then []
                else --new relations only
                     (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     --only one definition for it
                     (if findProjRelGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has Proj Rel defined for it")]
                      else []),
              decNewRels);
  --check all mutual relations included
  top.toAbellaMsgs <-
      let allRels::[QName] =
          filterMap(
             \ p::(Decorated QName with {relationEnv}, [String]) ->
               if p.1.relFound
               then just(p.1.fullRel.name)
               else nothing(),
             decNewRels) ++ oldRels
      in
        flatMap(\ q::QName ->
                  case findMutualGroup(q, top.proverState) of
                  | just(g) ->
                    let missing::[QName] = removeAll(allRels, g)
                    in
                      case missing of
                      | [] -> [] --none missing, so fine
                      | l -> [errorMsg("Missing relation" ++
                                 (if length(l) == 1 then " " else "s ") ++
                                 "defined mutually with " ++
                                 justShow(q.pp) ++ ":  " ++
                                 implode(", ", map(justShow, map((.pp), l))))]
                      end
                    end
                  | nothing() -> [] --bad module name; error elsewhere
                  end,
                allRels)
      end;

  top.is_nonextensible = false;
}





{--------------------------------------------------------------------
  Extension Size Definition
 --------------------------------------------------------------------}
{-
  Build the full R_ES definition for the relations in fullRels
-}
function buildExtSize
TopCommand ::= fullRels::[QName] relEnv::Env<RelationEnvItem>
               cenv::Env<ConstructorEnvItem>
               buildsOns::[(QName, [QName])]
{
  local fullRelInfo::[(QName, RelationEnvItem)] =
      map(\ q::QName ->
            (q, decorate q with {relationEnv=relEnv;}.fullRel),
          fullRels);
  local preds::[(QName, Type)] =
      map(\ p::(QName, RelationEnvItem) ->
            (extSizeQName(p.1.sub),
             foldr1(arrowType,
                    init(p.2.types.toList) ++ --drop prop at end
                    [integerType, propType])),
          fullRelInfo);
  local defs::[Def] =
      buildExtSizeDef(fullRelInfo, fullRels, relEnv, cenv, buildsOns);
  return definitionDeclaration(preds,
            foldrLastElem(consDefs, singleDefs, defs));
}

{-
  Build all the definitional clauses for the extSize version of the
  relations in relInfo
-}
function buildExtSizeDef
[Def] ::= relInfo::[(QName, RelationEnvItem)] allRels::[QName]
          renv::Env<RelationEnvItem> cenv::Env<ConstructorEnvItem>
          buildsOns::[(QName, [QName])]
{
  local pcIndex::Integer = head(relInfo).2.pcIndex;
  local defList::[([Term], Maybe<Metaterm>)] = head(relInfo).2.defsList;
  local firstRel::[Def] =
      buildExtSizeClauses(head(relInfo).1, defList, pcIndex, allRels,
                          renv, cenv, buildsOns);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel ++
                   buildExtSizeDef(t, allRels, renv, cenv, buildsOns)
         end;
}

{-
  Build the clauses for the extSize version of a single relation as
  part of a group of relations (allRels)
-}
function buildExtSizeClauses
[Def] ::= rel::QName defs::[([Term], Maybe<Metaterm>)]
          pcIndex::Integer allRels::[QName]
          renv::Env<RelationEnvItem> cenv::Env<ConstructorEnvItem>
          buildsOns::[(QName, [QName])]
{
  local extSizeRel::QName = extSizeQName(rel.sub);
  local usedVars::[String] =
      case head(defs) of
      | (tms, just(m)) -> m.usedNames ++ flatMap((.usedNames), tms)
      | (tms, nothing()) -> flatMap((.usedNames), tms)
      end;
  local num::String = freshName("N", usedVars);

  --determine whether this is a rule needing a +1 size
  local isExtRule::Boolean =
      let pc::Term = elemAtIndex(head(defs).1, pcIndex)
      in
      let constr::QName = pc.headConstructor
      in
        decorate pc with {
          relationEnv = renv;
          constructorEnv = cenv;
        }.isStructured &&
         --extension rules are the ones from modules building on rel
         contains(rel.moduleName,
            lookup(constr.moduleName, buildsOns).fromJust)
      end end;

  --(has extSize premises added, new body)
  local modBody::(Boolean, Metaterm) =
      case head(defs).2 of
      | just(bindingMetaterm(existsBinder(), binds, body)) ->
        let x::([String], Metaterm) =
            buildExtSizeDefBody(^body, num, isExtRule,
               binds.usedNames ++ usedVars, allRels)
        in
        let fullBinds::Bindings =
            foldr(addBindings(_, nothingType(), _), ^binds, x.1)
        in
          (!null(x.1),
           bindingMetaterm(existsBinder(), fullBinds, x.2))
        end end
      | just(m) ->
        let x::([String], Metaterm) =
            buildExtSizeDefBody(m, num, isExtRule, usedVars, allRels)
        in
          if null(x.1)
          then (false, x.2) --should hypothetically be equal to m
          else (true,
                bindingMetaterm(existsBinder(), toBindings(x.1), x.2))
        end
      | nothing() -> (false, error("Should not access this half"))
      end;
  local newBody::Metaterm = modBody.2;

  --new arguments:  original args + number
  local finalNumber::Term =
      if modBody.1 --something within is modified
      then basicNameTerm(num)
      else if isExtRule
      then integerToIntegerTerm(1) --1 for this step
      else integerToIntegerTerm(0);
  local newArgs::TermList = toTermList(head(defs).1 ++ [^finalNumber]);

  --new def corresponding to first original def
  local hereDef::Def =
      case head(defs).2 of
      | just(_) -> ruleDef(@extSizeRel, @newArgs, @newBody)
      | nothing() -> factDef(@extSizeRel, @newArgs)
      end;

  return case defs of
         | [] -> []
         | _::tl ->
           ^hereDef::buildExtSizeClauses(^rel, tl, pcIndex, allRels,
                                        renv, cenv, buildsOns)
         end;
}

{-
  Build the body (not including bindings) of a clause, changing each
  top-level relation to its extSize version and adding the additions
  - finalNumName is the name for the size at the root of the clause
-}
function buildExtSizeDefBody
--(new names, full metaterm body defs)
([String], Metaterm) ::= body::Metaterm finalNumName::String
    isExtRule::Boolean usedNames::[String] allRels::[QName]
{
  local allNames::[String] = finalNumName::usedNames;

  --(names of all size numbers,  modified body)
  local modBody::([String], [Metaterm]) =
      foldr(\ m::Metaterm rest::([String], [Metaterm]) ->
              case m of
              | relationMetaterm(r, t, _) when contains(^r, allRels) ->
                let name::String = freshName("N", rest.1 ++ allNames)
                in
                  (name::rest.1,
                   relationMetaterm(extSizeQName(r.sub),
                      toTermList(t.toList ++ [basicNameTerm(name)]),
                      emptyRestriction())::rest.2)
                end
              | _ -> (rest.1, m::rest.2)
              end,
            ([], []), splitMetaterm(^body));

  --build a term for addition here
  local addTerm::(Metaterm ::= Term Term Term) =
      \ t1::Term t2::Term result::Term ->
        relationMetaterm(toQName(integerAdditionName),
           toTermList([t1, t2, result]), emptyRestriction());
  --add up all the names in the list
  local sumUp::((String, [String], [Metaterm]) ::= [String]) =
      foldrLastElem(
         \ here::String rest::(String, [String], [Metaterm]) ->
           let name::String =
               freshName("N", rest.2 ++ modBody.1 ++ allNames)
           in
             (name, name::rest.2,
              addTerm(basicNameTerm(here), basicNameTerm(rest.1),
                      basicNameTerm(name))::rest.3)
           end,
         \ here::String -> (here, [], []),
         _);
  --(names of addition results, modified body with additions)
  local allBodyParts::([String], [Metaterm]) =
      case modBody.1 of
      | [] -> ([], modBody.2)
      --more than one
      | h::t when isExtRule -> --1 + sum
        let x::(String, [String], [Metaterm]) = sumUp(h::t)
        in
          (x.2, addTerm(integerToIntegerTerm(1), basicNameTerm(x.1),
                        basicNameTerm(finalNumName))::x.3 ++
                modBody.2)
        end
      | h::y::t ->
        let x::(String, [String], [Metaterm]) = sumUp(y::t)
        in
          (x.2, addTerm(basicNameTerm(h), basicNameTerm(x.1),
                        basicNameTerm(finalNumName))::x.3 ++
                modBody.2)
        end
      | [h] -> --add h = finalNumName to get names right
        ([], [eqMetaterm(basicNameTerm(h),
                 basicNameTerm(finalNumName))] ++ modBody.2)
      end;

  --combine it to get the whole thing as a Metaterm
  local fullBody::Metaterm = foldr1(andMetaterm, allBodyParts.2);
  --all the new names
  local fullNewNameSet::[String] = modBody.1 ++ allBodyParts.1;

  return (fullNewNameSet, ^fullBody);
}





{--------------------------------------------------------------------
  Projection Version of a Relation Definition
 --------------------------------------------------------------------}
{-
  Build the full R_P relation
-}
function buildProjRel
TopCommand ::= relInfo::[(QName, [String])]
               relEnv::Env<RelationEnvItem>
               constrEnv::Env<ConstructorEnvItem>
               --[(module, [modules on which it builds])]
               buildsOns::[(QName, [QName])]
{
  local fullRelInfo::[(QName, [String], RelationEnvItem)] =
      map(\ p::(QName, [String]) ->
            let rel::RelationEnvItem =
                decorate p.1 with {relationEnv=relEnv;}.fullRel
            in
              (rel.name, p.2, rel)
            end,
          relInfo);
  local defInfo::[(QName, ([String], [String], Maybe<Metaterm>),
                   [([Term], Maybe<Metaterm>)], RelationEnvItem)] =
      buildProjRelDefInfo(fullRelInfo);
  return buildProjRelDef(defInfo, buildsOns, relEnv, constrEnv);
}

--Gather up the information we need to build the R_P def clauses
function buildProjRelDefInfo
[(QName, ([String], [String], Maybe<Metaterm>),
  [([Term], Maybe<Metaterm>)], RelationEnvItem)] ::=
          relInfo::[(QName, [String], RelationEnvItem)]
{
  local r::(QName, [String], RelationEnvItem) = head(relInfo);
  local pcIndex::Integer = r.3.pcIndex;
  --split out clauses for non-unknownK and unknownK for this relation,
  --   of which there is <= 1
  local split::([([Term], Maybe<Metaterm>)], [([Term], Maybe<Metaterm>)]) =
      partition(\ p::([Term], Maybe<Metaterm>) ->
                  let pc::Term = elemAtIndex(p.1, pcIndex)
                  in
                    !pc.isUnknownTermK ||
                    !decorate pc with {
                        relationEnv = buildEnv([r.3]);
                        typeEnv = error("not actually needed");
                     }.unknownId.isJust
                  end,
                r.3.defsList);
  local defList::[([Term], Maybe<Metaterm>)] = split.1;
  --(args to conclusion, existentially-bound vars for body, binderless body)
  local qRule::([String], [String], Maybe<Metaterm>) =
      if null(split.2)
      then ([], [], nothing())
      else let kClause::([Term], Maybe<Metaterm>) = head(split.2)
           in
           let usedNames::[String] =
               case kClause.2 of
               | nothing() -> []
               | just(m) -> m.usedNames
               end ++
               flatMap((.usedNames), kClause.1)
           in
           let kName::String = freshName("K", usedNames)
           in
           let newArgs::[String] =
               map(\ t::Term ->
                     case t of
                     | nameTerm(v, _) -> v.shortName
                     | unknownKTerm(_) -> kName
                     | _ -> error("Nothing else should be here")
                     end, kClause.1)
           in
           let newBodyPieces::([String], Maybe<Metaterm>) =
               case kClause.2 of
               | nothing() -> ([], nothing())
               | just(bindingMetaterm(existsBinder(), binds, body)) ->
                 (map(fst, binds.toList), dropFalsePrem(^body))
               | just(m) -> ([], dropFalsePrem(m))
               end
           in
             (newArgs, newBodyPieces)
           end end end end end;
  local firstRel::(QName, ([String], [String], Maybe<Metaterm>),
                   [([Term], Maybe<Metaterm>)], RelationEnvItem) =
      (r.1, qRule, defList, r.3);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel::buildProjRelDefInfo(t)
         end;
}

{-
  Build all the definitional clauses for the projection version of
  the relations in rels and turn them into a definition
-}
function buildProjRelDef
TopCommand ::=
--[(rel, Q rule: (args to conclusion, existentially-bound vars for body,
--                binderless body), def clauses: (args, body), env item)]
   rels::[(QName, ([String], [String], Maybe<Metaterm>),
           [([Term], Maybe<Metaterm>)], RelationEnvItem)]
--[(module, [modules on which it builds])]
   buildsOns::[(QName, [QName])]
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
{
  local preds::[(QName, Type)] =
      map(\ p::(QName, ([String], [String], Maybe<Metaterm>),
                [([Term], Maybe<Metaterm>)], RelationEnvItem) ->
            (projRelQName(p.1.sub),
             foldr1(arrowType, p.4.types.toList)),
          rels);
  local allRels::[QName] = map(fst, rels);
  local fullReplaceRels::(Maybe<Metaterm> ::= Maybe<Metaterm>) =
      \ m::Maybe<Metaterm> ->
        bind(m, \ m::Metaterm ->
                  case m of
                  | bindingMetaterm(existsBinder(), b, m) ->
                    just(bindingMetaterm(existsBinder(), ^b,
                            replaceRelsProjRels(allRels, ^m)))
                  | _ -> just(replaceRelsProjRels(allRels, m))
                  end);
  local defs::[Def] =
      flatMap(\ p::(QName, ([String], [String], Maybe<Metaterm>),
                    [([Term], Maybe<Metaterm>)], RelationEnvItem) ->
                let projRelledQBody::Maybe<Metaterm> =
                    fullReplaceRels(p.2.3)
                in
                let projRelledDefs::[([Term], Maybe<Metaterm>)] =
                    map(\ p::([Term], Maybe<Metaterm>) ->
                          (p.1, fullReplaceRels(p.2)), p.3)
                in
                  buildProjRelClauses(p.1, projRelledDefs,
                     p.2.1, p.2.2, projRelledQBody,
                     p.4.pcIndex, allRels, buildsOns,
                     relEnv, constrEnv)
                end end,
              rels);
  return definitionDeclaration(preds,
            if null(defs) --check to find error loc in debugging
            then error("buildProjRelDef null list")
            else foldrLastElem(consDefs, singleDefs, defs));
}

{-
  Build the clauses for the projection version of a single relation
  as part of a group of relations (allRels)
-}
function buildProjRelClauses
[Def] ::= rel::QName defs::[([Term], Maybe<Metaterm>)]
          qRuleArgs::[String] qRuleBindings::[String]
          qRuleBody::Maybe<Metaterm>
          pcIndex::Integer allRels::[QName]
          buildsOns::[(QName, [QName])] relEnv::Env<RelationEnvItem>
          constrEnv::Env<ConstructorEnvItem>
{
  local projRel::QName = projRelQName(rel.sub);
  local usedVars::[String] =
      case head(defs) of
      | (tms, just(m)) -> m.usedNames ++ flatMap((.usedNames), tms)
      | (tms, nothing()) -> flatMap((.usedNames), tms)
      end;

  --fresh names for bound variables in body of Q rule
  --disjoint from the names in head(defs) and qRuleArgs
  local freshQBindings::[String] =
      foldr(\ x::String thusFar::[String] ->
              freshName(x, thusFar ++ qRuleArgs ++ usedVars)::thusFar,
            [], qRuleBindings);
  local freshQBody::Maybe<Metaterm> =
      case qRuleBody of
      | just(m) ->
        just(
           head(safeReplace([m], qRuleBindings,
                   map(\ x::String -> nameTerm(toQName(x), nothingType()),
                       freshQBindings))))
      | nothing() -> nothing()
      end;

  local pc::Term = elemAtIndex(head(defs).1, pcIndex);
  pc.relationEnv = relEnv;
  pc.constructorEnv = constrEnv;

  --replace vars from Q rule conclusion with terms from rule and
  --unknownK with pc
  local replacedQBody::Maybe<Metaterm> =
      case freshQBody of
      | just(m) ->
        just(decorate head(safeReplace([m], qRuleArgs,
                                       head(defs).1)) with {
                replaceUnknownK = ^pc;
             }.unknownKReplaced)
      | nothing() -> nothing()
      end;

  --determine whether this is a rule needing a projection
  local isExtRule::Boolean =
      let constr::QName = pc.headConstructor
      in --unstructured PC is host rule
         pc.isStructured &&
         --rules for K's getting here are instantiated default rules,
         --  which are host-y rules
         !pc.isUnknownTermK &&
         --extension rules are the ones from modules building on rel
         contains(rel.moduleName,
                  lookup(constr.moduleName, buildsOns).fromJust)
      end;

  --new body for the rule, with all bindings
  local modBody::Maybe<Metaterm> =
     case head(defs).2, replacedQBody of
     | mm, _ when !isExtRule -> mm
     | just(bindingMetaterm(existsBinder(), binds, body)), just(m2) ->
       just(bindingMetaterm(existsBinder(),
               foldr(addBindings(_, nothingType(), _), ^binds,
                     freshQBindings),
               andMetaterm(^body, m2)))
     | just(m1), just(m2) ->
       if null(freshQBindings)
       then just(andMetaterm(m1, m2))
       else just(bindingMetaterm(existsBinder(),
                    toBindings(freshQBindings),
                    andMetaterm(m1, m2)))
     | just(m), nothing() -> just(m)
     | nothing(), just(m) ->
       if null(freshQBindings)
       then just(m)
       else just(bindingMetaterm(existsBinder(),
                    toBindings(freshQBindings), m))
     | nothing(), nothing() -> nothing()
     end;

  local hereDef::Def =
      case modBody of
      | just(body) -> ruleDef(@projRel, toTermList(head(defs).1), body)
      | nothing() -> factDef(@projRel, toTermList(head(defs).1))
      end;

  return case defs of
         | [] -> []
         | _::tl -> ^hereDef::buildProjRelClauses(^rel, tl, qRuleArgs,
                                qRuleBindings, qRuleBody, pcIndex, allRels,
                                buildsOns, relEnv, constrEnv)
         end;
}

{-
  Replace all occurrences of relations in rels in the given metaterm with
  their projRel versions
-}
function replaceRelsProjRels
Metaterm ::= allRels::[QName] m::Metaterm
{
  local replaced::[Metaterm] =
      map(\ m::Metaterm ->
            case m of
            | relationMetaterm(r, t, s) when contains(^r, allRels) ->
              relationMetaterm(projRelQName(r.sub), ^t, ^s)
            | _ -> m
            end,
          splitMetaterm(^m));
  return foldr1(andMetaterm, replaced);
}

{-
  Q rules have bodies of the form
     exists x, m_1 /\ ... /\ m_n /\ (0 = 0 -> false)
  This assumes the binder has been lifted from the beginning and then
  removes the (0 = 0 -> false) assumption.
-}
function dropFalsePrem
Maybe<Metaterm> ::= m::Metaterm
{
  return case m.splitConjunctions of
         | x::y::r -> just(foldr1(andMetaterm, init(x::y::r)))
         | _ -> nothing() --[_] or []
         end;
}





{--------------------------------------------------------------------
  Extension Size Lemmas
 --------------------------------------------------------------------}
{-
  Build the lemmas for using the extension size:
  1. Size is always non-negative
  2. Size is always an integer (is_integer)
  3. ExtSize version implies the relation itself
  4. Relation itself implies the ExtSize version
  The first one is necessary for using our definition of acc.  We
  would not need it if we used nats, but that would lead to problems
  with representing them to the user and showing the difference
  compared to integers.  The second one is for using stdLib theorems
  for addition and less/lesseq.  The last one is so we can use other
  properties of the relation to help us prove Ext_Ind.

  - rel is the relation for which we are defining extSize
  - argNames is the list of (unique) names for the relation arguments
    (does not include size number for extSize)
-}
function buildExtSizeLemmas
[(QName, Metaterm)] ::= rel::QName argNames::[String]
{
  local numName::String = freshName("N", argNames);
  local binds::Bindings = toBindings(argNames ++ [numName]);
  local extSize::Metaterm =
      relationMetaterm(extSizeQName(rel.sub),
         toTermList(map(basicNameTerm, argNames ++ [numName])),
         emptyRestriction());

  --non-neg:  forall \bar{x} n.  extSize \bar{x} n  ->  0 <= n
  local nonNegThmName::QName = ext_ind_pos_name(^rel);
  local nonNegThmBody::Metaterm =
      bindingMetaterm(forallBinder(), @binds,
         impliesMetaterm(@extSize,
            relationMetaterm(toQName(integerLessEqName),
               toTermList([integerToIntegerTerm(0),
                           basicNameTerm(numName)]),
               emptyRestriction())));

  --is int:  forall \bar{x} n.  extSize \bar{x} n  ->  is_integer n
  local isIntThmName::QName = ext_ind_is_int_name(^rel);
  local isIntThmBody::Metaterm =
      bindingMetaterm(forallBinder(), ^binds,
         impliesMetaterm(^extSize,
            relationMetaterm(toQName("extensibella:stdLib:is_integer"),
               toTermList([basicNameTerm(numName)]),
               emptyRestriction())));

  --drop:  forall \bar{x} n.  extSize \bar{x} n  ->  R \bar{x}
  local dropExtSizeName::QName = drop_ext_ind_name(^rel);
  local dropExtSizeBody::Metaterm =
      bindingMetaterm(forallBinder(), ^binds,
         impliesMetaterm(^extSize,
            relationMetaterm(^rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction())));

  --add:  forall \bar{x}.  R \bar{x}  ->  exists n.  extSize \bar{x} n
  local addExtSizeName::QName = add_ext_ind_name(^rel);
  local addExtSizeBody::Metaterm =
      bindingMetaterm(forallBinder(), toBindings(argNames),
         impliesMetaterm(
            relationMetaterm(^rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction()),
            bindingMetaterm(existsBinder(), toBindings([numName]),
               ^extSize)));

return [(^nonNegThmName, ^nonNegThmBody),
        (^isIntThmName, ^isIntThmBody),
        (^dropExtSizeName, ^dropExtSizeBody),
        (^addExtSizeName, ^addExtSizeBody)];
}


function ext_ind_pos_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "ext_size_pos_" ++ rel.shortName);
}
function ext_ind_is_int_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "ext_size_is_int_" ++ rel.shortName);
}
function drop_ext_ind_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "drop_ext_size_" ++ rel.shortName);
}
function add_ext_ind_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "add_ext_size_" ++ rel.shortName);
}





{--------------------------------------------------------------------
  Projection Version Lemmas
 --------------------------------------------------------------------}
{-
  Build the lemmas for using the projection version:
  1. Projection version of the relation implies the relation itself
  This is the only immediately obvious one, but we make this general
  in case another one pops up sometime.

  - rel is the relation for which we are defining the projection version
  - argNames is the list of (unique) names for the relation arguments
-}
function buildProjRelLemmas
[(QName, Metaterm)] ::= rel::QName argNames::[String]
{
  local binds::Bindings = toBindings(argNames);
  local projRel::Metaterm =
      relationMetaterm(projRelQName(rel.sub),
         toTermList(map(basicNameTerm, argNames)),
         emptyRestriction());

  --dropP:  forall \bar{x}.  projRel \bar{X}  ->  R \bar{x}
  local dropPName::QName = dropP_name(^rel);
  local dropPBody::Metaterm =
      bindingMetaterm(forallBinder(), ^binds,
         impliesMetaterm(@projRel,
            relationMetaterm(^rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction())));

  return [(^dropPName, ^dropPBody)];
}


function dropP_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "drop_proj_rel_" ++ rel.shortName);
}





{--------------------------------------------------------------------
  Ext Ind Lemmas
 --------------------------------------------------------------------}
{-
  Build the lemma we know after proving Ext_Ind
  1. Relation itself implies the projection version, modulo the extra
     premises in the Ext_Ind declaration
  Note we also know the extension size version of the relation implies
  the projection version if the extension size was used, but this is
  also a fact we can get from this and the extension size lemmas,
  which must exist if we used the extension size, so we don't add it
  here.

  - rel is the relation for which we are defining the projection version
  - argNames is the list of (unique) names for the relation arguments
-}
function buildExtIndLemma
(QName, Metaterm) ::= rel::QName argNames::[String]
                      bindings::Bindings
                      prems::ExtIndPremiseList
{
  local relTm::Metaterm =
      relationMetaterm(@rel,
         toTermList(map(basicNameTerm, argNames)),
          emptyRestriction());
  local projRel::Metaterm =
      relationMetaterm(projRelQName(rel.sub),
         toTermList(map(basicNameTerm, argNames)),
         emptyRestriction());

  --addP:  forall \bar{x}.  R \bar{X}  ->  projRel \bar{x}
  local addPName::QName = addP_name(^rel);
  local addPBody::Metaterm =
      bindingMetaterm(forallBinder(), @bindings,
         foldr(impliesMetaterm, ^projRel,
               ^relTm::map(snd, prems.toList)));

  return (^addPName, ^addPBody);
}


function addP_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "add_proj_rel_" ++ rel.shortName);
}
