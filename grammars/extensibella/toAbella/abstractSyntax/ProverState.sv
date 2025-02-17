grammar extensibella:toAbella:abstractSyntax;

{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.  And by "a bit" I mean
  "a lot".
-}

data nonterminal ProverState with
   pp, --solely for debugging purposes
   state, debug, displayWidth,
   knownTheorems, knownExtSizes, knownProjRels,
   knownExtInds, remainingObligations,
   knownTypes, knownRels, knownConstrs, mutualRelGroups, buildsOns,
   provingThms, provingExtInds, duringCommands, afterCommands,
   keyRelModules, currentKeyRelModule;


--current state of Abella
annotation state::ProofState;
--theorems we are currently in the process of proving
--should be added to knownThms when we finish the proof
annotation provingThms::[(QName, Metaterm)];
--whether to print out the Abella commands/returns to the user
annotation debug::Boolean;
--approximate maximum line width for display
annotation displayWidth::Integer;

--Theorems we have proven and available
--(qualified name, statement)
annotation knownTheorems::[(QName, Metaterm)];

--ExtInds we have proven and available
--Each sublist is a group of mutually-ext-inded relations
--[[(rel, rel arg names, full bindings, premises)]]
annotation knownExtInds::[[(QName, [String], Bindings, ExtIndPremiseList)]];

--ExtSize relations that have been declared
--Each sublist is a group of mutually-defined ext size relations
annotation knownExtSizes::[[QName]];
--Projection versions of relations that have been declared
--Each sublist is a group of mutually-defined projection versions of relations
annotation knownProjRels::[[QName]];

--Things we will need to do in the proof based on imports that we
--haven't done yet
annotation remainingObligations::[ThmElement];

--Environments of various entities we know
annotation knownTypes::Env<TypeEnvItem>;
annotation knownRels::Env<RelationEnvItem>;
annotation knownConstrs::Env<ConstructorEnvItem>;

--Sets of relations declared mutually
--Does not guarantee they are actually mutual in definition, but they
--   were declared in one group
annotation mutualRelGroups::[[QName]];

--modules and the modules on which they build
annotation buildsOns::[(QName, [QName])];

--module introducing key relation for current property being proven
--use Maybe because there might not be one for some ProverStates
annotation currentKeyRelModule::Maybe<QName>;


abstract production proverState
top::ProverState ::=
   --extInds we are currently in the process of proving
   --should be added to knownExtInds when we finish the proof
   provingExtInds::[(QName, [String], Bindings, ExtIndPremiseList)]
   --things to do when the subgoal reaches that number
   --should clear it from the list once it has been sent to Abella
   --Note:  If there are commands for e.g. Subgoal 2 that are expected
   --  to move us to Subgoal 2.1, there should not be a separate entry
   --  for Subgoal 2.1.  Any sequential commands should be rolled into
   --  a single entry because we don't want to need to check this
   --  repeatedly.
   duringCommands::[(SubgoalNum, [ProofCommand])]
   --module introducing the key relation for each property being proven
   --subgoal number is for when that property becomes current
   keyRelModules::[(SubgoalNum, QName)]
   --things to do when the proof is done
   --I think this is only ever one Split, but make it general in case
   afterCommands::[AnyCommand]
{
  top.pp = ppConcat([text("Prover State{"), realLine(),
      text("  Debug Mode:  "), text(toString(top.debug)), realLine(),
      --during commands
      text("  During Commands:  [") ++ realLine() ++ text("   "),
         ppImplode(realLine() ++ text("   "),
            map(\ p::(SubgoalNum, [ProofCommand]) ->
                  text(subgoalNumToString(p.1) ++ ":  ") ++
                  nest(6, ppImplode(text(""), map((.pp), p.2))), duringCommands)),
         text("]"), realLine(),
      --types
      text("  Type Env:  ["), ppImplode(text(", "), map((.pp),
                                 map((.name), top.knownTypes))), text("]"), realLine(),
      --relations
      text("  Rel Env:  ["), ppImplode(text(", "), map((.pp),
                                 map((.name), top.knownRels))), text("]"), realLine(),
      --constructors
      text("  Con Env:  ["), ppImplode(text(", "), map((.pp),
                                map((.name), top.knownConstrs))) ++ text("]"), realLine(),
      --ext inds
      text("  Ext Inds:  ["), ppImplode(text(",  "),
                                 map(\ l::[(QName, [String], Bindings, ExtIndPremiseList)] ->
                                       ppConcat([text("["),
                                          ppImplode(text(", "), map((.pp), map(fst, l))),
                                          text("]")]), top.knownExtInds)),
                      text("]"), realLine(),
      --ext sizes
      text("  Ext Sizes:  ["), ppImplode(text(",  "),
                                  map(\ l::[QName] ->
                                        ppConcat([text("["),
                                           ppImplode(text(", "), map((.pp), l)),
                                           text("]")]), top.knownExtSizes)),
                      text("]"), realLine(),
      --proj rels
      text("  Proj Rels:  ["), ppImplode(text(",  "),
                                  map(\ l::[QName] ->
                                        ppConcat([text("["),
                                           ppImplode(text(", "), map((.pp), l)),
                                           text("]")]), top.knownProjRels)),
                      text("]"), realLine(),
      --end
      text("}"), realLine()]);

  top.provingExtInds = provingExtInds;
  top.duringCommands = duringCommands;
  top.keyRelModules = keyRelModules;
  top.afterCommands = afterCommands;
}


--Move all non-extensble obligations from the front of the obligation
--   set and add them to the knownThms
--Leaves everything else the same
--The commands must have already been sent to Abella
function removeNonextensibleObligations
ProverState ::= current::ProverState
{
  local outObligations::[ThmElement] =
      dropWhile((.is_nonextensible), current.remainingObligations);
  local take::[ThmElement] =
      takeWhile((.is_nonextensible), current.remainingObligations);
  local outThms::[(QName, Metaterm)] =
      foldl(\ rest::[(QName, Metaterm)] t::ThmElement ->
              decorate t with {knownThms = rest;}.thms ++ rest,
            current.knownTheorems, take);
  return proverState(current.provingExtInds, current.duringCommands,
            current.keyRelModules, current.afterCommands,
            --
            state = current.state, debug = current.debug,
            displayWidth = current.displayWidth, knownTheorems = outThms,
            knownExtInds = current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations = outObligations,
            knownTypes = current.knownTypes,
            knownRels = current.knownRels,
            knownConstrs =current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = current.provingThms,
            buildsOns = current.buildsOns,
            currentKeyRelModule = current.currentKeyRelModule);
}


--Remove an obligation if we finished one, otherwise return the list
--of obligations given
function removeFinishedObligation
[ThmElement] ::=
   obligations::[ThmElement] provenThms::[(QName, Metaterm)]
{
  return
      case obligations of
      | extensibleMutualTheoremGroup(thms, alsos, _)::rest ->
        --everything imported here is in the things we just proved
        if all(map(\ t::QName -> contains(t, map(fst, provenThms)),
                   map(fst, thms ++ alsos)))
        then rest
        else obligations
      | projectionConstraintTheorem(q, x, b, _)::rest ->
        case provenThms of
        | [(q2, _)] when ^q == q2 -> rest
        | _ -> obligations
        end
      | extIndElement(rels, thms, alsos, _)::rest ->
        --everything imported here is in the things we just proved
        if all(map(\ r::QName ->
                     contains(extIndThmName(r), map(fst, provenThms)),
                   map(fst, rels)))
        then rest
        else obligations
      | _ -> obligations
      end;
}


--A proof is done successfully, so modify the prover state accordingly
--Assumes current.state is already the one for it being completed
function finishProof
ProverState ::= current::ProverState
{
  return proverState([], [], [], [],
            --
            state = current.state, debug = current.debug,
            displayWidth = current.displayWidth,
            knownTheorems = current.provingThms ++ current.knownTheorems,
            --keep blanks out of the list for efficiency
            knownExtInds =
                if null(current.provingExtInds) then current.knownExtInds
                else current.provingExtInds::current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations =
               removeFinishedObligation(current.remainingObligations,
                  current.provingThms),
            knownTypes = current.knownTypes, knownRels = current.knownRels,
            knownConstrs = current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = [],
            buildsOns = current.buildsOns,
            currentKeyRelModule = nothing());
}


--A proof is quit, so modify the prover state accordingly
--Assumes current.state is already the one for it being aborted
function abortProof
ProverState ::= current::ProverState
{
  return proverState([], [], [], [],
            --
            state = current.state, debug = current.debug,
            displayWidth = current.displayWidth,
            knownTheorems = current.knownTheorems,
            knownExtInds = current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations = current.remainingObligations,
            knownTypes = current.knownTypes,
            knownRels = current.knownRels,
            knownConstrs = current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = [],
            buildsOns = current.buildsOns,
            currentKeyRelModule = nothing());
}


--Set debug to debugVal, leaving everything else the same
function setProverDebug
ProverState ::= current::ProverState debugVal::Boolean
{
  return proverState(current.provingExtInds,
            current.duringCommands, current.keyRelModules,
            current.afterCommands,
            --
            state = current.state, debug = debugVal,
            displayWidth = current.displayWidth,
            knownTheorems = current.knownTheorems,
            knownExtInds = current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations = current.remainingObligations,
            knownTypes = current.knownTypes,
            knownRels = current.knownRels,
            knownConstrs = current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = current.provingThms,
            buildsOns = current.buildsOns,
            currentKeyRelModule = current.currentKeyRelModule);
}


--Set displayWidth to width, leaving everything else the same
function setProverWidth
ProverState ::= current::ProverState width::Integer
{
  return proverState(current.provingExtInds,
            current.duringCommands, current.keyRelModules,
            current.afterCommands,
            --
            state = current.state, debug = current.debug,
            displayWidth = width,
            knownTheorems = current.knownTheorems,
            knownExtInds = current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations = current.remainingObligations,
            knownTypes = current.knownTypes,
            knownRels = current.knownRels,
            knownConstrs = current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = current.provingThms,
            buildsOns = current.buildsOns,
            currentKeyRelModule = current.currentKeyRelModule);
}


--General updates that might happen in a top command
--Assumes we were not in a proof before
function updateProverStateTop
ProverState ::= current::ProverState newProofState::ProofState
   newThms::[(QName, Metaterm)] newTys::[TypeEnvItem]
   newRels::[RelationEnvItem] newConstrs::[ConstructorEnvItem]
   newMutualRelGroups::[[QName]]
   provingThms::[(QName, Metaterm)]
   provingExtInds::[(QName, [String], Bindings, ExtIndPremiseList)]
   newExtSizeGroup::Maybe<[QName]>
   newProjRelGroup::Maybe<[QName]>
   duringCmds::[(SubgoalNum, [ProofCommand])]
   keyRelModules::[(SubgoalNum, QName)]
   afterCmds::[AnyCommand]
{
  return proverState(provingExtInds, duringCmds,
            if null(keyRelModules) then [] else tail(keyRelModules),
            afterCmds,
            --
            state = ^newProofState, debug = current.debug,
            displayWidth = current.displayWidth,
            knownTheorems = newThms ++ current.knownTheorems,
            knownExtInds = current.knownExtInds,
            knownExtSizes = case newExtSizeGroup of
                            | nothing() -> current.knownExtSizes
                            | just(g) -> g::current.knownExtSizes
                            end,
            knownProjRels = case newProjRelGroup of
                            | nothing() -> current.knownProjRels
                            | just(g) -> g::current.knownProjRels
                            end,
            remainingObligations =
               --other obligations are removed when they are proved
               --since these have no proof, remove them here
               case current.remainingObligations of
               | extSizeElement(rels, _)::rest
                 when newExtSizeGroup.isJust &&
                      subset(map(fst, rels),
                             newExtSizeGroup.fromJust) -> rest
               | projRelElement(rels, _)::rest
                 when newProjRelGroup.isJust &&
                      subset(map(fst, rels),
                             newProjRelGroup.fromJust) -> rest
               | l -> l
               end,
            knownTypes = addEnv(current.knownTypes, newTys),
            knownRels = addEnv(current.knownRels, newRels),
            knownConstrs = addEnv(current.knownConstrs, newConstrs),
            mutualRelGroups = newMutualRelGroups ++ current.mutualRelGroups,
            provingThms = provingThms, buildsOns = current.buildsOns,
            currentKeyRelModule =
                if null(keyRelModules) then nothing()
                else just(head(keyRelModules).2));
}


--Replace only the state in a prover state
function setProofState
ProverState ::= current::ProverState newProofState::ProofState
{
  local updateKeyRelModule::Boolean =
      case current.keyRelModules of
      | [] -> false
      | (s, _)::_ -> subgoalStartsWith(s, newProofState.currentSubgoal)
      end;
  return proverState(current.provingExtInds, current.duringCommands,
            if updateKeyRelModule then tail(current.keyRelModules)
            else current.keyRelModules,
            current.afterCommands,
            --
            state = ^newProofState, debug = current.debug,
            displayWidth = current.displayWidth,
            knownTheorems = current.knownTheorems,
            knownExtInds = current.knownExtInds,
            knownExtSizes = current.knownExtSizes,
            knownProjRels = current.knownProjRels,
            remainingObligations = current.remainingObligations,
            knownTypes = current.knownTypes,
            knownRels =current.knownRels,
            knownConstrs = current.knownConstrs,
            mutualRelGroups = current.mutualRelGroups,
            provingThms = current.provingThms,
            buildsOns = current.buildsOns,
            currentKeyRelModule = if updateKeyRelModule
                                  then just(head(current.keyRelModules).2)
                                  else current.currentKeyRelModule);
}


--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::= obligations::[ThmElement] tyEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   mutualRelGroups::[[QName]] knownThms::[(QName, Metaterm)]
   buildsOns::[(QName, [QName])]
{
  {-Starting environments with the things from the environment not
    having special syntax to hide them-}
  --types with special constructors can still be seen, so we add them
  local knownTys::[TypeEnvItem] =
      buildEnv(
         [libTypeEnvItem(toQName(pairTypeName), 2),
          libTypeEnvItem(toQName("$lib__nat"), 0),
          libTypeEnvItem(toQName("$lib__bool"), 0),
          libTypeEnvItem(toQName("$lib__integer"), 0),
          libTypeEnvItem(toQName("$char"), 0), --part of strings
          --not our library, but still *a* library
          libTypeEnvItem(toQName("list"), 1),
          libTypeEnvItem(toQName("prop"), 0)]);
  local knownRels::[RelationEnvItem] =
      buildEnv(
         [fixedRelationEnvItem(toQName("extensibella:stdLib:is_pair"),
             toTypeList([arrowType(varType("A"), propType),
                         arrowType(varType("B"), propType),
                         pairType(varType("A"), varType("B")),
                         propType])),
          fixedRelationEnvItem(toQName("extensibella:stdLib:is_string"),
             toTypeList([stringType(), propType])),
          fixedRelationEnvItem(toQName("extensibella:stdLib:is_bool"),
             toTypeList([boolType, propType])),
          fixedRelationEnvItem(toQName("extensibella:stdLib:is_integer"),
             toTypeList([integerType, propType])),
          fixedRelationEnvItem(toQName("extensibella:stdLib:is_list"),
             toTypeList([arrowType(varType("A"), propType),
                         listType(varType("A")), propType])),
              --this doesn't seem special enough to merit an unqualified name
          fixedRelationEnvItem(toQName("extensibella:stdLib:length"),
             toTypeList([listType(varType("A")),
                         integerType, propType])),
          --need hidden relations due to how we handle importing from
          --one module to another one
          fixedRelationEnvItem(toQName(integerAdditionName),
             toTypeList([integerType, integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerSubtractionName),
             toTypeList([integerType, integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerMultiplicationName),
             toTypeList([integerType, integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerDivisionName),
             toTypeList([integerType, integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerModulusName),
             toTypeList([integerType, integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerNegateName),
             toTypeList([integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerLessName),
             toTypeList([integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerLessEqName),
             toTypeList([integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerGreaterName),
             toTypeList([integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(integerGreaterEqName),
             toTypeList([integerType, integerType, propType])),
          fixedRelationEnvItem(toQName(appendName),
             toTypeList([listType(varType("A")),
                         listType(varType("A")),
                         listType(varType("A")), propType])),
          fixedRelationEnvItem(toQName(orName),
             toTypeList([boolType, boolType, boolType, propType])),
          fixedRelationEnvItem(toQName(andName),
             toTypeList([boolType, boolType, boolType, propType])),
          fixedRelationEnvItem(toQName(notName),
             toTypeList([boolType, boolType, propType])),
          --
          fixedRelationEnvItem(toQName("extensibella:stdLib:acc"),
             toTypeList([integerType, propType])),
          --once again, not our library, but *a* library
          fixedRelationEnvItem(toQName("member"),
             toTypeList([varType("A"),
                         listType(varType("A")), propType]))
         ]);
    local knownConstrs::[ConstructorEnvItem] =
        buildEnv(
            --hidden pair constructor
           [constructorEnvItem(toQName(pairConstructorName),
               pairType(varType("A"), varType("B")),
               toTypeList([varType("A"), varType("B")])),
            --hidden integer constructors
            constructorEnvItem(toQName(posIntegerName),
               integerType,
               toTypeList([nameType(toQName("$lib__nat"))])),
            constructorEnvItem(toQName(negIntegerName),
               integerType,
               toTypeList([nameType(toQName("$lib__nat"))])),
            --hidden nat constructors
            constructorEnvItem(toQName(natSuccName),
               nameType(toQName("$lib__nat")),
               toTypeList([nameType(toQName("$lib__nat"))])),
            constructorEnvItem(toQName(natZeroName),
               nameType(toQName("$lib__nat")), toTypeList([]))
           ]);

  return proverState([], [], [], [],
            --
            state = noProof(isAbellaForm=false), debug = false,
            displayWidth = 80, knownTheorems = knownThms,
            knownExtInds = [], knownExtSizes = [], knownProjRels = [],
            remainingObligations = obligations,
            knownTypes = addEnv(tyEnv, knownTys),
            knownRels = addEnv(relEnv, knownRels),
            knownConstrs = addEnv(constrEnv, knownConstrs),
            mutualRelGroups = mutualRelGroups,
            provingThms = [], buildsOns = buildsOns,
            currentKeyRelModule = nothing());
}


--Drop a duringCommand from the beginning, leaving all else the same
--This should only be used when the first command has just run
function dropDuringCommand
ProverState ::= p::ProverState
{
  return proverState(p.provingExtInds, tail(p.duringCommands),
            p.keyRelModules, p.afterCommands,
            --
            state = p.state, debug = p.debug,
            displayWidth = p.displayWidth,
            knownTheorems = p.knownTheorems,
            knownExtInds = p.knownExtInds,
            knownExtSizes = p.knownExtSizes,
            knownProjRels = p.knownProjRels,
            remainingObligations = p.remainingObligations,
            knownTypes = p.knownTypes, knownRels = p.knownRels,
            knownConstrs = p.knownConstrs,
            mutualRelGroups = p.mutualRelGroups,
            provingThms = p.provingThms,
            buildsOns = p.buildsOns,
            currentKeyRelModule = p.currentKeyRelModule);
}


--(full name, statement)
function findTheorem
[(QName, Metaterm)] ::= name::QName state::ProverState
{
  return
     filter(
        if name.isQualified
        then \ p::(QName, Metaterm) -> p.1 == ^name
        else \ p::(QName, Metaterm) -> p.1.shortName == name.shortName,
        state.knownTheorems);
}

--Find an ExtInd declaration group including rel
function findExtIndGroup
Maybe<[(QName, [String], Bindings, ExtIndPremiseList)]> ::=
   name::QName state::ProverState
{
  local find::[[(QName, [String], Bindings, ExtIndPremiseList)]] =
      filter(\ l::[(QName, [String], Bindings, ExtIndPremiseList)] ->
               contains(^name, map(fst, l)),
             state.knownExtInds);
  return case find of
         | [] -> nothing()
         | [x] -> just(x)
         | _ -> error("findExtIndGroup impossible")
         end;
}

--Find an ExtSize declaration group including rel
function findExtSizeGroup
Maybe<[QName]> ::= name::QName state::ProverState
{
  local find::[[QName]] = filter(contains(^name, _), state.knownExtSizes);
  return case find of
         | [] -> nothing()
         | [x] -> just(x)
         | _ -> error("findExtSizeGroup impossible")
         end;
}

--Find a R_P declaration group including rel
function findProjRelGroup
Maybe<[QName]> ::= name::QName state::ProverState
{
  local find::[[QName]] = filter(contains(^name, _), state.knownProjRels);
  return case find of
         | [] -> nothing()
         | [x] -> just(x)
         | _ -> error("findProjRelGroup impossible")
         end;
}


--check whether builtOnMod is in the builds-on set for buildingOnMod
function buildsOn
Boolean ::= p::ProverState builtOnMod::QName buildingOnMod::QName
{
  return
      case lookup(^buildingOnMod, p.buildsOns) of
      | just(l) -> contains(^builtOnMod, l)
      | nothing() ->
        error("Unknown module " ++ justShow(buildingOnMod.pp))
      end;
}


--Find the mutual group with which a relation was declared
function findMutualGroup
Maybe<[QName]> ::= name::QName state::ProverState
{
  local find::[[QName]] =
      filter(contains(^name, _), state.mutualRelGroups);
  return case find of
         | [] -> nothing()
         | [x] -> just(x)
         | _ -> error("findMutualGroup multiple")
         end;
}
