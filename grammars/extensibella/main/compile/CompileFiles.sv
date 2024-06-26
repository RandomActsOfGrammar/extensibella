grammar extensibella:main:compile;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;


--Run through a list of files, compiling them
function compile_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  return foldl(\ thusFar::IOVal<Integer> f::String ->
                 if thusFar.iovalue == 0
                 then compile_file(parsers, thusFar.io, f, config)
                 else thusFar,
               ioval(ioin, 0), config.filenames);
}


--Compile a file, outputting it into the generated directory
function compile_file
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken filename::String
                   config::Configuration
{
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement],
                      [(QName, [QName])]))>> =
      processFile(filename, parsers, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement],
                    [(QName, [QName])]) =
      fileInfo.iovalue.fromRight.snd;
  --
  local modComms::ListOfCommands = processed.1;
  modComms.typeEnv = [];
  modComms.relationEnv = [];
  modComms.constructorEnv = [];
  modComms.currentModule = fileAST.1.fromJust;
  modComms.config = config;
  modComms.ignoreDefErrors = true;
  modComms.proverState =
      error("extensibella:main:compile:compile_file.modComms.proverState");
  local fileErrors::[Message] = fileAST.2.fileErrors;
  --
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(parsers, fileInfo.io);
  local importedProofDefs::([TypeEnvItem], [RelationEnvItem],
                            [ConstructorEnvItem], [[QName]]) =
      defElementsDefinitions(processed.2);
  local proverState::ProverState =
      defaultProverState(processed.3,
         buildEnv(modComms.tys ++ importedProofDefs.1),
         buildEnv(modComms.rels ++ importedProofDefs.2),
         buildEnv(modComms.constrs ++ importedProofDefs.3),
         importedProofDefs.4 ++ modComms.newMutualRelGroups,
         stdLibThms.iovalue.fromRight, processed.4);
  --
  local compiledContents::String =
      buildCompiledOutput(fileAST.1.fromJust, fileAST.2, proverState);
  local extensibellaGen::IOVal<String> =
      envVarT("EXTENSIBELLA_GENERATED", stdLibThms.io);
  local outputFile::String =
      extensibellaGen.iovalue ++ fileAST.1.fromJust.outerfaceFileName;
  local written::IOToken =
      writeFileT(outputFile, compiledContents, extensibellaGen.io);

  return
     case fileInfo.iovalue of
     | left(err) -> ioval(printT(err, fileInfo.io), 1)
     | right(_) ->
       if !null(fileErrors)
       then ioval(printT("Processing errors:\n" ++
                     implode("\n", map((.msg_pp), fileErrors)) ++ "\n",
                     fileInfo.io), 1)
       else if extensibellaGen.iovalue == ""
       then ioval(printT("Extensibella generated location not set\n",
                         extensibellaGen.io), 1)
       else ioval(printT("Successfully compiled file " ++ filename ++
                         "\n", written), 0)
     end;
}




function buildCompiledOutput
String ::= currentModule::QName comms::ListOfCommands
           proverState::ProverState
{
  comms.typeEnv = proverState.knownTypes;
  comms.relationEnv = proverState.knownRels;
  comms.constructorEnv = proverState.knownConstrs;
  comms.proverState = proverState;
  comms.currentModule = currentModule;
  comms.ignoreDefErrors = true;
  local initTags::[(Integer, Integer, String)] =
      filterMap(fst, comms.compiled);
  local allTagged::[((Integer, Integer, String), TopCommand)] =
      combineTags(comms.compiled, initTags, (0, 1, ""),
         currentModule);
  --use abella_pp to get correct prefixes for relations, types, etc.
  return implode("\n",
            map(\ p::((Integer, Integer, String), TopCommand) ->
                  toString(p.1.1) ++ "/" ++ toString(p.1.2) ++
                  " -> " ++ p.1.3 ++ " : " ++ p.2.abella_pp,
                allTagged));
}


function combineTags
[((Integer, Integer, String), TopCommand)] ::=
   comms::[(Maybe<(Integer, Integer, String)>, TopCommand)]
   tags::[(Integer, Integer, String)] last::(Integer, Integer, String)
   mod::QName
{
  local n::Integer = hashModule(mod);
  return
      case comms, tags of
      | [], _ -> []
      | (just(t), c)::rest, _::restT ->
        (t, c)::combineTags(rest, restT, t, mod)
      | (nothing(), c)::rest, nextT::restT ->
        let newTag::(Integer, Integer) = betweenTag(last, nextT, n)
        in
          ((newTag.1, newTag.2, justShow(mod.pp)),
            c)::combineTags(rest, tags,
                   (newTag.1, newTag.2, justShow(mod.pp)), mod)
        end
      | (nothing(), c)::rest, [] ->
        let newTag::(Integer, Integer, String) =
            (last.1 + n, last.2, justShow(mod.pp))
        in
          (newTag, c)::combineTags(rest, [], newTag, mod)
        end
      end;
}

function betweenTag
(Integer, Integer) ::=
   low::(Integer, Integer, String) high::(Integer, Integer, String)
   n::Integer
{
  --get the same denominator for both tag numbers
  local denominator::Integer =
      if low.2 == high.2
      then low.2
      else low.2 * high.2;
  local lowNumerator::Integer =
      if low.2 == high.2
      then low.1
      else low.1 * high.2;
  local highNumerator::Integer =
      if low.2 == high.2
      then high.1
      else high.1 * low.2;
  --difference between them
  local diff::Integer = highNumerator - lowNumerator;
  --2^k such that n/(2^k) < diff/denominator
  local kDen::Integer = find2KValue(diff, denominator, n);
  --find new tag:  low + n/ked
  local fullNum::Integer = lowNumerator * kDen + n;
  local fullDen::Integer = denominator * kDen;
  --find gcd to reduce if possible
  local g::Integer = gcd(fullNum, fullDen);
  return
     --if same tags, only possible tag between uses same number
     if lowNumerator == highNumerator
     then (low.1, low.2)
     else (fullNum / g, fullDen / g);
}

--find 2^k for the smallest non-negative k such that
--   n/(2^k) < diff/denominator
function find2KValue
Integer ::= diff::Integer denominator::Integer n::Integer
{
  return find2KValue_help(diff, denominator, n, 1);
}
function find2KValue_help
Integer ::= diff::Integer denominator::Integer n::Integer
            kDenThusFar::Integer
{
  local fullDen::Integer = denominator * kDenThusFar;
  local fullDiff::Integer = diff * kDenThusFar;
  return if n < fullDiff
         then kDenThusFar
         else find2KValue_help(diff, denominator, n, 2 * kDenThusFar);
}

function gcd
Integer ::= a::Integer b::Integer
{
  return if a == 0
         then b
         else let n::Integer = b % a
              in
                gcd(if n < 0 then a + n else n, a)
              end;
}


--hash a module into a number we can use for creating a tag
function hashModule
Integer ::= module::QName
{
  --need a non-negative, non-zero, non-one number
  local n::Integer = hashString(justShow(module.pp)) % 83;
  return 2 + if n < 0 then 83 + n else n;
}





synthesized attribute compiled<a>::a;

attribute
   compiled<[(Maybe<(Integer, Integer, String)>, TopCommand)]>
occurs on ListOfCommands;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.compiled = [];
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.compiled =
      case a.compiled of
      | just(ac) -> (a.maybeTag, ac)::rest.compiled
      | nothing() -> rest.compiled
      end;
}



attribute compiled<Maybe<TopCommand>>, maybeTag occurs on AnyCommand;

synthesized attribute maybeTag::Maybe<(Integer, Integer, String)>;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.compiled =
      case c.compiled of
      | just(x) -> just(x)
      | nothing() -> nothing()
      end;

  top.maybeTag = c.maybeTag;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.compiled = nothing();
  top.maybeTag = nothing();
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.compiled = nothing();
  top.maybeTag = nothing();
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.compiled = nothing();
  top.maybeTag = nothing();
}



attribute compiled<Maybe<TopCommand>>, maybeTag occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.compiled = just(theoremDeclaration(fullName, params, body.full));
  top.maybeTag = nothing();
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local fullPreds::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            ( if p.1.isQualified
              then p.1
              else addQNameBase(top.currentModule, p.1.shortName),
             decorate p.2 with {typeEnv = top.typeEnv;}.full ),
          preds);
  top.compiled = just(definitionDeclaration(fullPreds, defs.full));
  top.maybeTag = nothing();
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local fullPreds::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            ( if p.1.isQualified
              then p.1
              else addQNameBase(top.currentModule, p.1.shortName),
             decorate p.2 with {typeEnv = top.typeEnv;}.full ),
          preds);
  top.compiled = just(codefinitionDeclaration(fullPreds, defs.full));
  top.maybeTag = nothing();
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.compiled = nothing();
  top.maybeTag = nothing();
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.compiled =
      just(splitTheorem(theoremName.fullRel.name, expandedNames));
  top.maybeTag = nothing();
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.compiled = nothing();
  top.maybeTag = nothing();
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.compiled = just(kindDeclaration(newNames, k));
  top.maybeTag = nothing();
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.compiled = just(typeDeclaration(newNames, ty.full));
  top.maybeTag = nothing();
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.compiled = error("Should not compile importCommand");
  top.maybeTag = nothing();
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.compiled =
      just(extensibleTheoremDeclaration(thms.full, alsos.full));
  top.maybeTag = nothing();
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  local foundThm::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | extensibleMutualTheoremGroup(thms, alsos, _) ->
                 setEq(map(fst, thms), names)
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundThm of
      | [extensibleMutualTheoremGroup(thms, alsos, _)] ->
        just(
           extensibleTheoremDeclaration(
              foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
                      rest::ExtThms ->
                      addExtThms(p.1, p.2, p.3, p.4, rest),
                    newThms.full, thms),
              foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
                      rest::ExtThms ->
                      addExtThms(p.1, p.2, p.3, p.4, rest),
                    newAlsos.full, alsos)))
      | _ ->
        error("Could not identify theorems when compiling prove; " ++
              "file must be checkable before compilation")
      end;
  top.maybeTag = just(head(foundThm).tag);
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.compiled =
      just(projectionConstraint(fullName, binds, body.full));
  top.maybeTag = nothing();
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  local foundThm::[ThmElement] =
      filter(
         \ t::ThmElement ->
           case t of
           | projectionConstraintTheorem(projName, binds, body, _) ->
             name == projName
           | _ -> false
           end,
         top.proverState.remainingObligations);
  top.compiled =
      case foundThm of
      | [projectionConstraintTheorem(name, binds, body, _)] ->
        just(projectionConstraint(name, binds, body))
      | _ ->
        error("Could not identify constraint when compiling " ++
              "Prove_Constraint; file must be checkable before " ++
              "compilation")
      end;
  top.maybeTag = just(head(foundThm).tag);
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.compiled =
      just(extIndDeclaration(body.full, thms.full, alsos.full));
  top.maybeTag = nothing();
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  local foundExtInd::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | extIndElement(relInfo, thms, alsos, _) ->
                 let l::[QName] = map(fst, relInfo)
                 in --equal by mutual subsets
                   subset(l, rels) && subset(rels, l)
                 end
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundExtInd of
      | [extIndElement(relInfo, thms, alsos, _)] ->
        just(extIndDeclaration(
                branchExtIndBody(extIndInfo_to_extIndBody(relInfo),
                                 newRels.full),
              foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
                      rest::ExtThms ->
                      addExtThms(p.1, p.2, p.3, p.4, rest),
                    newThms.full, thms),
              foldr(\ p::(QName, Bindings, ExtBody, InductionOns)
                      rest::ExtThms ->
                      addExtThms(p.1, p.2, p.3, p.4, rest),
                    newAlsos.full, alsos)))
      | _ ->
        error("Could not identify Ext_Ind when compiling " ++
              "Prove_Ext_Ind; file must be checkable before " ++
              "compilation")
      end;
  top.maybeTag = just(head(foundExtInd).tag);
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.compiled =
      just(extSizeDeclaration(
              map(\ p::(QName, [String]) ->
                    (decorate p.1 with {
                        relationEnv = top.relationEnv;}.fullRel.name,
                     p.2),
                  rels)));
  top.maybeTag = nothing();
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  local foundExtSize::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | extSizeElement(relInfo, _) ->
                 let l::[QName] = map(fst, relInfo)
                 in --equal by mutual subsets
                   subset(l, oldRels) && subset(oldRels, l)
                 end
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundExtSize of
      | [extSizeElement(relInfo, _)] ->
        just(extSizeDeclaration(relInfo ++
                map(\ p::(QName, [String]) ->
                      (decorate p.1 with {
                          relationEnv = top.relationEnv;}.fullRel.name,
                       p.2),
                    newRels)))
      | _ ->
        error("Could not identify Ext_Size when compiling " ++
              "Add_Ext_Size; file must be checkable before " ++
              "compilation")
      end;
  top.maybeTag = just(head(foundExtSize).tag);
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.compiled =
      just(projRelDeclaration(
              map(\ p::(QName, [String]) ->
                    (decorate p.1 with {
                        relationEnv = top.relationEnv;}.fullRel.name,
                     p.2),
                  rels)));
  top.maybeTag = nothing();
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  local foundProjRel::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | projRelElement(relInfo, _) ->
                 let l::[QName] = map(fst, relInfo)
                 in --equal by mutual subsets
                   subset(l, oldRels) && subset(oldRels, l)
                 end
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundProjRel of
      | [projRelElement(relInfo, _)] ->
        just(projRelDeclaration(relInfo ++
                map(\ p::(QName, [String]) ->
                      (decorate p.1 with {
                          relationEnv = top.relationEnv;}.fullRel.name,
                       p.2),
                    newRels)))
      | _ ->
        error("Could not identify Proj_Rel when compiling " ++
              "Add_Proj_Rel; file must be checkable before " ++
              "compilation")
      end;
  top.maybeTag = just(head(foundProjRel).tag);
}
