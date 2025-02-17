grammar extensibella:main:run;


type DecCmds = Decorated RunCommands with {
                  currentModule, filename, parsers, priorStep, config,
                  proverState, abella, ioin, interactive, cmdID
               };


{--
 - Set up and walk through a list of commands, presenting the proofs they represent
 -
 - @filename  The name of the file we are processing, if any
 - @cmds  Commands being processed
 - @import_parse  Parser for reading imported files
 - @from_parse  Parser for reading Abella output
 - @currentModule  Module about which we are proving properties
 - @definitionCmds  Commands for imports
 - @importDefs  Proof definitions being imported
 - @importThms  Proof obligations being imported
 - @config  The configuration of the process
 - @ioin  The incoming IO token
 - @return  The resulting IO token and exit status
-}
function run
IOVal<Integer> ::=
   filename::String cmds::RunCommands
   parsers::AllParsers
   currentModule::QName
   definitionCmds::ListOfCommands
   importDefs::[DefElement]
   importThms::[ThmElement]
   buildsOns::[(QName, [QName])]
   config::Configuration ioin::IOToken
{
  local decCmds::Either<IOVal<String>  DecCmds> =
      buildDecRunCommands(filename, ^cmds, parsers, ^currentModule,
         ^definitionCmds, importDefs, importThms, buildsOns, config,
         ioin);

  return
     case decCmds of
     | left(errIO) ->
       ioval(printT("Error:  " ++ errIO.iovalue ++ "\n", errIO.io), 1)
     | right(c) -> c.runResult
     end;
}


--pull this out into a separate function so we can get the list of
--   commands that has run, with all the states in which they ran,
--   instead of the result alone
function buildDecRunCommands
Either<IOVal<String>  DecCmds> ::=
   filename::String cmds::RunCommands
   parsers::AllParsers
   currentModule::QName
   definitionCmds::ListOfCommands
   importDefs::[DefElement]
   importThms::[ThmElement]
   buildsOns::[(QName, [QName])]
   config::Configuration ioin::IOToken
{
  local started::IOVal<Either<String ProcessHandle>> =
      startAbella(ioin, config);
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(parsers, started.io);
  --basic context information from the definition file
  local build_context::(Env<TypeEnvItem>, Env<RelationEnvItem>,
                        Env<ConstructorEnvItem>) =
      module_elements(^definitionCmds);
  --context information for imported definitions
  local importedProofDefs::([TypeEnvItem], [RelationEnvItem],
                            [ConstructorEnvItem], [[QName]]) =
      defElementsDefinitions(importDefs);
  --combine definition file and imported proof definitions
  local startProverState::ProverState =
      defaultProverState(importThms,
         addEnv(build_context.1, importedProofDefs.1),
         addEnv(build_context.2, importedProofDefs.2),
         addEnv(build_context.3, importedProofDefs.3),
         importedProofDefs.4 ++ definitionCmds.newMutualRelGroups,
         stdLibThms.iovalue.fromRight, buildsOns);
  --send definitions to Abella
  local importDefCmds::[AnyCommand] =
      flatMap(
         \ d::DefElement ->
           flatMap(
              \ a::AnyCommand ->
                decorate a with {
                  currentModule = error("currentModule not needed");
                  proverState = startProverState;
                  priorStep = error("priorStep not needed");
                  typeEnv = startProverState.knownTypes;
                  relationEnv = startProverState.knownRels;
                  constructorEnv = startProverState.knownConstrs;
                  boundNames = [];
                }.toAbella, d.encode),
         importDefs);
  local set_up_abella::IOToken =
      set_up_abella_module(^currentModule, ^definitionCmds, importDefCmds,
         parsers, started.iovalue.fromRight, stdLibThms.io,
         config);
  --
  local handleIncoming::([AnyCommand], ProverState) =
      handleIncomingThms(startProverState);
  local sendIncoming::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), handleIncoming.1),
         started.iovalue.fromRight, set_up_abella, config);

  --set inh attrs for processing file
  cmds.currentModule = ^currentModule;
  cmds.filename = filename;
  cmds.parsers = parsers;
  cmds.proverState = handleIncoming.2;
  cmds.priorStep =
      decorate emptyRunCommands() with {
         currentModule = ^currentModule;
         interactive = config.runsInteractive;
         priorStep = error("initial.priorStep");
         proverState = handleIncoming.2;
         abella = started.iovalue.fromRight;
         ioin = error("initial.ioin");
         parsers = parsers;
         config = config;
      };
  cmds.config = config;
  cmds.abella = started.iovalue.fromRight;
  cmds.ioin = sendIncoming.io;
  cmds.interactive = config.runsInteractive;

  return
     if !started.iovalue.isRight
     then left(ioval(started.io, started.iovalue.fromLeft))
     else if !stdLibThms.iovalue.isRight
     then left(ioval(stdLibThms.io, stdLibThms.iovalue.fromLeft))
     else right(cmds);
}

--pull out the information for building environments
function module_elements
(Env<TypeEnvItem>, Env<RelationEnvItem>, Env<ConstructorEnvItem>) ::=
   comms::ListOfCommands
{
  comms.typeEnv = [];
  comms.relationEnv = [];
  comms.constructorEnv = [];
  comms.currentModule = error("currentModule not needed");
  comms.ignoreDefErrors = true;
  comms.proverState =
      error("extensibella:main:run:module_elements.proverState");
  return (buildEnv(comms.tys), buildEnv(comms.rels),
          buildEnv(comms.constrs));
}





----------------------------------------------------------------------
-- Translate from ListOfCommands to RunCommands
-- Need them separate because they set envs differently
-- Get it this way to avoid needing a special parser
----------------------------------------------------------------------
synthesized attribute toRunCommands::RunCommands
   occurs on ListOfCommands;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.toRunCommands = emptyRunCommands();
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.toRunCommands = addRunCommands(^a, rest.toRunCommands);
}





----------------------------------------------------------------------
-- Actually run the commands
----------------------------------------------------------------------
inherited attribute filename::String;

synthesized attribute runResult::IOVal<Integer>;

attribute
   filename, runResult
occurs on RunCommands;

aspect production emptyRunCommands
top::RunCommands ::=
{
  local state::ProofState = top.proverState.state;

  --Permit the addition of extra actions to be carried out
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;

  --clean up by exiting Abella now that there is nothing more to do
  local finalIO::IOToken =
      exitAbella([anyNoOpCommand(quitCommand())], io(top.ioin),
         top.abella, top.proverState.debug, top.config);

  top.runResult =
      if !top.config.runningFile --non-file can quit whenever
      then ioval(finalIO, 0)
      else if state.inProof
      then ioval(printT("Proof in progress at end of file " ++
                        top.filename ++ "\n", finalIO), 1)
      else if !null(top.proverState.remainingObligations)
      then ioval(printT("Not all proof obligations fulfilled in " ++
                        "file " ++ top.filename ++ "\n", finalIO), 1)
      else ioval(printT("Successfully processed file " ++
                        top.filename ++ "\n", finalIO), 0);
}


abstract production addRunCommands
top::RunCommands ::= a::AnyCommand rest::RunCommands
{
  forwards to error("Should not forward");

  top.isNull = false;

  rest.currentModule = top.currentModule;
  rest.filename = top.filename;
  rest.parsers = top.parsers;
  rest.abella = top.abella;
  rest.config = top.config;
  rest.interactive = top.interactive;

  production state::ProofState = top.proverState.state;
  local debug::Boolean = top.proverState.debug;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  a.typeEnv = top.proverState.knownTypes;
  a.relationEnv = top.proverState.knownRels;
  a.constructorEnv = top.proverState.knownConstrs;
  a.proverState = top.proverState;
  a.boundNames = state.boundNames_out;
  a.priorStep = top.priorStep;
  a.currentModule = top.currentModule;
  a.interactive = top.interactive;
  a.ignoreDefErrors = false; --running, so check defs
  --whether we have an error
  local is_error::Boolean = any(map((.isError), a.toAbellaMsgs));
  local speak_to_abella::Boolean = !is_error && !null(a.toAbella);
  --an error or message based on our own checking
  local our_own_output::String =
      errors_to_string(a.toAbellaMsgs);
  --Send to Abella and read output
  ----------------------------
  local io_action_1::IOVal<String> =
      if speak_to_abella
      then sendCmdsToAbella(map((.abella_pp), a.toAbella),
              top.abella, top.ioin, top.config)
      else ioval(top.ioin, "");
  local back_from_abella::String = io_action_1.iovalue;
  local full_a::FullDisplay =
      processDisplay(back_from_abella, top.parsers.from_parse);
  a.newProofState = full_a.proof;
  --Output if in debugging mode
  ----------------------------
  local io_action_2::IOToken =
      if speak_to_abella
      then debugOutput(debug, top.config, a.toAbella,
              "Entered Command", back_from_abella, io_action_1.io)
                                      --Why?  Solving type constraints
      else debugOutput(debug, top.config, tail([anyParseFailure("")]),
              "Entered Command", "", io_action_1.io);

  {-
    FURTHER STATE PROCESSING
  -}
  --whether the command was full undo in PG
  local fullUndo::Boolean =
      case a.newPriorStep of
      | nothing() -> false
      | just(s) -> s.isNull
      end;
  --whether to do the processing or launder the IOToken through
  local continueProcessing::Boolean =
      speak_to_abella && !is_error && !fullUndo;
  --Run any during commands for the current subgoal
  local io_action_3::IOVal<(Integer, ProverState, FullDisplay)> =
      if continueProcessing
      then runDuringCommands(a.newProverState, ^full_a,
              top.parsers.from_parse, io_action_2, top.abella, debug,
              top.config)
      else ioval(io_action_2, error("Should not access (3)"));
  local duringed::(Integer, ProverState, FullDisplay) =
      io_action_3.iovalue;
  --After-proof commands
  local io_action_4::IOVal<(Integer, ProverState)> =
      if continueProcessing
      then runAfterProofCommands(duringed.2, io_action_3.io,
              top.abella, debug, top.config)
      else ioval(io_action_3.io, error("Should not access (4)"));
  local aftered::(Integer, ProverState) = io_action_4.iovalue;
  --Process any imported theorems we can now add
  local io_action_5::IOVal<(Integer, ProverState)> =
      if continueProcessing
      then runIncoming(aftered.2, io_action_4.io, top.abella,
                       debug, top.config)
      else ioval(io_action_4.io, error("Should not access (5)"));
  local nonErrorProverState::ProverState = io_action_5.iovalue.2;
  --Show to user
  ----------------------------
  local finalDisplay::FullDisplay = duringed.3;
  local width::Integer =
      if speak_to_abella || is_error
      then top.proverState.displayWidth
      else a.newProverState.displayWidth;
  production output_output::String =
      if speak_to_abella && continueProcessing
      then our_own_output ++
           decorateAndShow(new(finalDisplay),
              nonErrorProverState.knownTypes,
              nonErrorProverState.knownRels,
              nonErrorProverState.knownConstrs, width, true) ++ "\n"
      else our_own_output ++
           decorateAndShow(new(state), top.proverState.knownTypes,
              top.proverState.knownRels,
              top.proverState.knownConstrs, width, false) ++ "\n";
  local io_action_6::IOToken =
      if top.config.showUser
      then printT(output_output, io_action_5.io)
      else io_action_5.io;

  {-
    EXIT
  -}
  --this is outside the io_action numbering scheme because it doesn't
  --strictly happen in sync with the rest of them
  local exited::IOToken = exitAbella(a.toAbella, top.ioin,
                                     top.abella, debug, top.config);


  --Permit the addition of extra actions to be carried out after the
  --processing above
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;


  --finalIO is the IOToken for all this command's IO being done,
  --including any extra actions added apart from the basic sequence
  local finalIO::IOToken =
      io(if a.isQuit then exited else io_action_6);

  top.numAbellaCommands = length(a.toAbella) +
      if continueProcessing --only add others if they happened
      then duringed.1 + aftered.1 + io_action_5.iovalue.1
      else 0;

  rest.ioin = finalIO;
  rest.proverState =
       if speak_to_abella
       then nonErrorProverState
       else if is_error
       then top.proverState
       else a.newProverState;
  rest.priorStep =
       if speak_to_abella
       then if full_a.isError
            then top.priorStep --can't use this if this was bad
            else top
       else if is_error
       then top.priorStep --can't use this if this was bad
       else case a.newPriorStep of
            | nothing() -> top
            | just(s) -> s
            end;

  top.runResult =
      if top.config.runningFile
      then if is_error
           then ioval(printT("Could not process full file " ++
                         top.filename ++ ":\n" ++ our_own_output ++
                         "\n", finalIO), 1)
           else if full_a.isError
           then ioval(printT("Could not process full file " ++
                         top.filename ++ ":\n" ++
                         showDoc(top.proverState.displayWidth,
                                 full_a.pp),
                         finalIO), 1)
           else if a.isQuit && !rest.isNull
           then ioval(printT("Warning:  File contains Quit before " ++
                             "end\n", finalIO), 1)
           else rest.runResult
      else if a.isQuit
           then ioval(finalIO, 0)
           else if !is_error && fullUndo
           then expect_quit("Error:  After full undo, must have a " ++
                   "Quit command to finish", finalIO)
               --use unsafeTrace to force it to print output
           else unsafeTrace(rest.runResult, finalIO);
}



--Combine two IO actions into one
function combineIO
(IOToken ::= IOToken) ::= first::(IOToken ::= IOToken)
                          second::(IOToken ::= IOToken)
{
  return \ i::IOToken -> second(first(i));
}





{-
  Functions assisting in checking a file
-}

--Run any during commands that apply at this subgoal
function runDuringCommands
IOVal<(Integer, ProverState, FullDisplay)> ::=
   initProverState::ProverState displayIn::FullDisplay
   from_parse::Parser<FullDisplay_c> ioin::IOToken
   abella::ProcessHandle debug::Boolean config::Configuration
{
  local shouldClean::Boolean =
      --check for errors from given commands
      !displayIn.isError &&
      --and if we have any cleaning things to do right now
      case initProverState.duringCommands of
      | [] -> false
      | (sg, _)::_ -> sg == displayIn.proof.currentSubgoal
      end;
  local cleanCommands::[ProofCommand] =
      if shouldClean then head(initProverState.duringCommands).2
                     else [];
  local cleaned::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), cleanCommands), abella,
                       ioin, config);
  local cleaned_display::FullDisplay =
      processDisplay(cleaned.iovalue, from_parse);
  local outputCleanCommands::IOToken =
      if shouldClean
      then debugOutput(debug, config,
              cleanCommands,
              "Run During Commands",
              "(Cleaning commands were for Subgoal " ++
              subgoalNumToString(
                 head(initProverState.duringCommands).1) ++ ")\n\n" ++
               cleaned.iovalue, cleaned.io)
      else debugOutput(debug, config, cleanCommands,
              "Run During Commands", "", ioin);
  local cleanedState::ProverState =
      --(head(stateListIn).1 + length(cleanCommands),
      dropDuringCommand(setProofState(initProverState,
                                      cleaned_display.proof));
  --get the Extensibella version of the proof state
  local penultimateState::ProverState =
      if shouldClean then cleanedState else initProverState;
  local proofState::ProofState = penultimateState.state;
  proofState.typeEnv = initProverState.knownTypes;
  proofState.relationEnv = initProverState.knownRels;
  proofState.constructorEnv = initProverState.knownConstrs;
  return ioval(outputCleanCommands,
               (if shouldClean then length(cleanCommands) else 0,
                setProofState(penultimateState,
                              proofState.fromAbella),
                if shouldClean
                then ^cleaned_display
                else ^displayIn));
}


--Once a proof is done to Abella's satisfaction, do the after-proof
--commands needed for it
function runAfterProofCommands
IOVal<(Integer, ProverState)> ::=
   initProverState::ProverState ioin::IOToken abella::ProcessHandle
   debug::Boolean config::Configuration
{
  local proofDone::Boolean =
      case initProverState.state of
      | proofCompleted() -> true
      | _ -> false
      end;
  local runAfterCommands::Boolean =
      proofDone && !null(initProverState.afterCommands);
  local afterCommands::[AnyCommand] =
      if runAfterCommands then initProverState.afterCommands else [];
  local aftered::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), afterCommands), abella,
                       ioin, config);
  --don't parse aftered.iovalue---assume it worked
  local outputAfterCommands::IOToken =
      if runAfterCommands
      then debugOutput(debug, config, afterCommands,
              "After-Proof Commands", aftered.iovalue, aftered.io)
      else debugOutput(debug, config, afterCommands,
              "After-Proof Commands", "", ioin);

  --Put it together
  local newState::(Integer, ProverState) =
      (if runAfterCommands then length(afterCommands) else 0,
       finishProof(initProverState));
  return ioval(if runAfterCommands then outputAfterCommands else ioin,
               if proofDone then newState else (0, initProverState));
}


--If the proof is done, pass through any imported proof pieces that
--can now be done
function runIncoming
IOVal<(Integer, ProverState)> ::=
   stateIn::ProverState ioin::IOToken abella::ProcessHandle
   debug::Boolean config::Configuration
{
  local handleIncoming::([AnyCommand], ProverState) =
      if stateIn.state.inProof
      then ([], stateIn)
      else handleIncomingThms(stateIn);
  local incomingCommands::[AnyCommand] = handleIncoming.1;
  local incominged::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), incomingCommands), abella,
                       ioin, config);
  --don't parse incominged.iovalue---assume it worked
  local outputIncomingThms::IOToken =
      if !null(incomingCommands)
      then debugOutput(debug, config, incomingCommands,
              "Imported Theorems", incominged.iovalue, incominged.io)
      else debugOutput(debug, config, incomingCommands,
              "Imported Theorems", "", ioin);
  local completeState::(Integer, ProverState) =
      (length(handleIncoming.1), handleIncoming.2);
  return ioval(outputIncomingThms,
               if !null(incomingCommands)
               then completeState
               else (0, stateIn));
}


--Handle Abella exiting
function exitAbella
IOToken ::= commands::[AnyCommand] ioin::IOToken abella::ProcessHandle
            debug::Boolean config::Configuration
{
  local debug_output::IOToken =
      debugOutput(debug, config, commands, "User Commands",
                  "No Abella output because quitting", ioin);
  --We can't use our normal send/read function because that looks for
  --a new prompt at the end, and we won't have any
  local exit_out_to_abella::IOToken =
      sendToProcess(abella,
                    implode("\n", map((.abella_pp), commands)),
                    debug_output);
  local wait_on_exit::IOToken =
      waitForProcess(abella, exit_out_to_abella);
  --Guaranteed to get all the output because we waited for the process
  --to exit first
  local any_last_words::IOVal<String> =
      readAllFromProcess(abella, wait_on_exit);
  local output_last::IOToken =
      if config.showUser
      then printT(any_last_words.iovalue, any_last_words.io)
      else any_last_words.io;
  local exit_message::IOToken =
      if config.showUser
      then printT("Quitting.\n", output_last)
      else output_last;
  return exit_message;
}


--Parse a FullDisplay out of the string
--Assumes it succeeds, but gives a helpful error if it doesn't
function processDisplay
FullDisplay ::= s::String from_parse::Parser<FullDisplay_c>
{
  local p::ParseResult<FullDisplay_c> =
      from_parse(s, "<<Abella output>>");
  return if p.parseSuccess
         then p.parseTree.ast
         else error("Parse error in Abella output:\n\n" ++
                    s ++ "\n\n" ++ p.parseErrors);
}


--Display debugging output to the user, if you should
--commandReason is to explain whence the commands came
--   (e.g. after-theorem commands)
function debugOutput
attribute abella_pp {} occurs on command =>
IOToken ::= debug::Boolean config::Configuration commands::[command]
            commandReason::String abellaOutput::String ioin::IOToken
{
  local startString::String =
      "\n~~~~~~~~~~~~~~~~~~~~ Start " ++ commandReason ++
       " ~~~~~~~~~~~~~~~~~~~~\n\n";
  local commandString::String =
      if null(commands)
      then "<<< No Commands >>>"
      else implode("", map((.abella_pp), commands));
  local abellaString::String =
      "\n***** Abella Output *****\n" ++ abellaOutput;
  local endString::String =
      "\n\n~~~~~~~~~~~~~~~~~~~~ End " ++ commandReason ++
         " ~~~~~~~~~~~~~~~~~~~~\n\n";
  local full::String =
      startString ++ commandString ++
      (if null(commands) then "" else abellaString) ++
      endString;
  return if debug && config.showUser
         then printT(full, ioin)
         else ioin;
}


--Decorate here for efficiency, so it can throw away the decorated
--version after getting the show
function decorateAndShow
attribute typeEnv occurs on a,
attribute relationEnv occurs on a,
attribute constructorEnv occurs on a,
attribute fromAbella<a> {typeEnv, relationEnv, constructorEnv} occurs on a,
attribute pp {} occurs on a =>
String ::= a::a ty::Env<TypeEnvItem> rel::Env<RelationEnvItem>
           cons::Env<ConstructorEnvItem> width::Integer
           doFromAbella::Boolean
{
  a.typeEnv = ty;
  a.relationEnv = rel;
  a.constructorEnv = cons;
  return if doFromAbella
         then showDoc(width, a.fromAbella.pp)
         else showDoc(width, a.pp);
}
