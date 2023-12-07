grammar extensibella:main:compose;

type DecCmds = Decorated ListOfCommands;

function compose_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  local composeModule::QName = toQName(config.composeModuleName);

  local genDirs::IOVal<[String]> = getGenDirs(ioin);

  --interface file to know the modules we should have
  local interfaceFileLoc::IOVal<Maybe<String>> =
      findFile(composeModule.interfaceFileName, genDirs.iovalue, genDirs.io);
  local interfaceFileContents::IOVal<String> =
      readFileT(interfaceFileLoc.iovalue.fromJust, interfaceFileLoc.io);
  local parsedMods::ParseResult<ModuleList_c> =
      parsers.interface_parse(interfaceFileContents.iovalue,
                              interfaceFileLoc.iovalue.fromJust);
  local expectedMods::[QName] =
      parsedMods.parseTree.ast.mods ++
      --add because interface file doesn't include the module itself
      [composeModule];

  --definition file
  --we only need to read its contents; we will assume it is correct without parsing
  local composedDefFileLoc::IOVal<Maybe<String>> =
      findFile(composeModule.composedFileName, genDirs.iovalue,
               interfaceFileContents.io);
  local defFileContents::IOVal<String> =
      readFileT(composedDefFileLoc.iovalue.fromJust, composedDefFileLoc.io);

  --gather modules and check the right ones are there
  local gathered::IOVal<Either<String [(QName, String, DecCmds)]>> =
      gatherProofFiles(parsers, config, config.filenames, defFileContents.io);
  local checkMods::Either<String [(QName, DecCmds)]> =
      checkModulesMatch(expectedMods, gathered.iovalue.fromRight);

  --build and write the file, now that everything has checked out
  local createComposedFile::IOVal<Integer> =
      build_composed_file(config.composeFilename, defFileContents.iovalue,
                          checkMods.fromRight, gathered.io);

  return
      --interface errors
      if !interfaceFileLoc.iovalue.isJust
      then ioval(printT("Could not find interface file for module " ++
                        justShow(composeModule.pp) ++
                        "; must compile module first",
                        interfaceFileLoc.io), 1)
      else if !parsedMods.parseSuccess
      then ioval(printT("Could not parse interface file for module" ++
                        justShow(composeModule.pp) ++ ":\n" ++
                        parsedMods.parseErrors ++ "\n",
                        interfaceFileContents.io), 1)
      --definition errors
      else if !composedDefFileLoc.iovalue.isJust
      then ioval(printT("Could not find composed definition file for module " ++
                        justShow(composeModule.pp) ++
                        "; must compile module for composition first",
                        composedDefFileLoc.io), 1)
      --module gathering and checking errors
      else if !gathered.iovalue.isRight
      then ioval(printT(gathered.iovalue.fromLeft, gathered.io), 1)
      else if !checkMods.isRight
      then ioval(printT(checkMods.fromLeft, gathered.io), 1)
      else createComposedFile;
}


--gather the executed proof files by module name
function gatherProofFiles
IOVal<Either<String [(QName, String, DecCmds)]>> ::=
   parsers::AllParsers config::Configuration filenames::[String]
   ioin::IOToken
{
  local filename::String = head(filenames);

  --initial set-up for file
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement]))>> =
      processFile(filename, parsers, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement]) =
      fileInfo.iovalue.fromRight.snd;

  --run it
  local runFile::Either<IOVal<String>  DecCmds> =
      buildDecRunCommands(filename, fileAST.2, parsers, fileAST.1.fromJust,
         processed.1, processed.2, processed.3, config, fileInfo.io);
  local runIO::IOToken = --pull out an IOToken
      case runFile of
      | left(errIO) -> errIO.io
      | right(cmds) -> cmds.runResult.io
      end;

  --do it all again
  local rest::IOVal<Either<String [(QName, String, DecCmds)]>> =
      gatherProofFiles(parsers, config, tail(filenames), runIO);

  return case filenames of
         | [] -> ioval(ioin, right([]))
         | _::_ ->
           if !fileInfo.iovalue.isRight
           then ioval(fileInfo.io,
                      left("Error processing file " ++ filename ++
                           ":  "  ++ fileInfo.iovalue.fromLeft ++ "\n"))
           else case runFile of
                | left(errIO) ->
                  ioval(errIO.io,
                        left("Error processing file " ++ filename ++
                             ":  " ++ errIO.iovalue ++ "\n"))
                | right(cmds) ->
                  if cmds.runResult.iovalue != 0
                  then ioval(cmds.runResult.io,
                             left("File " ++ filename ++ " is not valid\n"))
                  else ioval(rest.io,
                             case rest.iovalue of
                             | left(x) -> left(x)
                             | right(l) ->
                               right((fileAST.1.fromJust, filename, cmds)::l)
                             end)
                end
         end;
}


{-
  Check the expected modules and found modules match; it is an error
  if there is not a one-to-one mapping between them
  @param expectedMods  modules that should be present
  @param foundMods  parsed and run files given by user
  @return  error message, if there is an error, or re-ordered file list
-}
function checkModulesMatch
Either<String [(QName, DecCmds)]> ::= expectedMods::[QName]
                                      foundMods::[(QName, String, DecCmds)]
{
  local allFiles::[(String, DecCmds)] =
      lookupAll(head(expectedMods), foundMods);
  local removeFiles::[(QName, String, DecCmds)] =
      filter(\ p::(QName, String, DecCmds) -> p.1 != head(expectedMods),
             foundMods);

  return
      case expectedMods, foundMods of
      --successfully finished
      | [], [] -> right([])
      --out of modules, extra files
      | [], [(q, f, c)] -> left("Extra proof file " ++ f ++ "\n")
      | [], l ->
        left("Extra proof files " ++
             implode(", ", map(\ p::(QName, String, DecCmds) -> p.2, l)) ++ "\n")
      --no more files for modules
      | [m], [] -> left("Missing proof file for module " ++ justShow(m.pp) ++ "\n")
      | l, [] ->
        left("Missing proof files for modules " ++
             implode(", ", map(\ m::QName -> justShow(m.pp), l)) ++ "\n")
      --step
      | m::tl, _::_ ->
        case allFiles of
        | [] -> left("Missing proof file for module " ++ justShow(m.pp) ++ "\n")
        | [(f, c)] -> bind(checkModulesMatch(tl, removeFiles),
                           \ l::[(QName, DecCmds)] -> right((m, c)::l))
        | l ->
          left("Multiple proof files for module " ++ justShow(m.pp) ++ ":  " ++
               implode(", ", map(\ p::(String, DecCmds) -> p.1, l)) ++ "\n")
        end
      end;
}


--
function build_composed_file
IOVal<Integer> ::= outFilename::String defFileContents::String
                   mods::[(QName, DecCmds)] ioin::IOToken
{
  --Extensibella standard library
  local stdLib::IOVal<[String]> = extensibellaStdLibAbellaCmds(ioin);
  local stdLibString::String =
      "/********************************************************************\n" ++
      " Extensibella Standard Library\n" ++
      " ********************************************************************/\n" ++
      implode("\n", stdLib.iovalue) ++ "\n\n\n";

  --language definition
  local langDefString::String =
      "/********************************************************************\n" ++
      " Language Definition\n" ++
      " ********************************************************************/\n" ++
      defFileContents ++ "\n\n\n";

  --properties and proofs
  local propertyString::String =
      "/********************************************************************\n" ++
      " Properties and Proofs\n" ++
      " ********************************************************************/\n";

  --put it all together
  local fullString::String = stdLibString ++ langDefString ++ propertyString;
  local output::IOToken =
      printT("Done\n",
             writeFileT(outFilename, fullString,
                        printT("Writing " ++ outFilename ++ "...", stdLib.io)));

  return ioval(output, 1);
}
