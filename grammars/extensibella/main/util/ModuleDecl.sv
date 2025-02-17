grammar extensibella:main:util;

imports silver:langutil:pp only showDoc;
imports silver:langutil only pp;


--Read the interface file for a module
function processModuleDecl
IOVal<Either<String
             (ListOfCommands, [DefElement], [ThmElement],
              [(QName, [QName])])>> ::=
   moduleName::QName parsers::AllParsers ioin::IOToken
{
  local gen_dirs::IOVal<[String]> = getGenDirs(ioin);

  --Read interface file
  local interface_file::IOVal<Maybe<String>> =
      findFile(moduleName.interfaceFileName, gen_dirs.iovalue,
               gen_dirs.io);
  local interface_file_contents::IOVal<String> =
      readFileT(interface_file.iovalue.fromJust,
                interface_file.io);
  local parsed_interface::ParseResult<ModuleList_c> =
      parsers.interface_parse(interface_file_contents.iovalue,
                      interface_file.iovalue.fromJust);
  local interface::ImportedModuleList =
      parsed_interface.parseTree.ast;

  --Read imported outerface files
  local outerface::IOVal<Either<String ([DefElement], [ThmElement])>> =
      readOuterfaces(interface.mods, parsers, gen_dirs.iovalue,
                     interface_file_contents.io);

  --Read definition file
  local definition_file::IOVal<Maybe<String>> =
      findFile(moduleName.definitionFileName, gen_dirs.iovalue,
               outerface.io);
  local definition_file_contents::IOVal<String> =
      readFileT(definition_file.iovalue.fromJust,
                definition_file.io);
  local parsed_definition::ParseResult<ListOfCommands_c> =
      parsers.import_parse(definition_file_contents.iovalue,
                   definition_file.iovalue.fromJust);
  local definition::ListOfCommands = parsed_definition.parseTree.ast;

  --put it together
  return
     --interface errors
     if !interface_file.iovalue.isJust
     then ioval(interface_file.io,
                left("Could not find interface file for module " ++
                     justShow(moduleName.pp) ++
                     "; must compile module first"))
     else if !parsed_interface.parseSuccess
     then ioval(interface_file_contents.io,
                left("Could not parse interface file for module " ++
                     justShow(moduleName.pp) ++ ":\n" ++
                     parsed_interface.parseErrors ++ "\n"))
     --outerface errors
     else if !outerface.iovalue.isRight
     then ioval(outerface.io, left(outerface.iovalue.fromLeft))
     --definition errors
     else if !definition_file.iovalue.isJust
     then ioval(definition_file.io,
                left("Could not find definition file for module " ++
                     justShow(moduleName.pp) ++
                     "; must compile module first"))
     else if !parsed_definition.parseSuccess
     then ioval(definition_file_contents.io,
                left("Could not parse definition file for module " ++
                     justShow(moduleName.pp) ++ ":\n" ++
                     parsed_definition.parseErrors ++ "\n"))
     --success
     else ioval(definition_file_contents.io,
                right((^definition, outerface.iovalue.fromRight.1,
                       outerface.iovalue.fromRight.2,
                       --add this module to it
                       (^moduleName, interface.mods)::interface.buildsOns)));
}


--read in and process all the outerface files
function readOuterfaces
IOVal<Either<String ([DefElement], [ThmElement])>> ::=
   mods::[QName] parsers::AllParsers gen_dirs::[String] ioin::IOToken
{
  local outerfaceFiles::IOVal<[Either<QName (QName, String)>]> =
      foldr(\ q::QName rest::IOVal<[Either<QName (QName, String)>]> ->
              let mf::IOVal<Maybe<String>> =
                  findFile(q.outerfaceFileName, gen_dirs, rest.io)
              in
                ioval(mf.io, case mf.iovalue of
                             | just(f) -> right((q, f))::rest.iovalue
                             | nothing() -> left(q)::rest.iovalue
                             end)
              end,
            ioval(ioin, []), mods);
  local findOuterfaceFileErrors::[QName] =
      flatMap(\ e::Either<QName (QName, String)> ->
                case e of
                | right(_) -> []
                | left(q) -> [q]
                end, outerfaceFiles.iovalue);
  local outerfaceFilenames::[(QName, String)] =
      flatMap(\ e::Either<QName (QName, String)> ->
                case e of
                | right(p) -> [p]
                | left(_) -> []
                end, outerfaceFiles.iovalue);
  local outerfaces::IOVal<[(QName, Outerface)]> =
      foldr(\ p::(QName, String) rest::IOVal<[(QName, Outerface)]> ->
              let contents::IOVal<String> =
                  readFileT(p.2, rest.io)
              in
              let parsed::ParseResult<Outerface_c> =
                  parsers.outerface_parse(contents.iovalue, p.2)
              in
                if !parsed.parseSuccess
                then error("Could not parse outerface file " ++
                        p.2 ++ ":\n" ++ parsed.parseErrors)
                else ioval(contents.io,
                           (p.1, parsed.parseTree.ast)::rest.iovalue)
              end end,
            ioval(outerfaceFiles.io, []), outerfaceFilenames);
  local outerface::([DefElement], [ThmElement]) =
      processModuleOuterfaces(outerfaces.iovalue);

  return if !null(findOuterfaceFileErrors)
         then ioval(outerfaceFiles.io,
                 left("Could not find outerface " ++
                    (if length(findOuterfaceFileErrors) == 1
                     then "file for module " ++
                          justShow(head(findOuterfaceFileErrors).pp)
                     else "files for modules " ++
                          implode(", ", map(justShow,
                             map((.pp), findOuterfaceFileErrors)))) ++
                    "; must compile first"))
         else ioval(outerfaces.io, right(outerface));
}


--Get the actual definitions out of def elements to add to the context
function defElementsDefinitions
--(types, rels, constrs, groups of mutually-defined relations
([TypeEnvItem], [RelationEnvItem], [ConstructorEnvItem], [[QName]]) ::=
   elems::[DefElement]
{
  local defs::ListOfCommands =
      foldr(addListOfCommands, emptyListOfCommands(),
            flatMap((.encode), elems));
  defs.typeEnv = buildEnv([]);
  defs.relationEnv = buildEnv([]);
  defs.constructorEnv = buildEnv([]);
  defs.currentModule = error("defElementsDefinitions.currentModule");
  defs.ignoreDefErrors = true;
  defs.proverState = error("defElementsDefinitions.proverState");
  return (defs.tys, defs.rels, defs.constrs, defs.newMutualRelGroups);
}


--Read in theorems from the standard library
function importStdLibThms
IOVal<Either<String [(QName, Metaterm)]>> ::=
      parsers::AllParsers ioin::IOToken
{
  local stdLibFiles::IOVal<Either<String [String]>> =
      standardLibraryFiles(ioin);
  local read::IOVal<Either<String [(QName, Metaterm)]>> =
      readStdLibThms(stdLibFiles.iovalue.fromRight, parsers,
                     stdLibFiles.io);
  return
     case stdLibFiles.iovalue of
     | left(err) -> ioval(stdLibFiles.io, left(err))
     | right(_) -> ioval(read.io, read.iovalue)
     end;
}


--Find all the library files, with their full path
--Does not include file extensions
function standardLibraryFiles
IOVal<Either<String [String]>> ::= ioin::IOToken
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
      envVarT("EXTENSIBELLA_LIBRARY", ioin);
  --filenames for the standard library
  local baseFiles::[String] =
      ["bools", "integers", "integer_addition", "integer_multiplication",
       "integer_division", "integer_comparison", "lists", "strings",
       "pairs", "extSize_induction"];
  local fullFilenames::[String] =
      map(\ filename::String -> library_loc.iovalue ++ filename,
          baseFiles);
  return
     ioval(library_loc.io,
           if library_loc.iovalue == ""
           then left("Interface library location not set; " ++
                     "must run through given script")
           else right(fullFilenames));
}


--Read all the given files, getting their theorems
function readStdLibThms
IOVal<Either<String [(QName, Metaterm)]>> ::=
      filenames::[String] parsers::AllParsers ioin::IOToken
{
  local contents::IOVal<String> =
      readFileT(head(filenames) ++ ".thm", ioin);
  local parsed::ParseResult<ListOfCommands_c> =
      parsers.import_parse(contents.iovalue, head(filenames) ++ ".thm");
  local ast::ListOfCommands = parsed.parseTree.ast;
  ast.currentModule = toQName("extensibella:stdLib");
  ast.proverState = error("proverState not needed");
  ast.ignoreDefErrors = true;
  ast.typeEnv = error("typeEnv not needed");
  ast.relationEnv = error("relationEnv not needed");
  ast.constructorEnv = error("constructorEnv not needed");
  local again::IOVal<Either<String [(QName, Metaterm)]>> =
      readStdLibThms(tail(filenames), parsers, contents.io);
  return
     case filenames of
     | [] -> ioval(ioin, right([]))
     | f::_ when !parsed.parseSuccess ->
       ioval(contents.io,
             left("Could not parse file " ++ f ++ ".thm:\n" ++
                  parsed.parseErrors))
     | _::_ when again.iovalue.isLeft ->
       ioval(again.io, again.iovalue)
     | _::_ ->
       ioval(again.io,
             right(ast.declaredThms ++ again.iovalue.fromRight))
     end;
}
