grammar extensibella:genStdLibDocs;

{-
  Process the standard library definitions into a documentation file
  that can be read by a person familiar with Extensibella, without
  needing to recognize the details of the Abella encoding
-}

imports silver:langutil:pp;
imports silver:langutil only pp, pps;

imports extensibella:common:abstractSyntax;
imports extensibella:toAbella:abstractSyntax;
imports extensibella:fromAbella:abstractSyntax;

imports extensibella:common:concreteSyntax;
imports extensibella:toAbella:concreteSyntax;

imports silver:util:cmdargs;

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  local parseResult::Either<String Decorated CmdArgs> = parseArgs(largs);
  local parsedArgs::Decorated CmdArgs = parseResult.fromRight;

  production attribute outputTypes::[DocOutputType] with ++;
  outputTypes := [
      docOutputType(docFormatFull = formatMarkdownFull,
                    docFormatFile = formatMarkdownFile,
                    docFormatThm = formatMarkdownThm,
                    tag = "Markdown",
                    outputDoc = \ a::Decorated CmdArgs -> a.doMarkdown,
                    docFilename = \ a::Decorated CmdArgs -> a.markdownFilename),
      docOutputType(docFormatFull = formatHtmlFull,
                    docFormatFile = formatHtmlFile,
                    docFormatThm = formatHtmlThm,
                    tag = "HTML",
                    outputDoc = \ a::Decorated CmdArgs -> a.doHTML,
                    docFilename = \ a::Decorated CmdArgs -> a.htmlFilename)
     ];

  local out::IOToken =
      foldr(\ d::DocOutputType rest::IOToken ->
              if d.outputDoc(parsedArgs)
              then let str::IOVal<String> =
                       processAllFiles(d.docFormatFull, d.docFormatFile,
                          d.docFormatThm, d.tag, rest)
                   in
                     writeFileT(d.docFilename(parsedArgs),
                                str.iovalue, str.io)
                   end
              else rest,
            ioin, outputTypes);

  return case parseResult of
         | left(msg) -> ioval(printT(msg, ioin), 0)
         | right(_) -> ioval(out, 0)
         end;
}


data nonterminal DocOutputType with
   docFormatFull, docFormatFile, docFormatThm,
   tag, outputDoc, docFilename;
--how to format a full set of files (list of files)
annotation docFormatFull::(String ::= [String]);
--how to format a single file (filename, thms all concatenated)
annotation docFormatFile::(String ::= String String);
--how to format a theorem (name, type params, body)
annotation docFormatThm::(String ::= QName [String] Metaterm);
--a name for the output type
annotation tag::String;
--whether to do this output type
annotation outputDoc::(Boolean ::= Decorated CmdArgs);
--get the output filename for this output type
annotation docFilename::(String ::= Decorated CmdArgs);
abstract production docOutputType top::DocOutputType ::= { }





{--------------------------------------------------------------------
                        Command Line Arguments
 --------------------------------------------------------------------}
synthesized attribute doMarkdown::Boolean;
synthesized attribute doHTML::Boolean;

synthesized attribute markdownFilename::String;
synthesized attribute htmlFilename::String;

synthesized attribute doHelp::Boolean;

attribute
   doMarkdown, doHTML,
   markdownFilename, htmlFilename,
   doHelp
occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.doMarkdown = false;
  top.doHTML = false;

  top.markdownFilename = "stdLibDoc.md";
  top.htmlFilename = "stdLibDoc.html";

  top.doHelp = false;
}


abstract production markdownFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.doMarkdown = true;
  top.doHTML = rest.doHTML;

  top.markdownFilename = rest.markdownFilename;
  top.htmlFilename = rest.htmlFilename;

  top.doHelp = rest.doHelp;

  forwards to ^rest;
}


abstract production htmlFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.doMarkdown = rest.doMarkdown;
  top.doHTML = true;

  top.markdownFilename = rest.markdownFilename;
  top.htmlFilename = rest.htmlFilename;

  top.doHelp = rest.doHelp;

  forwards to ^rest;
}


abstract production markdownFilenameFlag
top::CmdArgs ::= name::String rest::CmdArgs
{
  top.doMarkdown = true;
  top.doHTML = rest.doHTML;

  top.markdownFilename = name;
  top.htmlFilename = rest.htmlFilename;

  top.doHelp = rest.doHelp;

  forwards to ^rest;
}


abstract production htmlFilenameFlag
top::CmdArgs ::= name::String rest::CmdArgs
{
  top.doMarkdown = rest.doMarkdown;
  top.doHTML = true;

  top.markdownFilename = rest.markdownFilename;
  top.htmlFilename = name;

  top.doHelp = rest.doHelp;

  forwards to ^rest;
}


abstract production helpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.doMarkdown = rest.doMarkdown;
  top.doHTML = rest.doHTML;

  top.markdownFilename = rest.markdownFilename;
  top.htmlFilename = rest.htmlFilename;

  top.doHelp = true;

  forwards to ^rest;
}



function parseArgs
Either<String Decorated CmdArgs> ::= args::[String]
{
  --Processing flags
  production attribute flags::[FlagSpec] with ++;
  flags :=
     [flagSpec(name="--markdown",
               paramString=nothing(),
               help="output documentation to Markdown",
               flagParser=flag(markdownFlag)),
      flagSpec(name="--html",
               paramString=nothing(),
               help="output documentation to HTML",
               flagParser=flag(htmlFlag)),
      flagSpec(name="--markdownFile",
               paramString=just("<filename>"),
               help="name for Markdown documentation file",
               flagParser=option(markdownFilenameFlag)),
      flagSpec(name="--htmlFile",
               paramString=just("<filename>"),
               help="name for HTML documentation file",
               flagParser=option(htmlFilenameFlag)),
      flagSpec(name="--help",
               paramString=nothing(),
               help="output commandline help message",
               flagParser=flag(helpFlag))
     ];

  local usage::String = "Flag options:\n" ++ flagSpecsToHelpText(flags);

  --Parse the command line
  production a::CmdArgs = --add "-h" for help
      interpretCmdArgs(flagSpec(name="-h", paramString=nothing(),
                                help="", flagParser=flag(helpFlag))::flags, args);
  return if a.cmdError.isJust
         then left(a.cmdError.fromJust ++ "\n")
         else if a.doHelp
         then left(usage)
         else right(a);
}





{--------------------------------------------------------------------
                           File Processing
 --------------------------------------------------------------------}
parser file_parse::ListOfCommands_c
{
  extensibella:toAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}


--Read all the .thm files in the current directory and gather up their
--documentation into a single string
function processAllFiles
IOVal<String> ::= formatFull::(String ::= [String])
                  formatFile::(String ::= String String)
                  formatThm::(String ::= QName [String] Metaterm)
                  tag::String ioin::IOToken
{
  local printStart::IOToken =
      printT("\nProcessing files for " ++ tag ++
             " documentation...", ioin);

  --Get all files
  local dir::IOVal<String> = cwdT(printStart);
  local dirContents::IOVal<[String]> =
      listContentsT(dir.iovalue, dir.io);
  local thmFiles::[String] =
      filter(\ s::String -> splitFileNameAndExtension(s).2 == "thm",
             dirContents.iovalue);

  --Get their documentation
  local markdowns::IOVal<[String]> =
      foldr(\ filename::String rest::IOVal<[String]> ->
              let here::IOVal<String> =
                  processFile(filename, formatFile, formatThm, rest.io)
              in
                ioval(here.io, 
                      if isSpace(here.iovalue)
                      then rest.iovalue
                      else here.iovalue::rest.iovalue)
              end,
            ioval(dirContents.io, []), thmFiles);
  local full::String = formatFull(markdowns.iovalue);

  local printEnd::IOToken = printT("Done\n", markdowns.io);
  return ioval(printEnd, full);
}


--Process a single file to get its markdown output
--Assumes the file will exist and parse
function processFile
IOVal<String> ::= filename::String
                  formatFile::(String ::= String String)
                  formatThm::(String ::= QName [String] Metaterm)
                  ioin::IOToken
{
  --Get the file contents and set up to grab the doc string
  local contents::IOVal<String> = readFileT(filename, ioin);
  local parsed::ParseResult<ListOfCommands_c> =
      file_parse(contents.iovalue, filename);
  --to get the basic, initial envs
  local basicProverState::ProverState =
      defaultProverState([], buildEnv([]), buildEnv([]),
                         buildEnv([]), [], [], []);
  local ast::ListOfCommands = parsed.parseTree.ast;
  ast.typeEnv = basicProverState.knownTypes;
  ast.constructorEnv = basicProverState.knownConstrs;
  ast.relationEnv = basicProverState.knownRels;
  ast.currentModule = toQName("extensibella:stdLib");
  ast.proverState = basicProverState;
  ast.ignoreDefErrors = true;
  --
  ast.formatThm = formatThm;

  --Make the filename pretty for the user
  local baseFilename::String =
      splitFileNameAndExtension(filename).1;
  local splitWords::[String] = explode("_", baseFilename);
  local adjustedFilename::String =
      implode(" ", map(capitalizeString, splitWords));

  --Put it together
  local docString::String = --assumes filename is prettified
      formatFile(adjustedFilename, ast.docString);
  return ioval(contents.io, docString);
}





{--------------------------------------------------------------------
                           Format Markdown
 --------------------------------------------------------------------}
function formatMarkdownThm
String ::= name::QName params::[String] body::Metaterm
{
  local pString::String =
      if null(params)
      then ""
      else " `[" ++ implode(", ", params) ++ "]`";
  local startString::String =
      "* `" ++ name.shortName ++ "` " ++ pString;
  local bodyString::String =
      "\n  ```\n  " ++ justShow(body.pp) ++ "\n  ```";
  return startString ++ " : " ++ bodyString ++ "\n";
}

function formatMarkdownFile
String ::= filename::String thmDocs::String
{
  return if isSpace(thmDocs)
         then ""
         else "## " ++ filename ++ "\n" ++ thmDocs;
}

function formatMarkdownFull
String ::= fileDocs::[String]
{
  return "# Extensibella Standard Library\n" ++
         "All theorems are part of the `extensibella:stdLib` " ++
         "reasoning module.  Then, for example, the full name of " ++
         "the theorem listed below as `plus_integer_unique` is " ++
         "`extensibella:stdLib:plus_integer_unique`. \n\n" ++
         implode("\n\n", fileDocs);
}





{--------------------------------------------------------------------
                             Format HTML
 --------------------------------------------------------------------}
function formatHtmlThm
String ::= name::QName params::[String] body::Metaterm
{
  local pString::String =
      if null(params)
      then ""
      else " [" ++ implode(", ", params) ++ "]";
  local startString::String =
      "\n<li> <code>" ++ name.shortName ++ pString ++ "</code>";
  local bodyString::String =
      "<pre class=\"code extensibella\">" ++ show(100, body.pp) ++
      "</pre>";
  return startString ++ " : " ++ bodyString;
}

function formatHtmlFile
String ::= filename::String thmDocs::String
{
  return if isSpace(thmDocs)
         then ""
         else "<div class=\"section\">\n" ++
              "<h2>" ++ filename ++ "</h2>\n" ++
              "<ul>" ++ thmDocs ++ "\n</ul>\n</div>\n";
}

function formatHtmlFull
String ::= fileDocs::[String]
{
  return "<html>\n" ++
         "<body>\n" ++
         "<div class=\"section\">\n" ++
         "<h1>Extensibella Standard Library</h1>\n" ++
         "<p>All theorems are part of the <tt>extensibella:stdLib</tt> " ++
         "reasoning module.  Then, for example, the full name of the " ++
         "theorem listed below as <tt>plus_integer_unique</tt> is " ++
         "<tt>extensibella:stdLib:plus_integer_unique</tt>.</p>\n" ++
         "</div>\n\n" ++
         implode("\n\n", fileDocs) ++
         "</body>\n" ++
         "</html>\n";
}





{--------------------------------------------------------------------
                         Build Documentation
 --------------------------------------------------------------------}
inherited attribute formatThm::(String ::= QName [String] Metaterm);
synthesized attribute docString::String;

attribute
   formatThm, docString
occurs on ListOfCommands;
propagate formatThm on ListOfCommands;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.docString = "";
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.docString = a.docString ++ rest.docString;
}



attribute
   formatThm, docString
occurs on AnyCommand;
propagate formatThm on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.docString = c.docString;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.docString = "";
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.docString =
      if c.isQuit then error("Should not find Quit") else "";
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.docString = error("Should not find parse failures");
}



attribute
   formatThm, docString
occurs on TopCommand;
propagate formatThm on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.docString =
      if name.isQualified --assume qualification is the stdLib one
      then top.formatThm(^name, params, body.fromAbella)
      else "";

  local markdown::String =
      "* `" ++ justShow(name.pp) ++ 
      (if null(params) then ""
                       else "[" ++ implode(", ", params) ++ "]") ++
      "`:  `" ++ justShow(body.fromAbella.pp) ++ "`\n";
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.docString = "";
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.docString = "";
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.docString = "";
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.docString =
      foldr(\ p::(QName, Metaterm) rest::String ->
              if p.1.isQualified
              then top.formatThm(p.1, [], p.2) ++ rest
              else rest,
            "", zipped);

  local zipped::[(QName, Metaterm)] =
      case thm of
      | [_] -> zip(newTheoremNames, splitThm)
      | _ -> []
      end;
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.docString = "";
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.docString = "";
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.docString = "";
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.docString = "";
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.docString = error("Should not occur");
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.docString = error("Should not occur");
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.docString = error("Should not occur");
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.docString = error("Should not occur");
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.docString = error("Should not occur");
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.docString = error("Should not occur");
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.docString = error("Should not occur");
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.docString = error("Should not occur");
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.docString = error("Should not occur");
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.docString = error("Should not occur");
}
