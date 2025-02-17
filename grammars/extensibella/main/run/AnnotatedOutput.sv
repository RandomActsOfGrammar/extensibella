grammar extensibella:main:run;

{-
  Output nicely-formatted HTML of the interaction, including both
  commands and outputs, with each command having its own HTML element
  ID number (in order from the start)
-}

aspect function buildDecRunCommands
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
  cmds.cmdID = 1;
}

inherited attribute cmdID::Integer;

attribute
   cmdID
occurs on RunCommands;


aspect production addRunCommands
top::RunCommands ::= a::AnyCommand rest::RunCommands
{
  --Annotated HTML file with command and non-dying output
  io <- \ i::IOToken ->
          if top.config.outputAnnotated
          then appendFileT(top.config.annotatedFile,
                  --create block
                  "<pre class=\"code extensibella\"" ++
                       "id=\"" ++ toString(top.cmdID) ++ "\">\n" ++
                    --add prompt and command
                    " &lt; <b>" ++ stripExternalWhiteSpace(
                                      makeHTMLSafe(
                                         showDoc(80,
                                            nest(3, a.pp)))) ++
                          "</b>\n\n" ++
                    --Extensibella output
                    stripExternalWhiteSpace(
                       makeHTMLSafe(output_output)) ++ "\n" ++
                  --end block
                  "</pre>\n",
                  i)
          else i;

  rest.cmdID = top.cmdID + 1;
}


aspect function get_module_interactive
IOVal<Maybe<(QName, ListOfCommands, [DefElement], [ThmElement],
             [(QName, [QName])])>> ::=
   parsers::AllParsers config::Configuration ioin::IOToken
{
  --Annotated output
  io <- \ i::IOToken ->
          if config.outputAnnotated
          then appendFileT(config.annotatedFile,
                  --create block
                  "<pre class=\"code extensibella\">\n" ++
                    --add prompt and user input
                    " &lt; <b>" ++ makeHTMLSafe(input) ++
                          "</b>\n\n" ++
                    --add output
                    stripExternalWhiteSpace(makeHTMLSafe(output)) ++
                  --end block
                  "</pre>\n",
                  i)
          else i;
}


aspect function run_file
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken filename::String
                   config::Configuration
{
  --output the module declaration in the annotated file
  io <- \ i::IOToken ->
          if config.outputAnnotated
          then appendFileT(config.annotatedFile,
                  --create block
                  "<pre class=\"code extensibella\">\n" ++
                    --add prompt and module declaration (no output)
                    --module name had best be fairly short
                    " < <b>Module " ++
                      makeHTMLSafe(justShow(fileAST.1.fromJust.pp)) ++
                      ".</b>\n" ++
                  --end block
                  "</pre>\n",
                  i)
          else i;
}




{-
  In the HTML output, the extension size and projection versions of a
  relation are disappearing because they are treated as tags.  This
  replaces the literal "<" and ">" with HTML-safe versions.
-}
function makeHTMLSafe
String ::= s::String
{
  return substitute("<", "&lt;", substitute(">", "&gt;", s));
}





--whether the Extensibella commands and output should be placed in the
--given file
synthesized attribute outputAnnotated::Boolean occurs on CmdArgs;
synthesized attribute annotatedFile::String occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.outputAnnotated = false;
  top.annotatedFile =
      error("Shouldn't access annotatedFile if outputAnnotated = false");
}


--Output an HTML version of the commands with the Extensibella output
abstract production annotatedOutputFlag
top::CmdArgs ::= name::String rest::CmdArgs
{
  --if there are files, this requires checking
  top.checkFile = rest.checkFile || !null(rest.filenames);
  top.filenames = rest.filenames;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  top.displayHelp = rest.displayHelp;

  top.outputAnnotated = true;
  top.annotatedFile = name;

  top.runREPL = false;

  forwards to @rest;
}


aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--annotate",
               paramString=just("<filename>"),
               help="output an HTML version of the interaction",
               flagParser=option(annotatedOutputFlag))];

  errors <-
     if a.outputAnnotated && length(a.filenames) > 1
     then ["Can only check one file with annotated HTML output; " ++
           "multiple files would all be in the same HTML file"]
     else [];
}
