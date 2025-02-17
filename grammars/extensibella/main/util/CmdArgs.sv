grammar extensibella:main:util;

imports silver:util:cmdargs;


--Process flags:
synthesized attribute filenames::[String] occurs on CmdArgs;

synthesized attribute displayHelp::Boolean occurs on CmdArgs;

synthesized attribute runsInteractive::Boolean occurs on CmdArgs;

--whether to run the REPL in the end (other options turn it off)
synthesized attribute runREPL::Boolean occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.filenames = l;

  top.displayHelp = false;

  top.runsInteractive = true;

  top.runREPL = true;
}


--Display the help WITHOUT an error message
abstract production helpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.filenames = rest.filenames;

  top.displayHelp = true;

  top.runREPL = rest.runREPL;

  forwards to @rest;
}



function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  production attribute flags::[FlagSpec] with ++;
  flags := [];

  production attribute debugFlags::[FlagSpec] with ++;
  debugFlags := [];

  --flags to display help without error message, but without being
  --part of the usage
  local helpFlags::[FlagSpec] =
      map(\ s::String ->
            flagSpec(name=s, paramString=nothing(),
                     help="display usage and exit",
                     flagParser=flag(helpFlag)),
          ["--help", "-help", "-h"]);

  local usage::String = 
        "Usage: extensibella [options] [filenames]\n\n" ++
        "Flag options:\n" ++ flagSpecsToHelpText(flags) ++ "\n" ++
        "Debug flag options:\n" ++ flagSpecsToHelpText(debugFlags) ++
        "\n";

  -- Parse the command line
  production a::CmdArgs =
      interpretCmdArgs(flags ++ debugFlags ++ helpFlags, args);

  production attribute errors::[String] with ++;
  errors := if a.cmdError.isJust then [a.cmdError.fromJust] else [];

  return if !null(errors)
         then left(implode("\n", errors) ++ "\n\n" ++ usage)
         else if a.displayHelp
         then left(usage)
         else right(a);
}
