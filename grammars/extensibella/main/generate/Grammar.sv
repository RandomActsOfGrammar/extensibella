grammar extensibella:main:generate;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:outerfaceFile;

imports extensibella:main:util;

imports silver:util:cmdargs;



--New command line flags

--module and filename to generate skeletons for and into
synthesized attribute generateFiles::[(QName, String)] occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.generateFiles = [];
}


--Display the help WITHOUT an error message
aspect production helpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.generateFiles = rest.generateFiles;
}


--Generate a file with the required imported theorems for proving
abstract production generateFlag
top::CmdArgs ::= moduleInfo::[String] rest::CmdArgs
{
  top.filenames = rest.filenames;
  top.generateFiles =
      case moduleInfo of
      | [mod, filename] ->
        (toQName(mod), filename)::rest.generateFiles
      | _ -> --should be checked by silver:util:cmdargs
        rest.generateFiles
      end;

  top.runREPL = false;

  top.displayHelp = rest.displayHelp;

  forwards to @rest;
}



aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--generate",
               paramString=just("<module> <filename>"),
               help="generate a basic theorem file for the given module",
               flagParser=nOptions(2, generateFlag))];

  errors <-
     if !null(a.generateFiles) && !null(a.filenames)
     then ["Can give generate XOR filenames, not both"]
     else [];
}
