grammar extensibella:main:compose;

imports extensibella:common;
imports extensibella:fromAbella;
imports extensibella:toAbella;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

imports extensibella:main:util;
imports extensibella:main:run;
imports extensibella:main;

imports silver:util:cmdargs;

imports silver:util:subprocess;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;


--New command line flag
synthesized attribute composeFile::Boolean occurs on CmdArgs;
synthesized attribute composeFilename::String occurs on CmdArgs;
synthesized attribute composeModuleName::String occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.composeFile = false;
  top.composeFilename =
      error("Should not access composeFilename when composeFile is false");
  top.composeModuleName =
      error("Should not access composeModuleName when composeFile is false");
}


abstract production composeFlag
top::CmdArgs ::= args::[String] rest::CmdArgs
{
  top.composeFile = true;
  top.composeFilename = head(args);
  top.composeModuleName = head(tail(args));

  top.runsInteractive = false;

  top.runREPL = false;

  forwards to @rest;
}



aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--compose",
               paramString=just("<output filename> <module name>"),
               help="compose listed files into a single Abella proof",
               flagParser=nOptions(2, composeFlag))];

  errors <-
     if a.composeFile && null(a.filenames)
     then ["Must give filename(s) with --compose flag"]
     else [];
}
