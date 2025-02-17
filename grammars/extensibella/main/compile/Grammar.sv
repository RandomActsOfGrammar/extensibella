grammar extensibella:main:compile;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

imports extensibella:main:util;

imports silver:util:cmdargs;


--New command line flags

synthesized attribute compileFile::Boolean occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.compileFile = false;
}


--Display the help WITHOUT an error message
aspect production helpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.compileFile = rest.compileFile;
}


--Compile the file to allow its theorems to be discovered for modules
--   importing it
abstract production compileFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.compileFile = true;
  top.filenames = rest.filenames;

  top.runREPL = false;

  top.displayHelp = rest.displayHelp;

  forwards to @rest;
}



aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--compile",
               paramString=nothing(),
               help="compile file for importing into other modules",
               flagParser=flag(compileFlag))];

  errors <-
     if a.compileFile && null(a.filenames)
     then ["Must give filename(s) with --compile flag"]
     else [];
}
