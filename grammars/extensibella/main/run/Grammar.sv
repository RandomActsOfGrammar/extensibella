grammar extensibella:main:run;

imports extensibella:common;
imports extensibella:fromAbella;
imports extensibella:toAbella;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

imports extensibella:main:util;

imports silver:util:cmdargs;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;


--New command line flags

synthesized attribute checkFile::Boolean occurs on CmdArgs;

--whether we are running a file or interactive
synthesized attribute runningFile::Boolean occurs on CmdArgs;
--whether the user should see output
synthesized attribute showUser::Boolean occurs on CmdArgs;

--whether the Abella commands should be placed in the given file
--   Useful for debugging when the translation is wrong
synthesized attribute dumpAbella::Boolean occurs on CmdArgs;
synthesized attribute dumpAbellaFile::String occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.checkFile = false;

  top.runningFile = !null(l);
  top.showUser = null(l);

  top.dumpAbella = false;
  top.dumpAbellaFile =
      error("Shouldn't access dumpAbellaFile if dumpAbella = false");
}


--Display the help WITHOUT an error message
aspect production helpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = rest.checkFile;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;
}


--Check the file for correctness
abstract production checkFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = true;
  top.filenames = rest.filenames;

  top.runningFile = true;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  top.displayHelp = rest.displayHelp;

  forwards to rest;
}


--Dump translated commands to a file
abstract production dumpAbellaFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = rest.checkFile;
  top.filenames = rest.filenames;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = true;
  top.dumpAbellaFile = "abella_dump.thm";

  top.displayHelp = rest.displayHelp;

  forwards to rest;
}



aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--check",
               paramString=nothing(),
               help="check file for correctness and completion",
               flagParser=flag(checkFlag))];

  debugFlags <-
     [flagSpec(name="--dump-Abella",
               paramString=nothing(),
               help="dump translated Abella commands to a file",
               flagParser=flag(dumpAbellaFlag))];

  errors <-
     if a.checkFile && null(a.filenames)
     then ["Must give filename(s) with --check flag"]
     else [];
}