grammar extensibella:main:thmDoc;

imports extensibella:common;
imports extensibella:toAbella;

imports extensibella:main:util;

imports silver:util:cmdargs;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;


--Command line flags

synthesized attribute genThmDocHtml::Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.genThmDocHtml = false;
}


abstract production genThmDocHtmlFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.genThmDocHtml = true;

  top.runREPL = false; --this requires files

  forwards to @rest;
}


aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--thmDocHTML",
               paramString=nothing(),
               help="output an HTML file listing the theorems",
               flagParser=flag(genThmDocHtmlFlag))];
}
