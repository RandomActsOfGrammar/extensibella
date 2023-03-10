grammar extensibella:composed;

import extensibella:fromAbella:concreteSyntax;
import extensibella:toAbella:concreteSyntax;
import extensibella:interfaceFile:concreteSyntax;
import extensibella:outerfaceFile:concreteSyntax;

{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  extensibella:fromAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}

parser cmd_parse::AnyCommand_c
{
  extensibella:toAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}

parser module_decl_parse::ModuleDecl_c
{
  extensibella:toAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}

--Process a theorem file
parser file_parse::FullFile_c
{
  extensibella:toAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}

--Read a definition file
parser import_parse::ListOfCommands_c
{
  extensibella:toAbella:concreteSyntax;
  extensibella:common:concreteSyntax;
}

--Read an outerface file
parser outerface_parse::Outerface_c
{
  extensibella:common:concreteSyntax;
  extensibella:toAbella:concreteSyntax;
  extensibella:outerfaceFile:concreteSyntax;
}

--Read an interface file
parser interface_parse::ModuleList_c
{
  extensibella:common:concreteSyntax;
  extensibella:interfaceFile:concreteSyntax;
}

