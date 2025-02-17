grammar extensibella:interfaceFile:abstractSyntax;

imports extensibella:common:abstractSyntax;

nonterminal ImportedModuleList with mods, buildsOns;

synthesized attribute mods::[QName];
synthesized attribute buildsOns::[(QName, [QName])];

abstract production emptyModuleList
top::ImportedModuleList ::=
{
  top.mods = [];
  top.buildsOns = [];
}


abstract production addModuleList
top::ImportedModuleList ::= module::QName buildsOn::BuildsOnList
                            rest::ImportedModuleList
{
  top.mods = ^module::rest.mods;
  top.buildsOns = (^module, buildsOn.mods)::rest.buildsOns;
}



nonterminal BuildsOnList with mods;

abstract production emptyBuildsOnList
top::BuildsOnList ::=
{
  top.mods = [];
}


abstract production addBuildsOnList
top::BuildsOnList ::= module::QName rest::BuildsOnList
{
  top.mods = ^module::rest.mods;
}
