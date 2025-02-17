grammar extensibella:main:compose;

--[(relation, definition)]
synthesized attribute standInRules::[(QName, Def)] occurs on
  ListOfCommands, AnyCommand, TopCommand;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.standInRules = [];
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.standInRules = a.standInRules ++ rest.standInRules;
}





aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.standInRules = c.standInRules;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.standInRules = [];
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.standInRules = [];
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.standInRules = [];
}





aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.standInRules =
      case preds, defs of
      | [(standInRuleQName(relQ), _)], singleDefs(d) -> [(^relQ, ^d)]
      | _, _ -> []
      end;
}


aspect default production
top::TopCommand ::=
{
  top.standInRules = [];
}
