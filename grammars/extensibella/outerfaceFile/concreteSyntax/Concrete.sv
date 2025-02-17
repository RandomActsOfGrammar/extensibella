grammar extensibella:outerfaceFile:concreteSyntax;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:outerfaceFile:abstractSyntax;


--have this for future proofing against changes adding extra elements
closed nonterminal Outerface_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<Outerface>;

concrete productions top::Outerface_c
| t::TopCommands_c
  { top.ast = outerface(t.ast); }


closed nonterminal TopCommands_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<TopCommands>;

concrete productions top::TopCommands_c
|
  { top.ast = endTopCommands(); }
| t::PureTopCommand_c rest::TopCommands_c
  { top.ast =
        addTopCommands(
           case t.ast of
           | anyTopCommand(tc) -> ^tc
           | _ -> error("Cannot have errors in interface file")
           end, rest.ast); }
| whole::Number_t '-' num::Number_t '/' den::Number_t '->' q::Qname_t ':'
  t::PureTopCommand_c rest::TopCommands_c
  { top.ast =
        addTagTopCommands(
           (toInteger(whole.lexeme), toInteger(num.lexeme),
            toInteger(den.lexeme), q.lexeme),
           case t.ast of
           | anyTopCommand(tc) -> ^tc
           | _ -> error("Cannot have errors in interface file")
           end, rest.ast); }
| whole::Number_t '-' num::Number_t '/' den::Number_t '->' q::Id_t ':'
  t::PureTopCommand_c rest::TopCommands_c
  { top.ast =
        addTagTopCommands(
           (toInteger(whole.lexeme), toInteger(num.lexeme),
            toInteger(den.lexeme), q.lexeme),
           case t.ast of
           | anyTopCommand(tc) -> ^tc
           | _ -> error("Cannot have errors in interface file")
           end, rest.ast); }
