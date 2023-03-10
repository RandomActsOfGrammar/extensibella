grammar extensibella:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp, abella_pp,
   toAbella<[NoOpCommand]>, toAbellaMsgs,
   stateListIn, stateListOut,
   isQuit,
   proverState;
propagate proverState, toAbellaMsgs on NoOpCommand;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text, other than our own debug option
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";
  top.abella_pp = "Set " ++ opt ++ " " ++ val ++ ".\n";

  local abellaSetting::Boolean = opt != "debug";
  top.toAbella =
      if abellaSetting then [setCommand(opt, val)] else [];

  top.stateListOut =
      (if abellaSetting then 1 else 0,
       proverState(top.proverState.state,
                   if opt == "debug" then val == "on"
                                     else top.proverState.debug,
                   top.proverState.knownTheorems,
                   top.proverState.remainingObligations,
                   top.proverState.knownTypes,
                   top.proverState.knownRels,
                   top.proverState.knownConstrs,
                   top.proverState.provingThms,
                   top.proverState.duringCommands,
                   top.proverState.afterCommands)
      )::top.stateListIn;

  top.toAbellaMsgs <-
      if opt == "debug"
      then if val == "on" || val == "ofF"
           then []
           else [errorMsg("Option 'debug' can only be set to " ++
                          "'on' or 'off', not '" ++ val ++ "'")]
      else if opt == "witnesses"
      then if val == "on" || val == "off"
           then []
           else [errorMsg("Argument to option 'witnesses' must be " ++
                          "'on' or 'off', not '" ++ val ++ "'")]
      else if opt == "search_depth"
      then if toIntSafe(val).isJust
           then []
           else [errorMsg("Argument to option 'search_depth' must " ++
                          "be integer; found '" ++ val ++ "'")]
      else [errorMsg("Unknown option '" ++ opt ++ "'")];

  top.isQuit = false;
}


abstract production showCommand
top::NoOpCommand ::= theoremName::QName
{
  top.pp = "Show " ++ theoremName.pp ++ ".\n";
  top.abella_pp = "Show " ++ theoremName.abella_pp ++ ".\n";

  local possibleThms::[(QName, Metaterm)] =
     findTheorem(theoremName, top.proverState);
  top.toAbella = [showCommand(head(possibleThms).1)];

  top.toAbellaMsgs <-
      case possibleThms of
      | [] ->
        [errorMsg("Unknown theorem " ++ theoremName.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate theorem " ++ theoremName.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleThms))))]
      end;

  top.stateListOut = (1, top.proverState)::top.stateListIn;

  top.isQuit = false;
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";
  top.abella_pp = "Quit.\n";

  top.toAbella = [top];

  --this probably isn't needed
  top.stateListOut = top.stateListIn;

  top.isQuit = true;
}


--This is what Proof General uses for undoing things
abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = implode(" ", repeat("#back.", n)) ++ "\n";
  top.abella_pp = top.pp;

  local trans_n::Integer =
      foldr(\ p::(Integer, ProverState) rest::Integer -> p.1 + rest,
            0, take(n, top.stateListIn));
  --send a set of "back one"s so sending them to Abella and reading
  --them back works correctly
  top.toAbella = repeat(backCommand(1), trans_n);

  top.toAbellaMsgs <-
      if length(top.stateListIn) <= n
      then [errorMsg("Cannot go back that far")]
      else [];

  top.stateListOut = drop(n, top.stateListIn);

  top.isQuit = false;
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";
  top.abella_pp = "#reset.\n";

  top.toAbella = [top];

  top.toAbellaMsgs <- [errorMsg("Cannot #reset")];

  --shouldn't need this since this command isn't allowed
  top.stateListOut = top.stateListIn;

  top.isQuit = false;
}


abstract production showCurrentCommand
top::NoOpCommand ::=
{
  top.pp = "Show $$current.\n";
  top.abella_pp =
      error("showCurrentCommand.abella_pp should not be accessed");

  top.toAbella = [];

  --this doesn't really count as a command since it shouldn't be used
  --other than by Proof General
  top.stateListOut = top.stateListIn;

  top.isQuit = false;
}
