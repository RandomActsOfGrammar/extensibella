grammar extensibella:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp, abella_pp,
   toAbella<[NoOpCommand]>, toAbellaMsgs,
   priorStep, newPriorStep, newProverState,
   isQuit,
   proverState, interactive;
propagate proverState, toAbellaMsgs, interactive on NoOpCommand;

abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = cat(text("Set " ++ opt ++ " " ++ val ++ "."), realLine());
  top.abella_pp = "Set " ++ opt ++ " " ++ val ++ ".\n";

  local abellaSetting::Boolean = opt != "debug" && opt != "display_width";
  top.toAbella =
      if abellaSetting then [setCommand(opt, val)] else [];

  top.newProverState =
      if opt == "debug"
      then setProverDebug(top.proverState, val == "on")
      else if opt == "display_width"
      then setProverWidth(top.proverState, toInteger(val))
      else top.proverState;
  top.newPriorStep = nothing();

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
      else if opt == "display_width"
      then if toIntSafe(val).isJust
           then []
           else [errorMsg("Argument to option 'display_width' must" ++
                          " be integer; found '" ++ val ++ "'")]
      else [errorMsg("Unknown option '" ++ opt ++ "'")];
  top.toAbellaMsgs <-
      if top.interactive
      then []
      else if opt == "debug"
      then [errorMsg("Option 'debug' of 'Set' should not be used" ++
                     "in non-interactive settings")]
      else if opt == "witnesses"
      then [errorMsg("Option 'witnesses' of 'Set' should not be " ++
                     "used in non-interactive settings")]
      else [];

  top.isQuit = false;
}


abstract production showCommand
top::NoOpCommand ::= theoremName::QName
{
  top.pp = text("Show ") ++ theoremName.pp ++ text(".") ++ realLine();
  top.abella_pp = "Show " ++ theoremName.abella_pp ++ ".\n";

  production possibleThms::[(QName, Metaterm)] =
      findTheorem(^theoremName, top.proverState);
  top.toAbella = [showCommand(head(possibleThms).1)];

  top.newProverState = top.proverState;
  top.newPriorStep = nothing();

  top.toAbellaMsgs <-
      case possibleThms of
      | [] ->
        [errorMsg("Unknown theorem " ++ justShow(theoremName.pp))]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate theorem " ++ 
                  justShow(theoremName.pp) ++
                  "; possibilities are " ++
                  implode(", ", map(justShow, map((.pp),
                                  map(fst, possibleThms)))))]
      end;
  top.toAbellaMsgs <-
      if !top.interactive
      then [errorMsg("Show command should not be used in " ++
                     "non-interactive settings")]
      else [];

  top.isQuit = false;
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = cat(text("Quit."), realLine());
  top.abella_pp = "Quit.\n";

  top.toAbella = [^top];

  top.newProverState = top.proverState;
  top.newPriorStep = nothing();

  top.toAbellaMsgs <-
      if !top.interactive
      then [errorMsg("Quit command should not be used in " ++
                     "non-interactive settings")]
      else [];

  top.isQuit = true;
}


--This is what Proof General uses for undoing things
abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = cat(ppImplode(line(), repeat(text("#back."), n)),
               realLine());
  top.abella_pp = justShow(top.pp);

  local undone::Maybe<(Integer, PriorStep, ProverState)> =
      undoN(n, top.priorStep);
  top.newPriorStep = just(undone.fromJust.2);
  top.newProverState = undone.fromJust.3;

  --send a set of "back one"s so sending them to Abella and reading
  --them back works correctly
  top.toAbella = repeat(backCommand(1), undone.fromJust.1);

  top.toAbellaMsgs <-
      case undone of
      | nothing() -> [errorMsg("Cannot go back that far")]
      | _ -> []
      end;
  top.toAbellaMsgs <-
      if !top.interactive
      then [errorMsg("#back command should not be used in " ++
                     "non-interactive settings")]
      else [];

  top.isQuit = false;
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = cat(text("#reset."), realLine());
  top.abella_pp = "#reset.\n";

  top.toAbella = [^top];

  --this command is a fiction, so nothing here
  top.newProverState = error("resetCommand.newProverState");
  top.newPriorStep = error("resetCommand.newPriorStep");

  top.toAbellaMsgs <- [errorMsg("Cannot #reset")];

  top.isQuit = false;
}


--this doesn't really count as a command since it shouldn't be used
--other than by Proof General
abstract production showCurrentCommand
top::NoOpCommand ::=
{
  top.pp = cat(text("Show $$current."), realLine());
  top.abella_pp =
      error("showCurrentCommand.abella_pp should not be accessed");

  top.toAbella = [];

  top.newProverState = top.proverState;
  top.newPriorStep = just(top.priorStep);

  top.toAbellaMsgs <-
      if !top.interactive
      then [errorMsg("'Show $$current.' command should not be " ++
                     "used in non-interactive settings")]
      else [];

  top.isQuit = false;
}
