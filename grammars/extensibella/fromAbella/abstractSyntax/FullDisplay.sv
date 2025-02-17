grammar extensibella:fromAbella:abstractSyntax;


nonterminal FullDisplay with
   pp,
   fromAbella<FullDisplay>,
   typeEnv, relationEnv, constructorEnv,
   proof, isError, isWarning, proofEnded;
propagate typeEnv, relationEnv, constructorEnv on FullDisplay;

abstract production fullDisplay
top::FullDisplay ::= msg::ExtraInformation state::ProofState
{
  top.pp = (if msg.isEmpty then text("")
              else msg.pp ++ realLine() ++ realLine()) ++ state.pp;

  top.fromAbella = fullDisplay(msg.fromAbella, state.fromAbella);

  top.proof = ^state;
  top.isError = msg.isError;
  top.isWarning = msg.isWarning;
  top.proofEnded =
      case state of
      | noProof() -> false
      | proofCompleted() -> true
      | proofAborted() -> true
      | proofInProgress(_, _, _) -> false
      end;
}


abstract production showDisplay
top::FullDisplay ::= tl::TheoremList
{
  top.pp = ppImplode(realLine() ++ realLine(), tl.pps);

  top.fromAbella = showDisplay(tl.fromAbella);

  --We don't know what the current state is
  top.proof = noProof(isAbellaForm=true);
  top.isError = false;
  top.isWarning = false;
  top.proofEnded = false;
}





nonterminal TheoremList with
   pps,
   fromAbella<TheoremList>,
   typeEnv, relationEnv, constructorEnv;
propagate typeEnv, relationEnv, constructorEnv on TheoremList;

abstract production theoremListEmpty
top::TheoremList ::=
{
  top.pps = [];

  top.fromAbella = theoremListEmpty();
}

abstract production theoremListAdd
top::TheoremList ::= name::QName params::[String] body::Metaterm
                     rest::TheoremList
{
  top.pps = (text("Theorem ") ++ name.pp ++
            (if null(params)
             then text("")
             else text(" [") ++ ppImplode(text(", "), map(text, params)) ++
                  text("]")) ++
             text(" :") ++ line() ++
             docGroup(body.pp ++ text(".")))::rest.pps;

  top.fromAbella =
      theoremListAdd(name.fromAbella, params, body.fromAbella, rest.fromAbella);
}





nonterminal ExtraInformation with
   pp,
   fromAbella<ExtraInformation>,
   typeEnv, relationEnv, constructorEnv,
   isError, isWarning, isEmpty;
propagate typeEnv, relationEnv, constructorEnv on ExtraInformation;

synthesized attribute isEmpty::Boolean;


abstract production emptyInformation
top::ExtraInformation ::=
{
  top.pp = text("");

  top.fromAbella = emptyInformation();

  top.isError = false;
  top.isWarning = false;
  top.isEmpty = true;
}


abstract production importInformation
top::ExtraInformation ::= moduleName::String
{
  top.pp = text("Importing from \"" ++ moduleName ++ "\".");

  top.fromAbella = importInformation(moduleName);

  top.isError = false;
  top.isWarning = false;
  top.isEmpty = false;
}


abstract production syntaxErrorInformation
top::ExtraInformation ::= extraText::String
{
  top.pp = text("Syntax error.") ++
           if extraText == "" then text("")
                              else realLine() ++ text(extraText);

  top.fromAbella =
      syntaxErrorInformation("This is an Abella syntax error, " ++
         "which generally means something went wrong with Extensibella.");

  top.isError = true;
  top.isWarning = false;
  top.isEmpty = false;
}


abstract production processingError
top::ExtraInformation ::= msg::ProcessingErrorMessage
{
  top.pp = text("Error: ") ++ msg.pp;

  top.fromAbella = processingError(msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
  top.isEmpty = false;
}


abstract production typingError
top::ExtraInformation ::= msg::TypingErrorMessage
{
  top.pp = text("Typing Error.") ++ realLine() ++ msg.pp;

  top.fromAbella = typingError(msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
  top.isEmpty = false;
}


abstract production warningInformation
top::ExtraInformation ::= msg::WarningMessage
{
  top.pp = text("Warning: ") ++ msg.pp;

  top.fromAbella = warningInformation(msg.fromAbella);

  top.isError = false;
  top.isWarning = true;
  top.isEmpty = false;
}


abstract production alreadyImported
top::ExtraInformation ::= filepath::String
{
  top.pp = text("Ignoring import: " ++ filepath ++
                " has already been imported.");

  top.fromAbella = alreadyImported(filepath);

  top.isError = false;
  top.isWarning = true;
  top.isEmpty = false;
}


abstract production importError
top::ExtraInformation ::= moduleName::String
                          msg::ProcessingErrorMessage
{
  top.pp = text("Importing from \"" ++ moduleName ++
                "\".\nError: ") ++ msg.pp;

  top.fromAbella = importError(moduleName, msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
  top.isEmpty = false;
}

