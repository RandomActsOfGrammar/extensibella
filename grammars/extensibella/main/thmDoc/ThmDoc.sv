grammar extensibella:main:thmDoc;

{-
  Everything for creating the output for a file is generic in the
  output format; all that is necessary for using it for another output
  format is writing new formatting functions and adding a way to
  specify outputting it.
-}

function thmDoc_html_files
IOVal<Integer> ::= allParsers::AllParsers ioin::IOToken
                   config::Configuration
{
  return foldr(\ here::String rest::IOVal<Integer> ->
                 if rest.iovalue != 0
                 then rest
                 else thmDoc_one_file(here, htmlOutputType,
                                      allParsers, rest.io),
               ioval(ioin, 0), config.filenames);
}




function thmDoc_one_file
IOVal<Integer> ::= filename::String outputType::DocOutputType
                   allParsers::AllParsers ioin::IOToken
{
  local outFilename::String =
      splitFileNameAndExtension(fileNameInFilePath(filename)).1 ++
      outputType.fileExtension;
  local processed::IOVal<Maybe<(String, String)>> =
      processFile(filename, outputType, allParsers, ioin);
  return
      case processed.iovalue of
      | just((defs, thms)) ->
        ioval(writeFileT(outFilename, defs ++ thms, processed.io), 0)
      | nothing() -> ioval(processed.io, 1)
      end;
}




data nonterminal DocOutputType with
   formatThmFun, formatDefFun, formatDeclFun,
   combineThmsFun, combineDefsFun, fileExtension;
--format a theorem                  (name, params, body)
annotation formatThmFun::(String ::= QName [String] Metaterm);
--format Define/Codefine            (preds, defs, isNotCoDefinition)
annotation formatDefFun::(String ::= [(QName, Type)] Defs Boolean);
--format a Kind/Type decl            (names, specification info)
annotation formatDeclFun::(String ::= [QName] Either<Kind Type>);
--put together formatted thms
annotation combineThmsFun::(String ::= [String]);
--put together formatted defs and decls
annotation combineDefsFun::(String ::= [String]);
--file extension for files of this type
annotation fileExtension::String;
abstract production docOutputType top::DocOutputType ::= { }





{--------------------------------------------------------------------
                             Format HTML
 --------------------------------------------------------------------}
global htmlOutputType::DocOutputType =
   docOutputType(formatThmFun = formatHtmlThm,
      formatDefFun = formatHtmlDef, formatDeclFun = formatHtmlDecl,
      combineThmsFun = combineHtmlThms,
      combineDefsFun = combineHtmlDefs, fileExtension = ".html");

function formatHtmlThm
String ::= name::QName params::[String] body::Metaterm
{
  local pString::String =
      if null(params)
      then ""
      else " [" ++ implode(", ", params) ++ "]";
  local startString::String =
      "\n<li><code>" ++ name.shortName ++ pString ++ "</code>";
  local bodyString::String =
      "<pre class=\"code extensibella\">" ++ show(100, body.pp) ++
      "</pre>";
  return startString ++ " : " ++ bodyString;
}

function formatHtmlDef
String ::= preds::[(QName, Type)] defs::Defs isNotCo::Boolean
{
  local startString::String =
      "\n<li>" ++
      (if isNotCo
       then "Predicate"
       else "Co-Defined Predicate") ++
      if length(preds) > 1
      then "s "
      else " ";

  local formattedPreds::[String] =
      map(\ p::(QName, Type) ->
            "<code>" ++ justShow(p.1.pp) ++ "</code> : " ++
            "<code>" ++ justShow(p.2.pp) ++ "</code>",
          preds);
  local predsString::String =
      if length(preds) == 1
      then head(formattedPreds)
      else "<ul>\n" ++
           implode("\n<li>", formattedPreds) ++
           "\n</ul>";

  local defsString::String =
      "<pre class=\"code extensibella\">" ++
      show(100, ppImplode(text(";") ++ realLine(), defs.pps)) ++
      "</pre>";

  return startString ++ predsString ++ "\n" ++ defsString;
}

function formatHtmlDecl
String ::= names::[QName] kind_ty::Either<Kind Type>
{
  return
      case kind_ty of
      | left(k) ->
        implode("",
           map(\ q::QName ->
                 "\n<li>Type <code>" ++ justShow(q.pp) ++
                 "</code> : <code class=\"extensibella\">" ++
                 justShow(k.pp) ++ "</code>", names))
      | right(t) ->
        implode("",
           map(\ q::QName ->
                 "\n<li>Constructor <code>" ++ justShow(q.pp) ++
                 "</code> : <code class=\"extensibella\">" ++
                 justShow(t.pp) ++ "</code>", names))
      end;
}

function combineHtmlThms
String ::= elements::[String]
{
  --assumes everything starts with <li>
  return if null(elements)
         then ""
         else "<h3>Properties</h3>\n<ul>" ++
              implode("", elements) ++ "\n</ul>\n";
}

function combineHtmlDefs
String ::= elements::[String]
{
  --assumes everything starts with <li>
  return if null(elements)
         then ""
         else "<h3>Definitions</h3>\n<ul>" ++
              implode("", elements) ++ "\n</ul>\n";
}





{--------------------------------------------------------------------
                         Build Documentation
 --------------------------------------------------------------------}

function processFile
       --(defs/decls, thms)
IOVal<Maybe<(String, String)>> ::=
   filename::String outputType::DocOutputType
   allParsers::AllParsers ioin::IOToken
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  --get the file contents and parse it
  local contents::IOVal<String> = readFileT(filename, fileExists.io);
  local parsed::ParseResult<FullFile_c> =
      allParsers.file_parse(contents.iovalue, filename);
  --build the thms and defs
  local ast::ListOfCommands = parsed.parseTree.ast.2;
  ast.formatThm = outputType.formatThmFun;
  ast.formatDef = outputType.formatDefFun;
  ast.formatDecl = outputType.formatDeclFun;
  ast.knownThms = [];
  ast.currentModule = parsed.parseTree.ast.1.fromJust;

  return if !fileExists.iovalue
         then ioval(printT("File " ++ filename ++ " does not exist",
                           fileExists.io), nothing())
         else ioval(contents.io,
                 just((outputType.combineDefsFun(ast.defStrings),
                       outputType.combineThmsFun(ast.thmStrings))));
}





inherited attribute formatThm::(String ::= QName [String] Metaterm);
                                        --preds, defs, isNotCoDefinition
inherited attribute formatDef::(String ::= [(QName, Type)] Defs Boolean);
inherited attribute formatDecl::(String ::= [QName] Either<Kind Type>);
synthesized attribute thmStrings::[String];
synthesized attribute defStrings::[String];
--gather theorems for splits
inherited attribute knownThms::[(QName, Metaterm)];
synthesized attribute newThms::[(QName, Metaterm)];

attribute
   formatThm, formatDef, formatDecl,
   thmStrings, defStrings,
   knownThms
occurs on ListOfCommands;
propagate formatThm, formatDef, formatDecl on ListOfCommands;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.thmStrings = [];
  top.defStrings = [];
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.thmStrings = a.thmStrings ++ rest.thmStrings;
  top.defStrings = a.defStrings ++ rest.defStrings;

  a.knownThms = top.knownThms;
  rest.knownThms = a.newThms ++ rest.knownThms;
}



attribute
   formatThm, formatDef, formatDecl,
   thmStrings, defStrings,
   knownThms, newThms
occurs on AnyCommand;
propagate formatThm, formatDef, formatDecl on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.thmStrings = c.thmStrings;
  top.defStrings = c.defStrings;

  c.knownThms = top.knownThms;
  top.newThms = c.newThms;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}



attribute
   formatThm, formatDef, formatDecl,
   thmStrings, defStrings,
   knownThms, newThms
occurs on TopCommand;
propagate formatThm, formatDef, formatDecl on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.thmStrings = [top.formatThm(^name, params, ^body)];
  top.defStrings = [];

  top.newThms = [(^fullName, ^body)];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.thmStrings = [];
  top.defStrings = [top.formatDef(preds, ^defs, true)];

  top.newThms = [];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.thmStrings = [];
  top.defStrings = [top.formatDef(preds, ^defs, false)];

  top.newThms = [];
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  --only handle splitting thms introduced in this file
  --any imported ones are skipped for simplicity, avoiding the need
  --   to read the interface and outerface files
  local thms::[(QName, Metaterm)] =
      case lookup(if theoremName.isQualified
                  then ^theoremName
                  else addQNameBase(top.currentModule,
                                    theoremName.shortName),
              top.knownThms) of
      | nothing() -> []
      | just(m) -> zip(newTheoremNames, m.splitConjunctions)
      end;

  top.thmStrings = map(\ p::(QName, Metaterm) ->
                         top.formatThm(p.1, [], p.2),
                       thms);
  top.defStrings = [];

  top.newThms =
      map(\ p::(QName, Metaterm) ->
            (if p.1.isQualified then p.1
             else addQNameBase(top.currentModule, p.1.shortName), p.2),
          thms);
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.thmStrings = [];
  top.defStrings = [top.formatDecl(names, left(^k))];

  top.newThms = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.thmStrings = [];
  top.defStrings = [top.formatDecl(names, right(^ty))];

  top.newThms = [];
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.thmStrings = thms.thmStrings ++ alsos.thmStrings;
  top.defStrings = [];

  top.newThms = thms.newThms ++ alsos.newThms;
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.thmStrings = newThms.thmStrings ++ newAlsos.thmStrings;
  top.defStrings = [];

  top.newThms = [];
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.thmStrings =
      [top.formatThm(^name, [], bindingMetaterm(forallBinder(),
                                                ^binds, body.thm))];
  top.defStrings = [];

  top.newThms =
      [(^name, bindingMetaterm(forallBinder(), ^binds, body.thm))];
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.thmStrings = thms.thmStrings ++ alsos.thmStrings;
  top.defStrings = [];

  top.newThms = [];
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.thmStrings = [];
  top.defStrings = [];

  top.newThms = [];
}



attribute
   formatThm, thmStrings, newThms
occurs on ExtThms;
propagate formatThm on ExtThms;

aspect production endExtThms
top::ExtThms ::=
{
  top.thmStrings = [];

  top.newThms = [];
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 ons::InductionOns rest::ExtThms
{
  top.thmStrings =
      top.formatThm(^name, [], bindingMetaterm(forallBinder(),
                                               ^bindings, body.thm)
                   )::rest.thmStrings;

  top.newThms = (^fullName, bindingMetaterm(forallBinder(), ^bindings,
                                           body.thm))::rest.newThms;
}
