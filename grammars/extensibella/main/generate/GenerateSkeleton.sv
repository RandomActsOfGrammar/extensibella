grammar extensibella:main:generate;

imports extensibella:interfaceFile;

imports silver:langutil:pp;
imports silver:langutil only pp;


function generateSkeletonFiles
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  local r::IOVal<Boolean> =
      foldl(\ thusFar::IOVal<Boolean> p::(QName, String) ->
              if thusFar.iovalue
              then generateSkeletonFile(p.1, p.2, parsers, thusFar.io)
              else thusFar,
            ioval(ioin, true), config.generateFiles);
  return ioval(r.io, if r.iovalue then 0 else 1);
}


function generateSkeletonFile
IOVal<Boolean> ::= module::QName filename::String parsers::AllParsers
                   ioin::IOToken
{
  local processModule::IOVal<Either<String
                             (ListOfCommands, [DefElement],
                              [ThmElement],
                              [(QName, [QName])])>> =
      processModuleDecl(^module, parsers, ioin);
  local outputThms::[ThmElement] =
      filter((.inSkeleton), processModule.iovalue.fromRight.3);
  local outputString::String =
      "Module " ++ justShow(module.pp) ++ ".\n\n\n" ++
      implode("\n\n\n", map(\ p::ThmElement -> p.skeletonText,
                            outputThms)) ++ "\n\n";
  --
  local fileExists::IOVal<Boolean> =
      isFileT(filename, processModule.io);
  local askReplace::IOVal<String> =
      if fileExists.iovalue
      then let replace::IOVal<Maybe<String>> =
               readLineStdinT(
                  printT("File " ++ filename ++ " exists; replace? (Y/n) ",
                         fileExists.io))
           in
             ioval(replace.io, replace.iovalue.fromJust)
           end
      else ioval(fileExists.io, "");
  local doOutput::Boolean =
      !fileExists.iovalue ||
      askReplace.iovalue == "" ||
      substring(0, 1, askReplace.iovalue) == "Y" ||
      substring(0, 1, askReplace.iovalue) == "y";
  local message::IOToken =
      if doOutput
      then printT("Writing contents for " ++ justShow(module.pp) ++
                  " into " ++ filename ++ "\n", askReplace.io)
      else printT("Skipping module " ++ justShow(module.pp) ++ "\n",
                  askReplace.io);
  local output::IOToken =
      if doOutput
      then writeFileT(filename, outputString, message)
      else message;

  return
      case processModule.iovalue of
      | left(err) ->
        ioval(printT("Error:  " ++ err ++ "\n", processModule.io),
              false)
      | right(_) -> ioval(output, true)
      end;
}



attribute
   inSkeleton, skeletonText
occurs on ThmElement;

--whether it belongs in the generated skeleton
synthesized attribute inSkeleton::Boolean;
--the text to go in the skeleton if it belongs
synthesized attribute skeletonText::String;

aspect production extensibleMutualTheoremGroup
top::ThmElement ::= thms::[(QName, Bindings, ExtBody, InductionOns)]
                    alsos::[(QName, Bindings, ExtBody, InductionOns)]
                    tag::Tag
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Prove ") ++
         nest(6, ppImplode(text(",") ++ line(),
                    map((.pp), map(fst, thms)))) ++ text("."));
}


aspect production projectionConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
                    tag::Tag
{
  top.inSkeleton = true;
  top.skeletonText = "Prove_Constraint " ++ justShow(name.pp) ++ ".";
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  top.inSkeleton = false;
  top.skeletonText = "";
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.inSkeleton = false;
  top.skeletonText = "";
}


aspect production extIndElement
top::ThmElement ::=
   rels::[(QName, [String], Bindings, ExtIndPremiseList, [String])]
   thms::[(QName, Bindings, ExtBody, InductionOns)]
   alsos::[(QName, Bindings, ExtBody, InductionOns)]
   tag::Tag
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Prove_Ext_Ind ") ++
         nest(14, ppImplode(text(",") ++ line(),
                     map((.pp), map(fst, rels)))) ++
         (if length(thms) > 0
          then line() ++ text("and_thms") ++ line() ++
               nest(9, ppImplode(text(",")  ++ line(),
                         map((.pp), map(fst, thms))))
          else text("")) ++
         text("."));
}


aspect production extSizeElement
top::ThmElement ::= rels::[(QName, [String])] tag::Tag
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Add_Ext_Size ") ++
         nest(13, ppImplode(text(",") ++ line(),
                     map((.pp), map(fst, rels)))) ++
         text("."));
}


aspect production projRelElement
top::ThmElement ::= rels::[(QName, [String])] tag::Tag
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Add_Proj_Rel ") ++
         nest(13, ppImplode(text(",") ++ line(),
                     map((.pp), map(fst, rels)))) ++
         text("."));
}
