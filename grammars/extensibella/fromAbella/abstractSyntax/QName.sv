grammar extensibella:fromAbella:abstractSyntax;

attribute
   fromAbella<QName>, relFromAbella, tyFromAbella, constrFromAbella
occurs on SubQName, QName;

synthesized attribute isTranslation::Boolean occurs on QName;

synthesized attribute transFromAbella::QName occurs on QName;
synthesized attribute relFromAbella::QName;
synthesized attribute tyFromAbella::QName;
synthesized attribute constrFromAbella::QName;

aspect production baseName
top::SubQName ::= name::String
{
  --if we only have the short name, this is a var
  top.fromAbella = basicQName(baseName(name));

  top.relFromAbella = basicQName(top);
  top.tyFromAbella = basicQName(top);
  top.constrFromAbella = basicQName(top);
}


aspect production addModule
top::SubQName ::= name::String rest::SubQName
{
  --fromAbella should only be for error messages from QName, so use
  --the full name
  top.fromAbella = basicQName(top);

  --check if there are other relations by the same short name
  --only translates 
  top.relFromAbella =
      case lookupEnv(basicQName(baseName(rest.shortName)), top.relationEnv) of
      | [] -> error("Not possible (rel):  " ++ justShow(top.pp))
      | [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l -> basicQName(top)
      end;

  --check if there are other types by the same short name
  top.tyFromAbella =
      case lookupEnv(basicQName(baseName(rest.shortName)), top.typeEnv) of
      | [] -> error("Not possible (ty):  " ++ justShow(top.pp))
      | [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l -> basicQName(top)
      end;

  --check if there are other constructors by the same short name
  top.constrFromAbella =
      case lookupEnv(basicQName(baseName(rest.shortName)), top.constructorEnv),
           lookupEnv(basicQName(baseName(rest.shortName)), top.relationEnv) of
      | [], [] -> error("Not possible (constr):  " ++ justShow(top.pp) ++ "  [" ++
                     implode(", ", map(justShow, map((.pp), map((.name),
                        top.constructorEnv)))) ++ "] and [" ++
                     implode(", ", map(justShow, map((.pp), map((.name),
                        top.relationEnv)))) ++ "]")
      | [_], [] -> basicQName(baseName(rest.shortName)) --no confusion
      | [], [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l1, l2 -> basicQName(top)
      end;
}




aspect production fixQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production transQName
top::QName ::= rest::SubQName
{
  top.isTranslation = true;
  top.transFromAbella =
      case rest.tyFromAbella of
      | tyQName(s) -> transQName(s)
      | basicQName(s) -> transQName(s) --shortened name for display
      | _ ->
        error("Cannot have translation for this (" ++
              rest.tyFromAbella.abella_pp ++ ")")
      end;

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production tyQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production unknownQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production extSizeQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = extSizeQName(rest.fromAbella.sub);

  top.relFromAbella = extSizeQName(rest.relFromAbella.sub);
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production transRelQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = transRelQName(rest.fromAbella.sub);

  top.relFromAbella = transRelQName(rest.relFromAbella.sub);
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production libQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production basicQName
top::QName ::= rest::SubQName
{
  top.isTranslation = false;
  top.transFromAbella = error("Not a translation");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}
