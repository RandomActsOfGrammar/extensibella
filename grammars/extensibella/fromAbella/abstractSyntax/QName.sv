grammar extensibella:fromAbella:abstractSyntax;

attribute
   fromAbella<QName>, relFromAbella, tyFromAbella, constrFromAbella
occurs on SubQName, QName;

synthesized attribute isProjection::Boolean occurs on QName;

synthesized attribute projFromAbella::QName occurs on QName;
synthesized attribute relFromAbella::QName;
synthesized attribute tyFromAbella::QName;
synthesized attribute constrFromAbella::QName;

aspect production baseName
top::SubQName ::= name::String
{
  --if we only have the short name, this is a var or stdLib const/rel
  top.fromAbella = basicQName(baseName(name));

  top.relFromAbella = basicQName(^top);
  top.tyFromAbella = basicQName(^top);
  top.constrFromAbella = basicQName(^top);
}


aspect production addModule
top::SubQName ::= name::String rest::SubQName
{
  --fromAbella should only be for error messages from QName, so use
  --the full name
  top.fromAbella = basicQName(^top);

  --check if there are other relations by the same short name
  --only translates 
  top.relFromAbella =
      case lookupEnv(basicQName(baseName(rest.shortName)), top.relationEnv) of
      | [] -> error("Not possible (rel):  " ++ justShow(top.pp))
      | [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l -> basicQName(^top)
      end;

  --check if there are other types by the same short name
  top.tyFromAbella =
      case lookupEnv(basicQName(baseName(rest.shortName)), top.typeEnv) of
      | [] -> error("Not possible (ty):  " ++ justShow(top.pp))
      | [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l -> basicQName(^top)
      end;

  --check if there are other constructors by the same short name
  --filter out unknown constructors since they don't actually use the name
  top.constrFromAbella =
      case filter(\ c::ConstructorEnvItem ->
                    case c.name of
                    | unknownIQName(_) -> false
                    | unknownKQName(_) -> false
                    | _ -> true
                    end,
              lookupEnv(basicQName(baseName(rest.shortName)),
                        top.constructorEnv)),
           lookupEnv(basicQName(baseName(rest.shortName)), top.relationEnv) of
      | [], [] -> error("Not possible (constr):  " ++ justShow(top.pp) ++ "  [" ++
                     implode(", ", map(justShow, map((.pp), map((.name),
                        top.constructorEnv)))) ++ "] and [" ++
                     implode(", ", map(justShow, map((.pp), map((.name),
                        top.relationEnv)))) ++ "]")
      | [_], [] -> basicQName(baseName(rest.shortName)) --no confusion
      | [], [_] -> basicQName(baseName(rest.shortName)) --no confusion
      | l1, l2 -> basicQName(^top)
      end;
}




aspect production fixQName
top::QName ::= rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production projQName
top::QName ::= rest::SubQName
{
  top.isProjection = true;
  top.projFromAbella =
      case rest.tyFromAbella of
      | tyQName(s) -> projQName(^s)
      | basicQName(s) -> projQName(^s) --shortened name for display
      | _ ->
        error("Cannot have projection for this (" ++
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
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production unknownIQName
top::QName ::= rest::QName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production unknownKQName
top::QName ::= rest::QName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production extSizeQName
top::QName ::= rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = extSizeQName(rest.fromAbella.sub);

  top.relFromAbella = extSizeQName(rest.relFromAbella.sub);
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production projRelQName
top::QName ::= rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = projRelQName(rest.fromAbella.sub);

  top.relFromAbella = projRelQName(rest.relFromAbella.sub);
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production libQName
top::QName ::= rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}


aspect production basicQName
top::QName ::= rest::SubQName
{
  top.isProjection = false;
  top.projFromAbella = error("Not a projection");

  top.fromAbella = rest.fromAbella;

  top.relFromAbella = rest.relFromAbella;
  top.tyFromAbella = rest.tyFromAbella;
  top.constrFromAbella = rest.constrFromAbella;
}
