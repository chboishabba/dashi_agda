# Compute the actual characteristic-two involution fingerprint on every
# constructible 10-dimensional AtlasRep representation of M22.
#
# Goal: test the Completion10 requirement
#     rank(g-I)=5, dim Fix(g)=5
# for a sourced involution g.  In dimension 10 and characteristic two this is
# equivalent to Jordan type J2(1)^5 for an involution.
#
# No result is hard-coded.  Every AtlasRep 10-dimensional GF(2) representation
# found locally is checked, every conjugacy class of involutions is evaluated,
# and the literal rows are serialized.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;
if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

groupName := "M22";
expectedOrder := 443520;
expectedDimension := 10;

infos := AllAtlasGeneratingSetInfos(groupName);
candidates := [];

for info in infos do
  if IsBound(info.repname)
     and PositionSublist(info.repname,"f2r10") <> fail then
    Add(candidates,info);
  fi;
od;

if Length(candidates)=0 then
  Error("AtlasRep exposes no M22 f2r10 representation in this installation");
fi;

JsonBool := function(x)
  if x then return "true"; else return "false"; fi;
end;

output := OutputTextFile("build/m22_completion10_involution_screen.json",false);
SetPrintFormattingStatus(output,false);
AppendTo(output,"{\n");
AppendTo(output,"  \"group\": \"M22\",\n");
AppendTo(output,"  \"expected_order\": 443520,\n");
AppendTo(output,"  \"expected_dimension\": 10,\n");
AppendTo(output,"  \"completion10_target\": {\"rank_g_minus_i\":5,\"fixed_dimension\":5},\n");
AppendTo(output,"  \"representations\": [\n");

repCounter := 0;
totalRows := 0;
matchingRows := 0;

for info in candidates do
  G := AtlasGroup(info);
  if G=fail then
    Error(Concatenation("failed to construct ",info.repname));
  fi;
  if Size(G)<>expectedOrder then
    Error(Concatenation("unexpected order for ",info.repname));
  fi;
  gens := GeneratorsOfGroup(G);
  if Length(gens)=0 then
    Error("matrix group has no generators");
  fi;
  dim := NrRows(gens[1]);
  if dim<>expectedDimension then
    Error(Concatenation("unexpected dimension for ",info.repname));
  fi;

  classes := ConjugacyClasses(G);
  involutionClasses := Filtered(classes,cl -> Order(Representative(cl))=2);

  repCounter := repCounter+1;
  if repCounter>1 then AppendTo(output,",\n"); fi;
  AppendTo(output,"    {\"repname\":\"",info.repname,"\",");
  AppendTo(output,"\"involution_classes\":[");

  rowCounter := 0;
  for cl in involutionClasses do
    g := Representative(cl);
    identity := One(g);
    rankDiff := RankMat(g-identity);
    fixedDim := expectedDimension-rankDiff;
    squareZero := (g-identity)*(g-identity)=Zero(g);
    matches := rankDiff=5 and fixedDim=5 and squareZero;
    totalRows := totalRows+1;
    if matches then matchingRows := matchingRows+1; fi;

    rowCounter := rowCounter+1;
    if rowCounter>1 then AppendTo(output,","); fi;
    AppendTo(output,
      "{\"class_size\":",String(Size(cl)),
      ",\"centralizer_order\":",String(Size(G)/Size(cl)),
      ",\"rank_g_minus_i\":",String(rankDiff),
      ",\"fixed_dimension\":",String(fixedDim),
      ",\"square_zero\":",JsonBool(squareZero),
      ",\"matches_J2x5\":",JsonBool(matches),"}");
  od;
  AppendTo(output,"]}");
od;

AppendTo(output,"\n  ],\n");
AppendTo(output,"  \"representation_count\": ",String(repCounter),",\n");
AppendTo(output,"  \"involution_row_count\": ",String(totalRows),",\n");
AppendTo(output,"  \"matching_J2x5_row_count\": ",String(matchingRows),"\n");
AppendTo(output,"}\n");
CloseStream(output);

Print("M22 Completion10 involution screen written: reps=",repCounter,
  "; involution rows=",totalRows,
  "; J2^5 matches=",matchingRows,"\n");
QUIT;
