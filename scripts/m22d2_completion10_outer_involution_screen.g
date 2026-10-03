# Screen the actual characteristic-two 10-dimensional AtlasRep modules of
# M22:2 for the revised Completion10 binary phase.
#
# The bare M22 involution test is already negative: rank(g-I)=4, fixdim=6 on
# both 10a and 10b.  This script tests the strictly larger sourced stabilizer
# M22:2.  For every involution class in each faithful 10-dimensional GF(2)
# representation it records:
#
#   * whether the class lies outside the derived M22 subgroup;
#   * rank(g-I) and fixed-space dimension;
#   * whether the J2^5 Completion10 fingerprint occurs;
#   * for a match, an explicit basis of five swapped pairs;
#   * which M22 10a/10b module appears on restriction to the derived subgroup.
#
# A positive outer J2^5 row would pay the finite C' candidate at the
# M22:2-duad-stabilizer level.  It would still not identify the module with an
# actual Carnahan--Urano 2B Tate subquotient; that is the independent B' weld.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;
if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

expectedOrder := 887040;
expectedDerivedOrder := 443520;
expectedDimension := 10;
F := GF(2);

infos := AllAtlasGeneratingSetInfos(
  "M22.2", Dimension, expectedDimension, Characteristic, 2 );
if Length(infos)=0 then
  Error("AtlasRep exposes no M22.2 dimension-10 GF(2) representations");
fi;

m22Infos := AllAtlasGeneratingSetInfos(
  "M22", Dimension, expectedDimension, Characteristic, 2 );
if Length(m22Infos)<>2 then
  Error("expected exactly two M22 dimension-10 GF(2) AtlasRep modules");
fi;

JsonBool := function(x)
  if x then return "true"; else return "false"; fi;
end;

PrintStringList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,"\"",xs[i],"\"");
  od;
  AppendTo(out,"]");
end;

out := OutputTextFile(
  "build/m22d2_completion10_outer_involution_screen.json", false );
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"group\": \"M22.2\",\n");
AppendTo(out,"  \"expected_order\": 887040,\n");
AppendTo(out,"  \"expected_derived_order\": 443520,\n");
AppendTo(out,"  \"expected_dimension\": 10,\n");
AppendTo(out,"  \"target\": {\"rank_g_minus_i\":5,\"fixed_dimension\":5},\n");
AppendTo(out,"  \"representations\": [\n");

repCounter := 0;
outerInvolutionRows := 0;
outerMatches := 0;
allMatches := 0;

for info in infos do
  G := AtlasGroup(info);
  if G=fail then
    Error(Concatenation("failed to construct ",info.repname));
  fi;
  if Size(G)<>expectedOrder then
    Error(Concatenation("unexpected M22.2 order for ",info.repname));
  fi;
  gens := GeneratorsOfGroup(G);
  if NrRows(gens[1])<>expectedDimension then
    Error(Concatenation("unexpected matrix dimension for ",info.repname));
  fi;

  D := DerivedSubgroup(G);
  if Size(D)<>expectedDerivedOrder then
    Error("derived subgroup is not M22 of expected order");
  fi;

  # Identify the restriction to derived M22 against the two actual M22 10d
  # AtlasRep modules.  Transport standard M22 matrices along an explicit
  # abstract group isomorphism so MTX sees the same abstract generators.
  moduleD := GModuleByMats(GeneratorsOfGroup(D),F);
  restrictionLabels := [];
  for mi in m22Infos do
    GM := AtlasGroup(mi);
    if GM<>fail and Size(GM)=expectedDerivedOrder then
      iso := IsomorphismGroups(D,GM);
      if iso<>fail then
        mats := List(GeneratorsOfGroup(D),d -> Image(iso,d));
        transported := GModuleByMats(mats,F);
        if MTX.IsomorphismModules(moduleD,transported)<>fail then
          Add(restrictionLabels,mi.repname);
        fi;
      fi;
    fi;
  od;
  if Length(restrictionLabels)=0 then
    Error(Concatenation("could not identify M22 restriction of ",info.repname));
  fi;

  classes := ConjugacyClasses(G);
  involutionClasses := Filtered(classes,cl -> Order(Representative(cl))=2);

  repCounter := repCounter+1;
  if repCounter>1 then AppendTo(out,",\n"); fi;
  AppendTo(out,"    {\"repname\":\"",info.repname,"\",");
  AppendTo(out,"\"m22_restriction_matches\":");
  PrintStringList(out,restrictionLabels);
  AppendTo(out,",\"involution_classes\":[");

  rowCounter := 0;
  for cl in involutionClasses do
    g := Representative(cl);
    outer := not (g in D);
    identity := One(g);
    rankDiff := RankMat(g-identity);
    fixedDim := expectedDimension-rankDiff;
    squareZero := (g-identity)*(g-identity)=Zero(g);
    matches := rankDiff=5 and fixedDim=5 and squareZero;

    pairSwapBasisRank := 0;
    pairSwapBasisVerified := false;
    if matches then
      imageBasis := BaseMat(g-identity);
      if Length(imageBasis)<>5 then
        Error("rank-five image did not return five basis vectors");
      fi;
      pairBasis := [];
      pairChecks := [];
      for u in imageBasis do
        v := SolutionMat(g-identity,u);
        if v=fail then Error("could not solve v*(g-I)=u"); fi;
        a := v;
        b := v+u;
        Add(pairBasis,a);
        Add(pairBasis,b);
        Add(pairChecks,(a*g=b) and (b*g=a));
      od;
      pairSwapBasisRank := RankMat(pairBasis);
      pairSwapBasisVerified :=
        pairSwapBasisRank=10 and ForAll(pairChecks,x->x);
      if not pairSwapBasisVerified then
        Error("J2^5 row did not produce five explicit swapped pairs");
      fi;
    fi;

    if outer then outerInvolutionRows := outerInvolutionRows+1; fi;
    if matches then allMatches := allMatches+1; fi;
    if outer and matches then outerMatches := outerMatches+1; fi;

    rowCounter := rowCounter+1;
    if rowCounter>1 then AppendTo(out,","); fi;
    AppendTo(out,
      "{\"class_size\":",String(Size(cl)),
      ",\"centralizer_order\":",String(Size(G)/Size(cl)),
      ",\"outer\":",JsonBool(outer),
      ",\"rank_g_minus_i\":",String(rankDiff),
      ",\"fixed_dimension\":",String(fixedDim),
      ",\"square_zero\":",JsonBool(squareZero),
      ",\"matches_J2x5\":",JsonBool(matches),
      ",\"pair_swap_basis_rank\":",String(pairSwapBasisRank),
      ",\"pair_swap_basis_verified\":",JsonBool(pairSwapBasisVerified),"}");
  od;
  AppendTo(out,"]}");
od;

AppendTo(out,"\n  ],\n");
AppendTo(out,"  \"representation_count\": ",String(repCounter),",\n");
AppendTo(out,"  \"outer_involution_row_count\": ",String(outerInvolutionRows),",\n");
AppendTo(out,"  \"all_J2x5_match_count\": ",String(allMatches),",\n");
AppendTo(out,"  \"outer_J2x5_match_count\": ",String(outerMatches),",\n");
AppendTo(out,"  \"actual_2b_tate_subquotient_identified\": false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("M22:2 Completion10 outer-involution screen written: reps=",repCounter,
  "; outer involution rows=",outerInvolutionRows,
  "; all J2^5 matches=",allMatches,
  "; outer J2^5 matches=",outerMatches,"\n");
QUIT;
