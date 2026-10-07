# Compute characteristic-two extension invariants of the actual M24 degree-276
# duad permutation module restricted to H2 = M22:2.
#
# This goes strictly beyond Brauer/Jordan-Hoelder data.  It records invariants
# that see modular extension structure:
#   * radical and socle dimensions;
#   * indecomposable summand dimensions;
#   * endomorphism algebra dimension;
#   * a composition-series dimension profile;
#   * the complete 2-singular class fingerprint rank(g-I), fixed dimension,
#     and nilpotency index of (g-I) when unipotent.
#
# A future actual-Tate matrix realization can be compared against this receipt.
# Equality of Brauer characters alone is NOT promoted to equality of these
# extension invariants.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

expectedM24Order := 244823040;
expectedM22d2Order := 887040;
expectedDegree := 276;
F := GF(2);

infos := AllAtlasGeneratingSetInfos("M24");
permInfos := Filtered(infos, info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p276") <> fail);
if Length(permInfos)=0 then
  Error("AtlasRep exposes no M24 p276 permutation representation");
fi;

info := permInfos[1];
G := AtlasGroup(info);
if G=fail or Size(G)<>expectedM24Order then
  Error("failed to construct expected M24 p276 representation");
fi;
H2 := Stabilizer(G,1);
if Size(H2)<>expectedM22d2Order then
  Error("point stabilizer is not M22:2");
fi;

M := PermutationGModule(H2,F);
if MTX.Dimension(M)<>expectedDegree then
  Error("unexpected module dimension");
fi;

rad := MTX.BasisRadical(M);
soc := MTX.BasisSocle(M);
series := MTX.BasesCompositionSeries(M);
factors := MTX.CompositionFactors(M);
endos := MTX.BasisModuleEndomorphisms(M);
indecomp := MTX.Indecomposition(M);

radDim := Length(rad);
socDim := Length(soc);
seriesDims := List(series,Length);
factorDims := List(factors,f -> MTX.Dimension(f));
endoDim := Length(endos);
indecompDims := List(indecomp,x -> MTX.Dimension(x[2]));

NilpotencyIndex := function(n)
  local p,k,z;
  z := Zero(n);
  p := n;
  if p=z then return 1; fi;
  for k in [2..16] do
    p := p*n;
    if p=z then return k; fi;
  od;
  return 0;
end;

classes := ConjugacyClasses(H2);
twoSingularRows := [];
for cl in classes do
  g := Representative(cl);
  ord := Order(g);
  if ord mod 2 = 0 then
    mat := PermutationMat(g,expectedDegree,F);
    id := IdentityMat(expectedDegree,F);
    n := mat-id;
    rankDiff := RankMat(n);
    fixedDim := expectedDegree-rankDiff;
    # nilpotency index is meaningful only when g is a 2-element, i.e. order a
    # power of two; record 0 otherwise.
    tmp := ord;
    while tmp mod 2 = 0 do tmp := tmp/2; od;
    if tmp=1 then ni := NilpotencyIndex(n); else ni := 0; fi;
    Add(twoSingularRows,[ord,Size(cl),rankDiff,fixedDim,ni]);
  fi;
od;

PrintNatList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

PrintRows := function(out,rows)
  local i,r;
  AppendTo(out,"[");
  for i in [1..Length(rows)] do
    if i>1 then AppendTo(out,","); fi;
    r := rows[i];
    AppendTo(out,
      "{\"order\":",String(r[1]),
      ",\"class_size\":",String(r[2]),
      ",\"rank_g_minus_i\":",String(r[3]),
      ",\"fixed_dimension\":",String(r[4]),
      ",\"nilpotency_index_g_minus_i\":",String(r[5]),"}");
  od;
  AppendTo(out,"]");
end;

out := OutputTextFile("build/m22d2_duad276_extension_fingerprint_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"m24_repname\":\"",info.repname,"\",\n");
AppendTo(out,"  \"ambient_dimension\":276,\n");
AppendTo(out,"  \"m22d2_order\":",String(Size(H2)),",\n");
AppendTo(out,"  \"radical_dimension\":",String(radDim),",\n");
AppendTo(out,"  \"socle_dimension\":",String(socDim),",\n");
AppendTo(out,"  \"endomorphism_algebra_dimension\":",String(endoDim),",\n");
AppendTo(out,"  \"composition_series_dimensions\":"); PrintNatList(out,seriesDims); AppendTo(out,",\n");
AppendTo(out,"  \"composition_factor_dimensions\":"); PrintNatList(out,factorDims); AppendTo(out,",\n");
AppendTo(out,"  \"indecomposable_dimensions\":"); PrintNatList(out,indecompDims); AppendTo(out,",\n");
AppendTo(out,"  \"two_singular_class_rows\":"); PrintRows(out,twoSingularRows); AppendTo(out,",\n");
AppendTo(out,"  \"actual_2b_tate_extension_fingerprint_compared\":false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("M22:2 duad-276 extension fingerprint written: rad=",radDim,
  "; soc=",socDim,"; enddim=",endoDim,
  "; indecomp=",indecompDims,
  "; 2-singular rows=",Length(twoSingularRows),"\n");
QUIT;
