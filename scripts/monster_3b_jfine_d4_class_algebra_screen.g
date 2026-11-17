# Pure CTblLib class-algebra test for the JFine ζ-phase D4 character.
# NO mmgroup. NO AtlasGroup. NO 196883-dimensional matrix construction.
#
# Prior-art mathematical sources: Wilson (1988); Barraclough–Wilson (2007).
# Class multiplication method: GAP Reference Manual 71.12-7 and 71.12-9
# (ClassMultiplicationCoefficient, MatClassMultCoeffsCharTable).
#
# The MN3B class containing z and z² has exactly TWO elements.
# For a class C_i and its representative g, the multiset of classes
# containing z*g and z²*g is invariant under changing g in C_i.
# It is recovered exactly from [K_z K_i]_k |C_k| / |C_i|.
#
# A C3-PHASE-PRESERVING D4 must have z*g order 3*Order(g) for
# g of order 1,2,4 (coprime to 3). If g inverts z, the order stays
# Order(g). The geometric ζ character is RATIONAL INTEGER, so the
# two ordinary χ values at z*g, z²*g must coincide.
#
# This is a TABLE-LEVEL NECESSARY TEST. A compatible class fusion is
# NOT a constructed subgroup nor a full normalizer intertwiner.
# On a fail/unknown GAP computation, NEVER claim exhaustive no-go.
#
# Run: mkdir -p build && gap -q scripts/monster_3b_jfine_d4_class_algebra_screen.g

if LoadPackage("ctbllib") <> true then Error("requires CTblLib"); fi;
m := CharacterTable("M");
n := CharacterTable("MN3B");
if m=fail or n=fail then Error("missing Monster/MN3B source tables"); fi;
fNtoM := GetFusionMap(n,m);
if fNtoM=fail then Error("missing published MN3B->Monster fusion"); fi;
irr196883 := Filtered(Irr(m),c -> c[1]=196883);
if Length(irr196883)<>1 then Error("degree-196883 character must be unique"); fi;
chi := List(fNtoM,i -> irr196883[1][i]);
orders := OrdersClassRepresentatives(n);
sizes := SizesConjugacyClasses(n);
names := ClassNames(m,"ATLAS");
class3B := Position(names,"3B");
if class3B=fail then Error("Monster 3B class label unavailable"); fi;
centralCandidates := Filtered([1..Length(orders)],i ->
  orders[i]=3 and sizes[i]=2 and fNtoM[i]=class3B);
if Length(centralCandidates)<>1 then
  Error("expected unique size-two central 3B class in MN3B");
fi;
zClass := centralCandidates[1];

# Compute ordinary multiplication-by-{z,z²} entirely from table.
Kz := MatClassMultCoeffsCharTable(n,zClass);
if Length(Kz)<>Length(orders) then Error("class-algebra matrix size mismatch"); fi;

PhaseRealTrace := function(i)
  local k,c,weight,targets,targetOrders,phasePartner,distinct;
  targets := [];
  targetOrders := [];
  phasePartner := [];
  for k in [1..Length(orders)] do
    c := Kz[i][k];
    if c<>0 then
      weight := c*sizes[k]/sizes[i];
      if not IsInt(weight) or weight<0 or weight>2 then
        Error("not an honest two-element central class-product multiplicity");
      fi;
      Append(targets,List([1..weight],q -> chi[k]));
      Append(targetOrders,List([1..weight],q -> orders[k]));
      Append(phasePartner,List([1..weight],q -> k));
    fi;
  od;
  if Length(targets)<>2 or Length(targetOrders)<>2 then
    Error("central 3B class product must create exactly two target elements");
  fi;
  if ForAny(Concatenation([chi[i]],targets),x -> not IsInt(x)) then
    return rec(status:="unknown",reason:="nonintegral ambient character");
  fi;
  if ForAny(targetOrders,q -> q<>3*orders[i]) then
    return rec(status:="inverting",reason:="candidate does not centralize z",
               outputOrders:=targetOrders);
  fi;
  if targets[1]<>targets[2] then
    return rec(status:="nonreal",reason:="nontrivial zeta coefficient",
               outputClasses:=phasePartner,outputTraces:=targets);
  fi;
  if (chi[i]-targets[1]) mod 3<>0 then
    Error("phase-real projected trace not integral");
  fi;
  return rec(status:="real",projected:=(chi[i]-targets[1])/3,
             ordinaryTraces:=[chi[i],targets[1],targets[2]],
             outputClasses:=phasePartner,outputOrders:=targetOrders);
end;

# The selected 3B ζ-sector identity is a unit test for the class algebra.
identity := PhaseRealTrace(1);
if identity.status<>"real" or identity.projected<>65610 then
  Error("identity ζ-sector dimension must be 65610");
fi;

# Exactly the same D4 class-order conventions as the existing five-orbit
# character owner, but a DISTINCT 65610-dimensional target.
r := (1,2,3,4);
s := (2,4);
D4 := Group([r,s]);
tD4 := CharacterTable(D4);
classes := ConjugacyClasses(D4);
cI := PositionProperty(classes,cl -> One(D4) in Elements(cl));
cR2 := PositionProperty(classes,cl -> r^2 in Elements(cl));
cR := PositionProperty(classes,cl -> r in Elements(cl));
cS := PositionProperty(classes,cl -> s in Elements(cl));
cRS := PositionProperty(classes,cl -> r*s in Elements(cl));
if fail in [cI,cR2,cR,cS,cRS] then Error("D4 class identification failed"); fi;
positions := [cI,cR2,cR,cS,cRS];
want := [65610,810,90,2430,2430];
if Size(D4)<>8 or not IsNonabelian(D4) then
  Error("source canonical D4 is not dihedral order eight");
fi;
fusions := PossibleClassFusions(tD4,n);
if fusions=fail then
  Error("PossibleClassFusions returned unknown: no negative result permitted");
fi;

# The source table can identify the real centralizer class character without
# a concrete group G. Every actual D4<=C_N(z) produces one candidate fusion.
passed := [];
unknown := 0;
for f in fusions do
  valid := true;
  vals := [];
  for j in [1..5] do
    p := PhaseRealTrace(f[positions[j]]);
    if p.status="unknown" then
      unknown := unknown+1;
      valid := false;
      break;
    fi;
    if p.status<>"real" or p.projected<>want[j] then
      valid := false;
      break;
    fi;
    Add(vals,p.projected);
  od;
  if valid then
    Add(passed,rec(fusion:=f,canonicalPhaseValues:=vals,
                   monsterClasses:=List(positions,j -> fNtoM[f[j]])));
  fi;
od;

# Output literal surviving fusions, not merely the count.
out := OutputTextFile("build/monster_3b_jfine_d4_class_algebra_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"source\":\"CTblLib: MN3B->M class fusion and MN3B class algebra\",\n");
AppendTo(out,"  \"requires_mmgroup\":false,\n");
AppendTo(out,"  \"requires_actual_group_G\":false,\n");
AppendTo(out,"  \"central_3B_class_position\":",String(zClass),",\n");
AppendTo(out,"  \"geometric_D4_character\":[65610,810,90,2430,2430],\n");
AppendTo(out,"  \"possible_D4_fusions\":",String(Length(fusions)),",\n");
AppendTo(out,"  \"unknown_source_rows\":",String(unknown),",\n");
AppendTo(out,"  \"compatible_class_fusions\":[\n");
for k in [1..Length(passed)] do
  x := passed[k];
  AppendTo(out,"    {\"fusion\":[");
  for j in [1..Length(x.fusion)] do
    AppendTo(out,String(x.fusion[j]));
    if j<Length(x.fusion) then AppendTo(out,","); fi;
  od;
  AppendTo(out,"],\"phase_values\":[65610,810,90,2430,2430]}");
  if k<Length(passed) then AppendTo(out,","); fi;
  AppendTo(out,"\n");
od;
AppendTo(out,"  ],\n");
AppendTo(out,"  \"compatible_fusion_count\":",String(Length(passed)),",\n");
AppendTo(out,"  \"table_level_no_go\":");
if Length(passed)=0 and unknown=0 then
  AppendTo(out,"true");
else
  AppendTo(out,"false");
fi;
AppendTo(out,",\n  \"actual_D4_embedding_paid\":false,\n");
AppendTo(out,"  \"actual_normalizer_intertwiner_paid\":false\n}\n");
CloseStream(out);
Print("Source-typed MN3B class-algebra D4 phase screen written.\n");
Print("possible fusions: ",Length(fusions),"; compatible: ",Length(passed),
      "; unresolved rows: ",unknown,"\n");
QUIT;
