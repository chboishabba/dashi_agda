# Identify the outer involution classes of H2=M22:2 inside M24, transport them
# to the natural 24-point M24 action, and compute the full characteristic-two
# extension fingerprint on the 276-duad module.
#
# For an involution h over F2, N=h-I is square-zero and
#   dim Hhat^0(<h>,M) = dim ker N - dim im N = dim M - 2 rank N.
# Thus `iterated_tate_defect_dimension` is precisely the 2-singular invariant
# an actual 2B-pure Klein-four Tate computation should reproduce if the Tate
# head has the same extension structure as the duad module.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;

F := GF(2);
expectedM24Order := 244823040;
expectedM22d2Order := 887040;
expectedDegree := 276;

p276Infos := Filtered(AllAtlasGeneratingSetInfos("M24"), info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p276")<>fail);
p24Infos := Filtered(AllAtlasGeneratingSetInfos("M24"), info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p24")<>fail);
if Length(p276Infos)=0 or Length(p24Infos)=0 then
  Error("need M24 p276 and p24 AtlasRep actions");
fi;
G276 := AtlasGroup(p276Infos[1]);
G24 := AtlasGroup(p24Infos[1]);
if G276=fail or G24=fail or Size(G276)<>expectedM24Order or Size(G24)<>expectedM24Order then
  Error("failed to construct expected M24 actions");
fi;
H2 := Stabilizer(G276,1);
if Size(H2)<>expectedM22d2Order then Error("duad stabilizer is not M22:2"); fi;
D := DerivedSubgroup(H2);

isoM24 := IsomorphismGroups(G276,G24);
if isoM24=fail then Error("could not identify p276 M24 with p24 M24"); fi;

CycleLengths := function(p)
  local cyc;
  cyc := Cycles(p,[1..24]);
  return SortedList(List(cyc,Length));
end;

JsonBool := function(x) if x then return "true"; else return "false"; fi; end;
PrintNatList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

classes := ConjugacyClasses(H2);
rows := [];
for cl in classes do
  g := Representative(cl);
  if Order(g)=2 and not (g in D) then
    mat := PermutationMat(g,expectedDegree,F);
    n := mat-IdentityMat(expectedDegree,F);
    r := RankMat(n);
    fix := expectedDegree-r;
    defect := expectedDegree-2*r;
    g24 := Image(isoM24,g);
    Add(rows,[Size(cl),Size(H2)/Size(cl),r,fix,defect,CycleLengths(g24)]);
  fi;
od;
if Length(rows)=0 then Error("no outer involution classes in M22:2"); fi;

out := OutputTextFile("build/m22d2_outer_class_m24_cycle_tate_defect_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n  \"m22d2_order\":887040,\n  \"ambient_dimension\":276,\n  \"outer_involution_rows\":[");
for i in [1..Length(rows)] do
  if i>1 then AppendTo(out,","); fi;
  rr:=rows[i];
  AppendTo(out,"{\"class_size\":",String(rr[1]),
    ",\"centralizer_order\":",String(rr[2]),
    ",\"rank_g_minus_i\":",String(rr[3]),
    ",\"fixed_dimension\":",String(rr[4]),
    ",\"iterated_tate_defect_dimension\":",String(rr[5]),
    ",\"m24_p24_cycle_lengths\":");
  PrintNatList(out,rr[6]);
  AppendTo(out,"}");
od;
AppendTo(out,"],\n  \"target_class_1386_640_found\":",
  JsonBool(ForAny(rows,r -> r[1]=1386 and r[2]=640)),",\n");
AppendTo(out,"  \"actual_2b_iterated_tate_defect_compared\":false\n}\n");
CloseStream(out);
Print("M22:2 outer-class M24 cycle / Tate-defect screen written: rows=",Length(rows),"\n");
QUIT;
