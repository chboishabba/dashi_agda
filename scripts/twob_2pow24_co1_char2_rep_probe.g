# Probe AtlasRep/CTblLib for explicit characteristic-two representations of
# the modular-moonshine quotient 2^24.Co1 and test whether any available module
# exposes a 276-dimensional subquotient on which the normal 2^24 acts trivially.
#
# Borcherds--Ryba explicitly left triviality of the normal 2^24 action open in
# the original modular-moonshine construction.  This probe treats it as a
# computational question, not a literature stopping rule.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;

names := ["2^24.Co1","2^24:Co1","2^24.Co_1"];
allInfos := [];
for nm in names do
  for info in AllAtlasGeneratingSetInfos(nm) do Add(allInfos,[nm,info]); od;
od;

# Deduplicate by repname when available.
seen := [];
infos := [];
for pair in allInfos do
  info := pair[2];
  if IsBound(info.repname) then key:=info.repname; else key:=String(info); fi;
  if not key in seen then Add(seen,key); Add(infos,pair); fi;
od;

rows := [];
for pair in infos do
  nm := pair[1]; info:=pair[2];
  char := fail; dim := fail; repname := "unspecified";
  if IsBound(info.characteristic) then char:=info.characteristic; fi;
  if IsBound(info.dimension) then dim:=info.dimension; fi;
  if IsBound(info.repname) then repname:=info.repname; fi;
  constructed := false; groupOrder := 0; moduleDim := 0; factorDims := [];
  normal2Order := 0; normal2TrivialOnModule := false; ten276 := false;
  if char=2 then
    G := AtlasGroup(info);
    if G<>fail then
      constructed := true; groupOrder:=Size(G);
      gens := GeneratorsOfGroup(G);
      if IsMatrixGroup(G) then
        moduleDim := NrRows(gens[1]);
        M := GModuleByMats(gens,GF(2));
        factorDims := List(MTX.CompositionFactors(M),f->MTX.Dimension(f));
        O2 := PCore(G,2); normal2Order:=Size(O2);
        normal2TrivialOnModule := ForAll(GeneratorsOfGroup(O2),x->x=One(G));
        ten276 := 276 in factorDims;
      fi;
    fi;
  fi;
  Add(rows,[nm,repname,char,dim,constructed,groupOrder,moduleDim,factorDims,normal2Order,normal2TrivialOnModule,ten276]);
od;

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;
PrintMaybe:=function(out,x) if x=fail then AppendTo(out,"null"); else AppendTo(out,String(x)); fi; end;

out:=OutputTextFile("build/twob_2pow24_co1_char2_rep_probe.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n  \"representation_info_count\":",String(Length(rows)),",\n  \"rows\":[");
for i in [1..Length(rows)] do
  if i>1 then AppendTo(out,","); fi; r:=rows[i];
  AppendTo(out,"{\"atlas_name\":\"",r[1],"\",\"repname\":\"",r[2],"\",\"characteristic\":"); PrintMaybe(out,r[3]);
  AppendTo(out,",\"declared_dimension\":"); PrintMaybe(out,r[4]);
  AppendTo(out,",\"constructed\":",JsonBool(r[5]),",\"group_order\":",String(r[6]),",\"module_dimension\":",String(r[7]),",\"composition_factor_dimensions\":"); PrintNatList(out,r[8]);
  AppendTo(out,",\"normal_2_core_order\":",String(r[9]),",\"normal_2_core_trivial_on_module\":",JsonBool(r[10]),",\"has_276_composition_factor\":",JsonBool(r[11]),"}");
od;
AppendTo(out,"],\n  \"direct_weight_two_276_module_identified\":false\n}\n");
CloseStream(out);
Print("2^24.Co1 char2 representation probe written: infos=",Length(rows),"\n");
QUIT;
