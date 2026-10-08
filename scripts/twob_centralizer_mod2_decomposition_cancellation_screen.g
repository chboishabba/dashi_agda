# Test the 2-modular decomposition-matrix version of the source-native
# plus/minus cokernel candidate for C_M(2B)=2^(1+24).Co1.
#
# Ordinary weight-two branching:
#   196884 = 98304 + 98280 + (1 + 299).
# The Tate cokernel dimensions suggest that modulo 2 the common 98280 content
# cancels and the residual difference is the natural 24-dimensional Co1 module:
#
#   [98304]_2 - [98280]_2 = [24],
#   [98280]_2 + [1+299]_2 - [98304]_2 = [276].
#
# This screen asks the actual 2-modular decomposition matrix whether such a
# nonnegative pair exists.  It records Brauer-character multiplicity vectors,
# not an extension/module isomorphism; the actual norm-map placement remains a
# separate same-object seam.

if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;

ord:=CharacterTable("2^1+24.Co1");
if ord=fail then Error("2B-centralizer ordinary table unavailable"); fi;
mod:=ord mod 2;
if mod=fail then Error("2B-centralizer 2-modular Brauer table unavailable"); fi;
D:=DecompositionMatrix(mod);
if D=fail then Error("2B-centralizer decomposition matrix unavailable"); fi;

ordIrr:=Irr(ord); modIrr:=Irr(mod);
ordDeg:=List(ordIrr,x->x[1]);
modDeg:=List(modIrr,x->x[1]);
pos98304:=Positions(ordDeg,98304);
pos98280:=Positions(ordDeg,98280);
pos299:=Positions(ordDeg,299);
pos1:=Positions(ordDeg,1);
if Length(pos98304)=0 or Length(pos98280)=0 or Length(pos299)=0 or Length(pos1)=0 then
  Error("required ordinary character degrees 1,299,98280,98304 not all present");
fi;
trivialPos:=pos1[1];

VecSub:=function(a,b)
  return List([1..Length(a)],i->a[i]-b[i]);
end;
VecAdd:=function(a,b)
  return List([1..Length(a)],i->a[i]+b[i]);
end;
Nonnegative:=v->ForAll(v,x->x>=0);
WeightedDegree:=v->Sum([1..Length(v)],i->v[i]*modDeg[i]);
Sparse:=function(v)
  return Filtered(List([1..Length(v)],i->[i,modDeg[i],v[i]]),x->x[3]<>0);
end;

candidates:=[];
for i983 in pos98304 do
  for i982 in pos98280 do
    diff24:=VecSub(D[i983],D[i982]);
    if Nonnegative(diff24) and WeightedDegree(diff24)=24 then
      for i299 in pos299 do
        row300:=VecAdd(D[trivialPos],D[i299]);
        diff276:=VecSub(VecAdd(D[i982],row300),D[i983]);
        if Nonnegative(diff276) and WeightedDegree(diff276)=276 then
          Add(candidates,[i983,i982,i299,diff24,diff276]);
        fi;
      od;
    fi;
  od;
od;

# Strong candidate: residual 24 is a single irreducible Brauer character of
# degree 24, not merely a virtual sum of smaller factors.
strong:=Filtered(candidates,c ->
  Sum(c[4])=1 and Length(Sparse(c[4]))=1 and Sparse(c[4])[1][2]=24);

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
PrintTriples:=function(out,xs)
  local i,x; AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi; x:=xs[i];
    AppendTo(out,"[",String(x[1]),",",String(x[2]),",",String(x[3]),"]");
  od; AppendTo(out,"]");
end;
PrintCandidate:=function(out,c)
  AppendTo(out,"{\"ordinary_98304_position\":",String(c[1]),
    ",\"ordinary_98280_position\":",String(c[2]),
    ",\"ordinary_299_position\":",String(c[3]),
    ",\"residual_24_sparse\":"); PrintTriples(out,Sparse(c[4]));
  AppendTo(out,",\"residual_276_sparse\":"); PrintTriples(out,Sparse(c[5]));
  AppendTo(out,"}");
end;
PrintCandidateList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; PrintCandidate(out,xs[i]); od;
  AppendTo(out,"]");
end;
JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;

out:=OutputTextFile("build/twob_centralizer_mod2_decomposition_cancellation_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"ordinary_character_count\":",String(Length(ordIrr)),",\n");
AppendTo(out,"  \"brauer_character_count\":",String(Length(modIrr)),",\n");
AppendTo(out,"  \"degree_98304_positions\":"); PrintNatList(out,pos98304); AppendTo(out,",\n");
AppendTo(out,"  \"degree_98280_positions\":"); PrintNatList(out,pos98280); AppendTo(out,",\n");
AppendTo(out,"  \"degree_299_positions\":"); PrintNatList(out,pos299); AppendTo(out,",\n");
AppendTo(out,"  \"candidate_count\":",String(Length(candidates)),",\n");
AppendTo(out,"  \"strong_candidate_count\":",String(Length(strong)),",\n");
AppendTo(out,"  \"candidates\":"); PrintCandidateList(out,candidates); AppendTo(out,",\n");
AppendTo(out,"  \"strong_candidates\":"); PrintCandidateList(out,strong); AppendTo(out,",\n");
AppendTo(out,"  \"jh_common_98280_plus_residual24_pattern_found\":",JsonBool(Length(strong)>0),",\n");
AppendTo(out,"  \"actual_norm_map_98280_isomorphism_paid\":false,\n");
AppendTo(out,"  \"actual_tate_exterior_square_weld_paid\":false\n}\n");
CloseStream(out);
Print("2B centralizer mod-2 decomposition cancellation: candidates=",Length(candidates),
  "; strong=",Length(strong),"\n");
QUIT;
