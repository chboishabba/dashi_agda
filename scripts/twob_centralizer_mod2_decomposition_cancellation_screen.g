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
# This screen computes both irreducible Brauer support and CTBlocks 2-block
# support.  It additionally requires the residual 24 to be the unique
# degree-24 irreducible Brauer character in the table.  Combined with the
# source-native rank-24 quotient, this removes extension ambiguity on that
# residual block: a 24-dimensional module with one degree-24 composition factor
# has composition length one.
#
# The script still does not manufacture the actual integral norm matrix.  It
# certifies the representation-theoretic block/simple-module rigidity used by
# the proof-bearing norm-weld compiler.

if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;
if LoadPackage("ctblocks") <> true then Error("CTBlocks is required"); fi;

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
modPos24:=Positions(modDeg,24);
if Length(pos98304)=0 or Length(pos98280)=0 or Length(pos299)=0 or Length(pos1)=0 then
  Error("required ordinary character degrees 1,299,98280,98304 not all present");
fi;
if Length(modPos24)<>1 then
  Error("expected a unique degree-24 irreducible Brauer character");
fi;
unique24Pos:=modPos24[1];
trivialPos:=pos1[1];

# Map each irreducible Brauer character position to its unique 2-block number.
blocks:=PBlocks(ord,2);
if blocks=fail or Length(blocks)=0 then
  Error("CTBlocks exposes no 2-blocks for the 2B centralizer");
fi;
brauerBlockNumber:=[];
for i in [1..Length(modIrr)] do
  hits:=Filtered([1..Length(blocks)],b -> Position(IBr(blocks[b]),modIrr[i])<>fail);
  if Length(hits)<>1 then
    Error("Brauer irreducible does not lie in a unique CTBlocks 2-block");
  fi;
  Add(brauerBlockNumber,hits[1]);
od;
unique24Block:=brauerBlockNumber[unique24Pos];

VecSub:=function(a,b)
  return List([1..Length(a)],i->a[i]-b[i]);
end;
VecAdd:=function(a,b)
  return List([1..Length(a)],i->a[i]+b[i]);
end;
Nonnegative:=v->ForAll(v,x->x>=0);
WeightedDegree:=v->Sum([1..Length(v)],i->v[i]*modDeg[i]);
Support:=v->Filtered([1..Length(v)],i->v[i]<>0);
BlockSupport:=supp->Set(List(supp,i->brauerBlockNumber[i]));
Sparse:=function(v)
  return Filtered(List([1..Length(v)],i->[i,modDeg[i],v[i],brauerBlockNumber[i]]),x->x[3]<>0);
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
          supp982:=Support(D[i982]);
          supp24:=Support(diff24);
          supp276:=Support(diff276);
          blocks982:=BlockSupport(supp982);
          blocks24:=BlockSupport(supp24);
          blocks276:=BlockSupport(supp276);
          disjoint982_24:=Length(Intersection(Set(supp982),Set(supp24)))=0;
          disjoint982_276:=Length(Intersection(Set(supp982),Set(supp276)))=0;
          blockDisjoint982_24:=Length(Intersection(blocks982,blocks24))=0;
          blockDisjoint982_276:=Length(Intersection(blocks982,blocks276))=0;
          residualIsUnique24:=supp24=[unique24Pos] and diff24[unique24Pos]=1;
          Add(candidates,[i983,i982,i299,diff24,diff276,
            disjoint982_24,disjoint982_276,supp982,supp24,supp276,
            blocks982,blocks24,blocks276,
            blockDisjoint982_24,blockDisjoint982_276,residualIsUnique24]);
        fi;
      od;
    fi;
  od;
od;

# Strong candidate: residual 24 is exactly the unique degree-24 Brauer simple.
strong:=Filtered(candidates,c -> c[16]);

# Support-rigid candidate: old no-overlap criterion.
rigidSupport:=Filtered(strong,c -> c[6] and c[7]);

# Block-rigid candidate: stronger categorical separation.
rigidBlock:=Filtered(rigidSupport,c -> c[14] and c[15]);

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
PrintQuadruples:=function(out,xs)
  local i,x; AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi; x:=xs[i];
    AppendTo(out,"[",String(x[1]),",",String(x[2]),",",String(x[3]),",",String(x[4]),"]");
  od; AppendTo(out,"]");
end;
JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;
PrintCandidate:=function(out,c)
  AppendTo(out,"{\"ordinary_98304_position\":",String(c[1]),
    ",\"ordinary_98280_position\":",String(c[2]),
    ",\"ordinary_299_position\":",String(c[3]),
    ",\"residual_24_sparse_with_block\":"); PrintQuadruples(out,Sparse(c[4]));
  AppendTo(out,",\"residual_276_sparse_with_block\":"); PrintQuadruples(out,Sparse(c[5]));
  AppendTo(out,",\"common_98280_support\":"); PrintNatList(out,c[8]);
  AppendTo(out,",\"residual_24_support\":"); PrintNatList(out,c[9]);
  AppendTo(out,",\"residual_276_support\":"); PrintNatList(out,c[10]);
  AppendTo(out,",\"common_98280_block_support\":"); PrintNatList(out,c[11]);
  AppendTo(out,",\"residual_24_block_support\":"); PrintNatList(out,c[12]);
  AppendTo(out,",\"residual_276_block_support\":"); PrintNatList(out,c[13]);
  AppendTo(out,",\"common_98280_disjoint_from_residual24\":",JsonBool(c[6]));
  AppendTo(out,",\"common_98280_disjoint_from_residual276\":",JsonBool(c[7]));
  AppendTo(out,",\"common_98280_block_disjoint_from_residual24\":",JsonBool(c[14]));
  AppendTo(out,",\"common_98280_block_disjoint_from_residual276\":",JsonBool(c[15]));
  AppendTo(out,",\"residual_is_unique_degree24_simple\":",JsonBool(c[16]),"}");
end;
PrintCandidateList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; PrintCandidate(out,xs[i]); od;
  AppendTo(out,"]");
end;

out:=OutputTextFile("build/twob_centralizer_mod2_decomposition_cancellation_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"ordinary_character_count\":",String(Length(ordIrr)),",\n");
AppendTo(out,"  \"brauer_character_count\":",String(Length(modIrr)),",\n");
AppendTo(out,"  \"two_block_count\":",String(Length(blocks)),",\n");
AppendTo(out,"  \"unique_degree24_brauer_position\":",String(unique24Pos),",\n");
AppendTo(out,"  \"unique_degree24_brauer_block\":",String(unique24Block),",\n");
AppendTo(out,"  \"brauer_irreducible_block_numbers\":"); PrintNatList(out,brauerBlockNumber); AppendTo(out,",\n");
AppendTo(out,"  \"degree_98304_positions\":"); PrintNatList(out,pos98304); AppendTo(out,",\n");
AppendTo(out,"  \"degree_98280_positions\":"); PrintNatList(out,pos98280); AppendTo(out,",\n");
AppendTo(out,"  \"degree_299_positions\":"); PrintNatList(out,pos299); AppendTo(out,",\n");
AppendTo(out,"  \"candidate_count\":",String(Length(candidates)),",\n");
AppendTo(out,"  \"strong_candidate_count\":",String(Length(strong)),",\n");
AppendTo(out,"  \"rigid_support_candidate_count\":",String(Length(rigidSupport)),",\n");
AppendTo(out,"  \"rigid_block_candidate_count\":",String(Length(rigidBlock)),",\n");
AppendTo(out,"  \"candidates\":"); PrintCandidateList(out,candidates); AppendTo(out,",\n");
AppendTo(out,"  \"strong_candidates\":"); PrintCandidateList(out,strong); AppendTo(out,",\n");
AppendTo(out,"  \"rigid_support_candidates\":"); PrintCandidateList(out,rigidSupport); AppendTo(out,",\n");
AppendTo(out,"  \"rigid_block_candidates\":"); PrintCandidateList(out,rigidBlock); AppendTo(out,",\n");
AppendTo(out,"  \"residual_24_unique_simple_identified\":",JsonBool(Length(strong)>0),",\n");
AppendTo(out,"  \"jh_common_98280_plus_residual24_pattern_found\":",JsonBool(Length(strong)>0),",\n");
AppendTo(out,"  \"common_98280_support_separated_from_residual_lanes\":",JsonBool(Length(rigidSupport)>0),",\n");
AppendTo(out,"  \"common_98280_block_separated_from_residual_lanes\":",JsonBool(Length(rigidBlock)>0),",\n");
AppendTo(out,"  \"block_idempotent_split_available\":",JsonBool(Length(rigidBlock)>0),",\n");
AppendTo(out,"  \"actual_norm_map_98280_isomorphism_paid\":false,\n");
AppendTo(out,"  \"actual_tate_exterior_square_weld_paid\":false\n}\n");
CloseStream(out);
Print("2B centralizer mod-2 decomposition cancellation: candidates=",Length(candidates),
  "; strong-unique24=",Length(strong),"; rigid-support=",Length(rigidSupport),
  "; rigid-block=",Length(rigidBlock),"\n");
QUIT;
