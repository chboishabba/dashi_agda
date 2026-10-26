# Source-bound, mmgroup-free ACTUAL 3B centralizer D4 screen.
#
# Reuses the same GAP/AtlasRep/CTblLib checked model from
# scripts/monster_3b_actual_kernel_structure.g without changing the original
# standalone behavior (it QUITs unless MONSTER3B_REUSE_CHECKED_GROUP=true).
#
# Original mathematical/character sources:
#   Wilson, The odd-local subgroups of the Monster (1988).
#   Barraclough--Wilson, The Character Table of a Maximal Subgroup
#     of the Monster, LMS J Comput Math 10 (2007).
#   Breuer, GAP Character Table Library (CTblLib).
#
# IMPORTANT: no local GAP execution receipt is asserted. The code must NEVER
# identify arbitrary D4 <= N(3B) with a D4 <= C_N(3B)(z): the former can
# interchange zeta and zeta^2. This producer insists on the latter.
#
# Running: mkdir -p build && gap -q scripts/monster_3b_jfine_phase_preserving_d4_screen.g

MONSTER3B_REUSE_CHECKED_GROUP := true;
Read("scripts/monster_3b_actual_kernel_structure.g");

if not IsBound(G) or not IsBound(E) or not IsBound(z) then
  Error("exact checked MN3B group, E and selected 3B z must be present");
fi;
if z <> z^2 and Size(Orbit(G,z,OnConjugation)) <> 2 then
  Error("expected normalizer to invert the selected 3B central element");
fi;

C3B := Centralizer(G,z);
if Size(G) <> 2 * Size(C3B) then
  Error("3B phase-preserving centralizer must be index 2 in its normalizer");
fi;
P2C := SylowSubgroup(C3B,2);
I := One(G);
chiMonsterPositions := Filtered([1..Length(Irr(monster))],
                                i -> Irr(monster)[i][1] = 196883);
if Length(chiMonsterPositions) <> 1 then
  Error("missing unique degree-196883 Monster irreducible");
fi;
chiM := Irr(monster)[chiMonsterPositions[1]];
fusionM := GetFusionMap(mn3b,monster);
if fusionM = fail then Error("MN3B->M fusion absent"); fi;
chiN := List(fusionM, i -> chiM[i]);
classOrders := OrdersClassRepresentatives(mn3b);
classSizes := SizesConjugacyClasses(mn3b);
expectedTrace := rec(identity:=65610,half:=810,quarter:=90,reflection:=2430);

# Source-character value from group-element order + ambient class size.
# These invariants may not uniquely identify a conjugacy class. We accept
# the character value ONLY when *every* possible class has the same value.
# Otherwise the candidate is INCONCLUSIVE, never counted as a no-go.
PossibleTrace := function(x)
  local n,ambientClassSize,compatible,values;
  n := Order(x);
  ambientClassSize := Size(G) / Size(Centralizer(G,x));
  compatible := Filtered([1..Length(classOrders)],
    i -> classOrders[i] = n and classSizes[i] = ambientClassSize);
  if Length(compatible) = 0 then
    return fail;
  fi;
  values := Set(List(compatible,i -> chiN[i]));
  if Length(values) <> 1 or not IsInt(values[1]) then
    return fail;
  fi;
  return rec(value:=values[1],classPositions:=compatible,
             exactClassUnique:=Length(compatible)=1);
end;

# Actual zeta projector. z centralizes x by construction.
ProjectedTrace := function(x)
  local a,b,c,aa,bb;
  if x*z <> z*x then Error("phase-changing element passed to zeta projector"); fi;
  a := PossibleTrace(x);
  b := PossibleTrace(z*x);
  c := PossibleTrace((z^2)*x);
  if a = fail or b = fail or c = fail then
    return fail;
  fi;
  aa := a.value-b.value;
  bb := c.value-b.value;
  if aa mod 3 <> 0 or bb mod 3 <> 0 then
    Error("nonintegral zeta character: class maps/phase not aligned");
  fi;
  return rec(pair:=[aa/3,bb/3],ordinary:=[a.value,b.value,c.value],
             possiblePositions:=[a.classPositions,b.classPositions,c.classPositions],
             allPositionsUnique:=a.exactClassUnique and b.exactClassUnique and c.exactClassUnique);
end;

identityProjection := ProjectedTrace(I);
if identityProjection = fail or identityProjection.pair <> [65610,0] then
  Error("selected 3B phase identity triple must have degree 65610");
fi;

# All D4 subgroups can be conjugated inside this chosen Sylow2 of C3B.
# If an exhaustive search finds no match and every character class is
# resolved, this is a no-go for the *specified* geometric D4 character.
# A limit/ambiguity must be reported as inconclusive, never a negative theorem.
maxPairs := 12000;
pairTests := 0;
d4Tests := 0;
ambiguousD4 := 0;
truncated := false;
matched := false;
firstWitness := fail;
orders4 := Filtered(Elements(P2C),g -> Order(g)=4);
for rr in orders4 do
  S := Normalizer(P2C,Group([rr]));
  candidatesS := Filtered(Elements(S),ss ->
    Order(ss)=2 and not ss in Group([rr]) and rr^ss=rr^-1);
  for ss in candidatesS do
    pairTests := pairTests+1;
    if pairTests > maxPairs then
      truncated := true;
      break;
    fi;
    H := Group([rr,ss]);
    if Size(H) <> 8 or IsAbelian(H) then
      Error("D4 generators unexpectedly failed order-eight test");
    fi;
    d4Tests := d4Tests+1;
    locallyMatched := true;
    locallyAmbiguous := false;
    rows := [];
    for h in Elements(H) do
      t := ProjectedTrace(h);
      if t = fail then
        locallyAmbiguous := true;
        locallyMatched := false;
        break;
      fi;
      if h = I then
        wanted := expectedTrace.identity;
      elif h = rr^2 then
        wanted := expectedTrace.half;
      elif Order(h) = 4 then
        wanted := expectedTrace.quarter;
      else
        wanted := expectedTrace.reflection;
      fi;
      Add(rows,rec(elementOrder:=Order(h),expected:=wanted,
                   zetaPair:=t.pair,ordinaryTraces:=t.ordinary,
                   possiblePositions:=t.possiblePositions,
                   uniquePositions:=t.allPositionsUnique));
      if t.pair <> [wanted,0] then
        locallyMatched := false;
      fi;
    od;
    if locallyAmbiguous then
      ambiguousD4 := ambiguousD4+1;
    elif locallyMatched then
      matched := true;
      firstWitness := rows;
      break;
    fi;
  od;
  if truncated or matched then break; fi;
od;

JsonBool := function(b)
  if b then return "true"; else return "false"; fi;
end;
JsonList := function(xs)
  return Concatenation("[",JoinStringsWithSeparator(List(xs,String),","),"]");
end;

output := OutputTextFile("build/monster_3b_jfine_phase_preserving_d4_screen.json",false);
SetPrintFormattingStatus(output,false);
AppendTo(output,
  "{\n",
  "  \"source_table\":\"MN3B\",\n",
  "  \"centralizer_only\":true,\n",
  "  \"centralizer_index_in_normalizer\":2,\n",
  "  \"actual_checked_extraspecial_E\":true,\n",
  "  \"actual_D4_witness_runtime_observed\":",JsonBool(matched),",\n",
  "  \"screen_exhausted\":",JsonBool(not truncated and not matched),",\n",
  "  \"search_truncated\":",JsonBool(truncated),",\n",
  "  \"pairs_tested\":",String(pairTests),",\n",
  "  \"d4_subgroups_tested_with_duplicates\":",String(d4Tests),",\n",
  "  \"ambiguous_source_class_tests\":",String(ambiguousD4),",\n",
  "  \"certified_no_compatible_D4\":",
    JsonBool(not truncated and not matched and ambiguousD4=0),",\n",
  "  \"geometric_D4_character\":[65610,810,90,2430,2430],\n",
  "  \"identity_zeta_trace\":",JsonList(identityProjection.pair),",\n",
  "  \"matched_first_witness\":[\n"
);
if matched then
  for j in [1..Length(firstWitness)] do
    t := firstWitness[j];
    AppendTo(output,"    {\"element_order\":",String(t.elementOrder),
      ",\"expected\":",String(t.expected),",\"zeta_trace_pair\":",
      JsonList(t.zetaPair),",\"ordinary_trace_triple\":",
      JsonList(t.ordinaryTraces),",\"all_class_positions_unique\":",
      JsonBool(t.uniquePositions),"}");
    if j < Length(firstWitness) then AppendTo(output,","); fi;
    AppendTo(output,"\n");
  od;
fi;
AppendTo(output,"  ]\n}\n");
CloseStream(output);
Print("Source-bound selected 3B centralizer D4 screen written.\n");
if matched then
  Print("Found a matching phase-preserving D4 character (not N(3B) action T).\n");
elif not truncated and ambiguousD4=0 then
  Print("Exhaustive chosen-Sylow2 D4 class-character obstruction.\n");
else
  Print("Inconclusive due to partial search or ambiguous ambient class trace.\n");
fi;
QUIT;
