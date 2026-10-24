# Character-theoretic 78 = Sym^2(12) / Sym^2(12*) screen.
# Reuses the existing 6.Suz faithful degree-12 and ALL degree-78 characters; the latter may descend to 3.Suz.
# No mmgroup, subgroup matrix model or complex 196883 representation.
#
# Primary sources: Barraclough and Wilson (2007), character table of N(3B);
# finite-dimensional symmetric-square character identity (classical);
# CTblLib 6.Suz ordinary character and second power map.
#
# This computes mathematical CLASS-FUNCTION equality, not the
# same-object Monster occurrence or the central-quotient descent.
# Print source table ATLAS labels/positions; do not guess 12a/78b.
if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;
tbl := CharacterTable("6.Suz");
if tbl = fail then Error("source table 6.Suz absent"); fi;
irr := Irr(tbl);
labels := AtlasLabelsOfIrreducibles(tbl,"short");
pow2 := PowerMap(tbl,2);
if pow2 = fail or Length(labels)<>Length(irr) then
  Error("second power map / labels unavailable");
fi;
faithful := chi -> ClassPositionsOfKernel(chi) = [1];
p12 := Filtered([1..Length(irr)],i -> irr[i][1]=12 and faithful(irr[i]));
p78 := Filtered([1..Length(irr)],i -> irr[i][1]=78);
if Length(p12)<>2 or Length(p78)<2 then
  Error("expected two faithful degree12 and at least two degree78 characters");
fi;
# DO NOT filter 78 by faithfulness: Sym^2 of a faithful 6.Suz 12
# kills the central order-two element, hence descends through 3.Suz.
central2 := Filtered(ClassPositionsOfCentre(tbl),
  i -> OrdersClassRepresentatives(tbl)[i]=2);
if Length(central2)<>1 then Error("expected unique central involution"); fi;
for a in p12 do
  if irr[a][central2[1]]<>-12 then
    Error("a faithful degree12 6.Suz character must act as -I on centre C2");
  fi;
od;
central3 := Filtered(ClassPositionsOfCentre(tbl),
  i -> OrdersClassRepresentatives(tbl)[i]=3);
if Length(central3)<>2 then Error("expected two nonidentity C3 centre classes"); fi;

# χ_Sym²(V)(g) = (χ_V(g)^2 + χ_V(g²))/2.
# χ_Sym²(V*)(g) is complex conjugate of the above.
# Test complete class functions to avoid degree/label coincidences.
matches := [];
for a in p12 do
  squares := List([1..Length(pow2)],k ->
    (irr[a][k]^2 + irr[a][pow2[k]])/2);
  if squares[1]<>78 then Error("symmetric square of 12 is not degree78"); fi;
  dualSquares := List(squares,v -> GaloisCyc(v,-1));
  for b in p78 do
    isSym := squares = List(irr[b],x -> x);
    isDual := dualSquares = List(irr[b],x -> x);
    equalCentralPhase := irr[a][central3[1]]/12 = irr[b][central3[1]]/78;
    # Source-level character constraint from SAME extended H_729 and the
    # SAME diagonal quotient kernel acting trivially on both tensor factors.
    if isSym and equalCentralPhase then
      Error("direct Sym² cannot preserve a nontrivial central C3 phase");
    fi;
    if isDual and not equalCentralPhase then
      Error("dual Sym² must preserve central C3 phase");
    fi;
    Add(matches,rec(p12:=a,p78:=b,lab12:=labels[a],lab78:=labels[b],
      exactSym2:=isSym,exactDualSym2:=isDual,faithful78:=faithful(irr[b]),
      sameCentralC3Phase:=equalCentralPhase,
      centralInvolution78:=irr[b][central2[1]],
      phase12First:=irr[a][central3[1]]/12,
      phase78First:=irr[b][central3[1]]/78,
      squaredCentralPhase:=irr[a][central3[1]]^2/144));
  od;
od;
anySym := ForAny(matches,r -> r.exactSym2);
anyDual := ForAny(matches,r -> r.exactDualSym2);
# The mathematical central involution obstruction must reject any
# claimed faithful 78 symmetric-square identification.
if ForAny(matches,r -> (r.exactSym2 or r.exactDualSym2) and r.faithful78) then
  Error("a faithful 78 cannot be Sym² of faithful 12: central C2 acts trivially");
fi;
if not anySym and not anyDual then
  Print("Source-level finding: 78 is neither Sym² nor dual Sym² of faithful 12.\n");
fi;
# GAP syntax-safe standalone boolean emitter.
BoolText := function(b)
  if b then return "true"; else return "false"; fi;
end;
out := OutputTextFile("build/monster_3b_suzuki_sym2_character_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"source\":\"CTblLib 6.Suz ordinary Irr, PowerMap(2), central classes\",\n");
AppendTo(out,"  \"checked_full_character_equalities\":true,\n");
AppendTo(out,"  \"faithful12_count\":2,\n  \"degree78_total_count\":",String(Length(p78)),",\n");
AppendTo(out,"  \"symmetric_square_match_exists\":",BoolText(anySym),",\n");
AppendTo(out,"  \"dual_symmetric_square_match_exists\":",BoolText(anyDual),",\n");
AppendTo(out,"  \"rows\":[\n");
for k in [1..Length(matches)] do
  r:=matches[k];
  AppendTo(out,"    {\"position12\":",String(r.p12),
    ",\"position78\":",String(r.p78),
    ",\"atlas_label12\":\"",r.lab12,
    "\",\"atlas_label78\":\"",r.lab78,
    "\",\"faithful78\":",BoolText(r.faithful78),\n    ",\"central_involution78_trace\":",String(r.centralInvolution78),\n    ",\"sym2_equal\":",BoolText(r.exactSym2),
    ",\"dual_sym2_equal\":",BoolText(r.exactDualSym2),
    ",\"same_central_C3_phase\":",BoolText(r.sameCentralC3Phase),
    ",\"common_H729_diagonal_phase_necessary\":",
      BoolText(r.sameCentralC3Phase),
    ",\"central_phase12\":\"",String(r.phase12First),
    "\",\"central_phase78\":\"",String(r.phase78First),
    "\",\"square_phase12\":\"",String(r.squaredCentralPhase),"\"}");
  if k<Length(matches) then AppendTo(out,","); fi;
  AppendTo(out,"\n");
od;
AppendTo(out,"  ],\n");
AppendTo(out,"  \"selected_Monster_12_78_occurrence_matched\":false,\n");
AppendTo(out,"  \"quotient_descent_proved\":false,\n");
AppendTo(out,"  \"actual_D4_subgroup_identified\":false\n}\n");
CloseStream(out);
Print("6.Suz faithful 12 vs 78 symmetric-square table screen written.\n");
QUIT;
