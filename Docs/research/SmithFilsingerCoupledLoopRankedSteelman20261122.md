# Smith × Filsinger — coupled-tuned-winding BIDI steelman (22 November 2026)

## Purpose and scope
We have NO original physical Filsinger pin diagram. Do not request it as a prerequisite to a logical steelman. Reopened the Filsinger original-transcript source index `Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json` and `Docs/research/DonSmithHighPowerDevices147PageOriginalPDFMaxCut20261112.md` / `Docs/research/SmithFilsingerNonlinearQuadratureMaxCut20261112.md`. The Filsinger record preserves an NST midpoint, a capacitor across a selected coil, two diodes off cap/two off another wire/coil, all forward-facing positive outputs combined, output return to midpoint/Earth/ground, and alleged pole shift and spark discharge. The Smith/Kelly/Darrer compilation independently describes magnetically coupled primary/secondary with split sections and secondary-tuning capacitor(s). These are **historical influences and narration**, not an authenticated original Filsinger pin equality. Four midpoint source-index connections remain 0/4 verified and the raw empirical archive 0/24.

## Reverse ranking, not an invented netlist
**S1 best minimal extra-edge completion:** selected centre-referenced tuned secondary with opposite input terminals U,V and joined positive-going diode groups, a real P-to-M load return and capacitor across that selected winding. Explains half-voltage vs full winding, midpoint, two groups, capacitor, tuning and possible coupled magnetic phase alteration. Requires separately proving whether M belongs to selected tuned winding and real diode pin polarities.

**S2:** capacitor and diode groups tied to one NST half winding, producing effectively half-wave rectification. Preserves midpoint but makes four positive diode packages partially redundant and requires bank smoothing for sustained positive DC.

**S3:** *distinct* tuned, magnetically driven secondary with a deliberately conductive or capacitive/displacement return to the NST midpoint/Earth reference. Strongest mechanism-level steelman for 'one coil' affecting 'another' and pole shift; pays additional unproven return/coupling edges and cannot be declared naturally replenished by Earth.

**S4:** conventional full bridge with DC-negative hard-bonded to M. Real finite-winding model can pass current but pays negative-half clamp loss, requires return diodes with orientations not naturally conveyed by 'all forward' and does not explain cap/coil diode grouping as directly. Retained as lower-fit nonideal alternative, not categorically impossible.

Ranking = ordinal **assumption minimisation and literal speech consistency**, not a Bayesian likelihood or source claim of actual installation. In particular, selecting S1 does not prove its real wiring or power output. Smith's split 17+17-turn L2 belongs to a compiled historical source and is not assigned to the Filsinger reel.

## New exact magnetic-source mechanism: parallel at external port, series in driven circulation loop
For passive coupled coils with primary impedance `Z1=R1+iωL1`, secondary closed induced-loop impedance `Z2=R2+R_L+i(ωL2−1/(ωC))`, and mutual inductance M, assume a source-generated magnetic EMF and *series-equivalent* passive extraction resistance `R_L` inside the secondary loop. This is NOT a literal diode/netlist claim:
```
Vs = Z1 I1 + iωM I2
0  = iωM I1 + Z2 I2
I2 = -iωM I1 / Z2
Zin= Z1 + ω² M² / Z2
```
A capacitor physically across L2 forms a parallel two-terminal pair to an externally imposed voltage. But when internal EMF is distributed along the winding, the closed L2–C circulating loop has a *series* impedance above. The external parallel-tank antiresonance and internal magnetically driven circulating resonance are different **ports and driving conventions**, not contradictory mathematics. For physically passive linear magnetic coupling, impose `M²<=L1 L2`.

At electrical `ω0=1/√(L2 C)`, `I2=−iω0 M I1/(R2+R_L)`: a quadrature current, and a real reflected source resistance `R_ref=ω0²M²/(R2+R_L)>0`. Reversing winding dot orientation changes sign/phase of I2 but **not** the dissipated or extracted real power. It offers a mundane and falsifiable meaning for the claimed 'pole shift', not an actual observed Filsinger flux reversal.

Energy conservation in RMS phasors is exact at all frequencies:
`Re(Vs conjugate(I1))=R1|I1|²+(R2+R_L)|I2|²`.
The capacitor and conservative mutual coupling can shift voltages/currents and transport energy, but supply **no independent average real power**. A genuinely replenished Earth/atmosphere/chemical/RF donor would be an *additional measured signed source port*, not the value of the circuit's reference node.

## Back-solve extraction optimally, with fixed-voltage driver included
For an additional model in which *primary reactance is compensated* at the electrical operating frequency, let `K=(ωM)²`, fixed source RMS voltage Vs and primary source resistance R1>0. Then:
```
I1=Vs(R2+R_L)/[R1(R2+R_L)+K]
I2=−i sqrt(K)Vs/[R1(R2+R_L)+K]
P_useful= K Vs² R_L/[R1(R2+R_L)+K]²
```
The exact unique positive-load optimum is **`R_L*=R2+K/R1`**, rather than `R_L=R2`. The latter assumes a *fixed primary current*, which is not true for the selected finite-voltage driver. The maximum useful output is `K Vs²/[4R1(R1 R2+K)]`, strictly bounded by `Vs²/(4R1)` for R2>0. This shows coupled resonance can shift where output work is harvested **without** delivering unaccounted work. A real rectifier/spark/storage load is nonlinear and must not be replaced by an arbitrary unqualified constant `R_L` in the physical source claim.

Synthetic normalization R1=2,R2=3,K=4,Vs=1 yields R_L*=5, P_useful=1/20, P_drive=2/5, primary heat=8/25, secondary heat=3/100 and useful fraction=1/8. These are exact *model units*, never Filsinger data. Local SymPy 1.14 `/mnt/data/check_smith_filsinger_coupled_coil_bidi.py` **39/39 PASS**, source blob `a1de794883b0f1b1b34dee403f9c4feaa46c974b`; script is local-only, no GitHub CI or Agda kernel acceptance claimed.

## Next BIDI consumer
Stop trying to invent photo-confirmed original connections that the user cannot supply. Route S1 through S4 to existing source-indexed diode, capacitor-bank, spark, transient-charge and Maxwell energy owners as **conditional candidates**. Next perform nonlinear model comparisons with an explicit full-period source/storage budget, fixed physical source assumptions and competing Earth-port funding counterworlds. Account for source driver and reflected coil loading. Preserve unresolved original hardware equivalence as a gate, but do not make it a blocker for mathematical steelman advancement.
