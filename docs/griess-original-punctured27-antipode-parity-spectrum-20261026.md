# 2026-10-26 PARETO / Ibrahim max-cut: native punctured27 signed Fourier parity versus Albert J0(26)

## Source roots and exactly which carriers are the same

- **Robert L. Griess Jr. (1990)**, *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131:281–293, DOI 10.1016/0021-8693(90)90176-O: ORIGINAL Griess F3³ graded Albert multiplication and exceptional group; subsequent DASHI rational model is not the original discovery.
- **Jonathan L. Gross (1974)**, *Voltage graphs*, Discrete Math. 9:239–246, DOI 10.1016/0012-365X(74)90006-5; **Jonathan L. Gross and Thomas W. Tucker (1977)**, *Generating all graph coverings by permutation voltage assignments*, Discrete Math. 18:273–283, DOI 10.1016/0012-365X(77)90131-5: ORIGINAL graph voltage/cover theory, not the derived Python scripts.
- **Agda #1249** `DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact`: original **nonwrapping P3³** adjacency, inversion and unique removed origin. This is the sole native graph owner.
- **Agda #1261** `Punctured27NineSheetBridgeExact` and its crystallography/diamond audit: 26=9+8+9, 13=3+6+4 support strata, exact signed-cubic B3 operator. **Agda #1239** and original Ibrahim/OEIS contributors are the older 1+26, 13+13 arithmetic/grade provenance owners.
- **Lean #52** already contains actual `Grade=F3³`, Griess Moufang order13 actor and **native rational Albert J0(26) operator B**, and a computed positive rational `BX=XP` (det X=-729/4096) between the FREE Q-MODULE ON 26 NONZERO GRADES and native Albert J0; this is NOT an adjacency/Jordan-product or physics identification.
- **Agda #1250 actual selected Monster 3B** and **Agda #1260 Eisenstein lambda-nine** are independent current PRs. #1260's additive C81×C243 is not elementary C3^9 merely because both have 3^9 elements; selected Monster 3B full-character source matching is NOT an Albert/P3³ parity intertwiner.

## NEW P0 REAL SOURCE OPERATOR: original P3³ minus its center

Let x range over the original 26 signed grade points and r_a (a=1..13) range over antipodal quotient representatives. In the native Q-linear **function space ON 26 GRAPH SITES** define e_a^+=e_{r_a}+e_{-r_a}, e_a^-=e_{r_a}-e_{-r_a}. The original graph adjacency A26 commutes with native antipode. The exact 26x26 integer H of these columns satisfies

`Hᵀ H = 2 I26,       A26 H = H diag(Aplus,Aminus)`.

Aplus is unsigned 13x13 adjacency on the **actual spatial quotient graph** (24 edges), Aminus is its SIGNED 13x13 voltage adjacency, with nontrivial odd-holonomy XOR four-cycle already owned by #1249. This has NOTHING TO DO with 52 point/line flags of the distinct classical PG(2,3) incidence relation on the same labels.

Independent exact rational SymPy confirms

```
χ_plus(t) = t (t²−14)(t²−2)^5          rank12, nullity1
χ_minus(t)= t^7 (t²−8)^3               rank6,  nullity7
χ_26(t)   = t^8 (t²−14)(t²−8)^3(t²−2)^5    rank18, nullity8.
```

This has CHEAPER PARETO certificates: the 13-axis graph is support-parity bipartite 7+6; for literal original 7×6 incidence blocks Bplus,Bminus,

```
Bplusᵀ Bplus = 2 I6 + 2 J6;
(Bminusᵀ Bminus)^2 = 8 (Bminusᵀ Bminus);
trace(Bminusᵀ Bminus) = 24.
```

These identities determine the spectral factors by elementary rational linear algebra without a costly 26x26 determinant. The signed block's lower spectral radius is a **finite graph-cover holonomy effect**, NOT measured physics/quantum spectral splitting.

## Source ACTOR passes the representation gate but FAILS graph action

The SAME original Griess source-corrected word e01→e12→e20 (order13) commutes with antipode. Its linear action on the signed 26-site basis has **two regular rational 13-cycle modules**, one in each parity sector. Under H the source action is block diagonal (ordinary P13 on plus, signed P13 on minus); both blocks have trace0 for powers 1..12. This explains why `26=(1+12)+(1+12)` is the same *rational C13 isotypy* as the already-computed actual native Albert J0 actor B.

However the SAME P3³ adjacency is NOT invariant: all 48 original punctured edges map to NONedges; full original 27 cube all 54 fail. Exact discrepancy

```
||Pgradeᵀ A26 Pgrade − A26||_F² = 192
even-sector contribution = 76
odd-sector contribution  = 116
projective quotient 13-axis graph preserves only 5/24 edges.
```

Thus positive Q[C13] same-module ≠ original graph/operator/Jordan same-object theorem. New owner Lean #52 `Integration/Griess1990PuncturedCubeAntipodalSpectral.lean` reuses **existing exact Grade/projective rep/path adjacency**, states small 6×6 finite Gram and antipode proof targets and no-go. The SAME independent Python source `scripts/check_griess_punctured27_signed_fourier_operator.py` was added to Lean #52 and Agda #1249. Local independently constructed (not byte-identical committed blob) `/mnt/data/check_griess_punctured27_signed_fourier_operator.py` **EXECUTED PASS** including small-Gram, exact charpolys, regular C13 parity and 76+116=192 discrepancy; receipt `/mnt/data/griess_punctured27_signed_fourier_operator_receipt.json`.

## NEW strongest SAME-JORDAN negative control: parity is not multiplication

The old actual B on rational Albert tracezero26 admits an explicit cyclic basis X (det=-729/4096). Change to parity basis
`Y=X [[I13,I13],[I13,-I13]]`: **det(Y)=1458!=0**, BY=Y diag(P13,P13). Transporting +/- through Y gives a rational chosen involution J on ACTUAL native Albert tracezero26: J²=I, traceJ=0, preserves actual native trace Gram and commutes B. This is a LEGITIMATE REPRESENTATION/isometry, but is chosen by X and not intrinsic to the native exceptional algebra.

Extend J to native Albert J27 fixing the actual unit. It swaps native simple tracezero diagonal roots
`alpha0=(1,-1,0)`, `alpha1=(0,1,-1)`, and sends the ACTUAL primitive Jordan idempotent
`e0=(1,0,0)=(unit+2alpha0+alpha1)/3`
to
`E(e0)=(2/3,2/3,-1/3)`.
But `E(e0)◦E(e0)=(4/9,4/9,1/9) ≠ E(e0)`. A Jordan automorphism cannot destroy a primitive idempotent. This is a **three-coordinate EXACT actual-native product no-go**, far stronger than a mere matching dimension/character and blocks promotion to F4.

Lean #52 NEW `Integration/Griess1990AntipodalParityAlbert26NonJordan.lean` gives a source-written conditional universal no-go for **any unital Q-linear Jordan map swapping these simple roots** using the actual `RationalAlbertNative.RationalAlbert.jordanProduct`, plus an explicitly constructed parity Y and det1458 proof targets. Local exact SymPy `/mnt/data/check_griess_parity_albert_jordan_idempotent_obstruction.py` **EXECUTED PASS**; receipt `/mnt/data/griess_parity_albert_jordan_idempotent_obstruction_receipt.json`. Equivalent portable source script committed to both Lean #52/Agda #1249, consumes the existing rational matrix certificates, no duplicated octonion algebra.

## Proof, attribution and stop rules

**EXACT LOCAL Python PASS**: 26-site spectral/parity, 7x6 Gram matrices, C13-source actor split, graph Frobenius failure, rational Albert parity det1458 and primitive-idempotent failure. **SOURCE-WRITTEN but Lean/Agda kernels NOT RUN:** neither toolchain was installed locally, and exact GitHub-byte script replay was unavailable. The new Lean theorem targets and earlier Agda #1249 13-axis codec must not be promoted to kernel checked until independently compiled. This turn also repaired **64 invalid Agda dot-pattern constructor occurrences** on the original #1249 `HyperfabricPunctured27Projective13OrientationExact.agda`; source needs a focused Agda typecheck (including constructor cases), not new graph-object redesign.

Pareto now: (P0) exact-head kernel acceptance of **original Griess source Q(omega)→native 729 product chain and actual order13 actor**, (P0) kernel accept small 6x6 parity Gram/actual native-idempotent no-go and earlier 26x26 Q[C13] matrix certificate, (P0) Agda source orientation chart/4-edge XOR proof typecheck; (P1) only if actual same-operator selected external data, attempt stronger F4/Monster/physics intertwiners. **No physical, RH, string or Monster 3B theorem from 13/26 counts**.

Strict attribution: Griess Jr. 1990 ORIGINAL Albert source; Gross 1974 / Gross--Tucker 1977 ORIGINAL voltage graph theory; classical algebra for representation/parity; original Ibrahim/OEIS sequence contributor lineage remains attributed to its distinct numerical/path-cube roles; local computational reconstructions by DASHI contributors with ChatGPT assistance. Distinguish source document existence, authored statement, independent corroboration, exact finite computation, source-written formal theorem, kernel-certified theorem and empirical evidence.
