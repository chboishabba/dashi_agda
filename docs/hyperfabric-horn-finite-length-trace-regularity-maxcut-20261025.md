# Geometric horn no-go: exact trace certificate, finite-depth criterion, and diameter-control counterexample

**2026-10-25 (Brisbane)** · Continuation of [Agda #1249](https://github.com/chboishabba/dashi_agda/pull/1249) and [Lean #84](https://github.com/chboishabba/dashi_lean4/pull/84). Separate author branches: [horn #1244](https://github.com/chboishabba/dashi_agda/pull/1244), [neutrino/Wilson #1247](https://github.com/chboishabba/dashi_agda/pull/1247).

## Source genealogy and choice of object

1. J. W. Alexander (1924), classical horned sphere; *original geometry*.
2. Allen Hatcher, *Algebraic Topology*, Example 2B.2, [pp. 170–172](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf): exterior \(G=\pi_1(\mathbb R^3\setminus B)\) is a **direct limit** of successively larger free groups under the injective maps that replace every generator by its children's commutator. Hatcher explicitly says the resulting group has trivial abelianization and is **highly nonfree**. It is a NONTRIVIAL PERFECT, LOCALLY FREE group, not one free group of infinite rank.
3. Original other worker's dated [horn-neutrino physical regularity ledger](https://github.com/chboishabba/dashi_agda/blob/chatgpt/neutrino-icecube-maxcut-20261024/Docs/physics/HornedSU3ObservableRegularityParetoMaxCut20261024.md), the source horn-stage probe and its reported **50 tests**, including 42 Git-blob-matched source tests and eight exploratory tests, are HIS/HER/THEIR independent receipts and are not rerun or claimed as produced by this continuation.
4. Original #1247 `NeutrinoHornedSU3RootExact` / `NeutrinoHornedWilsonInterferenceExact` owns the selected rational-\(\zeta_3\) matrix and exact Wilson trace. The #1249 D4/Witten conformal embedding is externally published by Lä​cki & Zaugg (1989); it supplies **chiral** \(SU(3)_1\) pointed fusion, NOT selected gauge holonomy on a wild exterior.
5. The original mainline `DASHI/Geometry/FlatFormalDiskHolonomySurface.agda` remains the analytic contract owner: actual normed-unitary fibers, bounded compatible parallel transport, finite-area/loop maps, Stokes, and holonomy-to-identity remain **uninhabited**. Do not substitute finite arithmetic for it.

### Source-conflict quarantine: Riebe (1968)

The openly accessible [institutional abstract](https://digitalcommons.usu.edu/etd/6821/) of N. W. Riebe, *The Fundamental Groups of the Complements of Some Solid Horned Spheres* (1968), says the groups `G^k` are *free of countably infinite rank*. That cannot describe the **same nontrivial Hatcher marked direct-limit group** as constructed in Example 2B.2: its abelianization is zero, whereas a nontrivial free group has nonzero free-abelian abelianization. Possible difference in object/complement/presentation or abstract wording is **NOT RESOLVED** because the full Riebe thesis PDF is access-restricted. Do not erase this provenance discrepancy or replace Hatcher's explicit commutator proof with the abstract's free-group claim.

## New D1: exact selected Wilson root gap with NO numeric eigensolver

Source exact character:
```text
D = 181846007130841
Tr W = (176093404722400 - 19836986431118 ζ3)/D
Re Tr W = 221179426799 / 216225930001.
```
For ANY 3×3 unitary matrix \(W\),
```text
||W-I||_F² = 6 - 2 Re Tr(W),
||W-I||_op² >= (1/3) ||W-I||_F².
```
Therefore the source-selected \(W\) obeys the exact CERTIFICATE
```text
delta_op² >= 854996726408 / 648677790003
         = 1.318060737680021... > 1.
```
This is an exact rational calculation using the ORIGINAL sibling #1247 trace, with the standard elementary Frobenius/operator comparison as background mathematical authority. It proves \(\delta>1\) even if no eigenvalues are computed. The sibling numeric eigenvalue source previously gave \(\delta\approx1.4381884752669252\), consistent with this strictly weaker lower bound. Both statements remain **post-hoc abstract SU3** until physical geometry supplies the group/holonomy representation.

## New D2: finite-depth acceptance criterion, no asymptotic infinite proof required

Unitary group commutator lemma:
```text
d([U,V]) <= 2 d(U) d(V),  d(U):=||U-I||_op.
```
The envelope \(E_0(e)=e, E_{n+1}(e)=2E_n(e)^2\) fixes \(e=1/2\). Thus for a complete Hatcher depth-\(n\) binary generator tree, if **all** descendants at that depth obey \(d(U_w)\le1/2\), then \(d(U_{root})\le1/2\) at **any finite depth**. The exact selected root has \(d(W)>1\) and hence violates the conclusion.

On actual based/whiskered geometric loops, compatible unitary parallel transport gives \(d(U_w)\le M\operatorname{length}(\gamma_w)\) when \(M\) bounds the connection norm along each short local meridian in compatible gauge charts. Conjugating by stems to the single root base point preserves operator norm. Therefore a single **certified depth \(n\)** satisfying
```text
sup_{|w|=n} length(gamma_w) <= ell_n,  M*ell_n <= 1/2
```
would refute the source-selected nontrivial root for that bounded-connection model. The original infinite-depth bound gives the sharper \(M\ge (2\delta)^{1/2^n}/(2\ell_n)\), still CONDITIONAL on \(\ell_n\) and \(M\). For illustrative \(\ell_n=2^{-n}\), the sibling's \(n=12\) lower bound is about \(2048.528334\), but that loop-length law is **not proved** for the selected embedding.

The previously open bottleneck has become a precise *finite geometric witness*: source a geometrically faithful representative of every marked Hatcher child, prove its homotopy class in the actual complement (with whiskers), quantify Euclidean or source-spacetime metric **length**, and establish compatible SU3 unitary transport. No mere horn drawing, tube diameter, flatness label, or group presentation pays these terms.

## New D3: exact negative control — small DIAMETER does not imply small holonomy

A smooth SU(3) connection on ordinary \(\mathbb R^2\), embedded diagonally with \(H=\operatorname{diag}(1,-1,0)\), has
```text
A = (iH/2)(-y dx + x dy),   F_A = iH dx∧dy ≠ 0.
```
Let \(\gamma_n\) be the circle of radius \(1/n\) traversed **\(n^2\) times**. Then
```text
diam(image gamma_n) = 2/n -> 0,
||A|| on the circle <= 1/(2n) ->0,
length(gamma_n) = 2π n -> infinity,
∮gamma_n A = iπ H,
Hol(gamma_n)=diag(-1,-1,1),  ||Hol-I||op=2 for EVERY n.
```
This is an EXACT nonflat, smooth, bounded connection and *repeated-winding* counterexample to the invalid argument `shrinking image diameter + bounded A => holonomy identity`. It is **NOT** a flat connection, nor a simple small horn meridian. In a source horned geometry where genuinely SIMPLE meridian circles can be chosen with length proportional to their tube radii, the stronger length criterion may still hold. But finite-stage tube **diameter** alone will not establish it, and a global basepoint's nonshrinking whisker length is not a problem if one separately isolates small local loops and exploits unitary conjugacy of holonomy.

New executed original regression `scripts/check_horn_geometry_length_trace_maxcut.py`:
- exact selected Galois/Frobenius rational certificate;
- 33 exact rational fixed-envelope depths;
- source-consistent 7 finite-depth gap/lower-bound controls;
- 7 exact analytic repeated-winding examples with fixed flux, shrinking diameter and diverging length.
Local Python source executed PASS; committed script exists in GitHub, byte-exact blob comparison remains to be confirmed.

Lean #84 `Integration/DASHITOE/HornWittenRegularityAndChargeCut.lean` appends source-written pure rational theorems for the exact trace lower bound \(>1\), finite-depth contradiction conditional on its true **external** analytic norm inequality, and \(n^2(1/n)^2=1\) / length-growth counterexample coefficients. **Lean/Lake kernel not run; no actual source connection is built by the Lean file.**

## Next Pareto / proof inventory

| Gate | Deliverable | Status |
|---|---|---|
| R0 | exact-source Hatcher group vs 1968 abstract; original worker attribution | Hatcher directly verified; Riebe discrepancy quarantined |
| R1 | selected source unitary trace ⇒ \(\delta>1\) exact rational, no eigenvalues | **PASS** algebraically/local Python |
| R2 | full tree finite cutoff and quantitative leaf-growth | **PASS conditional on physical group/holonomy tree** |
| R3 | diameter-only wrong inference control | **PASS exact smooth nonflat SU3 counterexample** |
| R4 | actual marked geometric meridians of literal three-copy wild embedding and **length** | **OPEN — priority** |
| R5 | compatible bounded SU3 connection vs singular/defect escape; same spectral physics | **OPEN** |
| R6 | Witten D4 chiral \(SU3_1\) fusion, Monster C27, other C3 and selected Wilson W same physical operator | **NOT IDENTIFIED; direct abelian-character interpretation already rejected** |
| R7 | Hosotani matter determinant, anomaly-safe field content and predictive independent measurement | **OPEN** |

**Strongest remaining mathematical delivery:** either a source-coordinate meridian/collar construction with certified \(\ell_n\to0\) and fixed gauge compatibility, or a counterexample showing the intended embedding lacks that property. Do not claim the stage-by-stage handles themselves provide this length bound absent a metric/meridian witness.** No CI needed**, but Agda and Lean kernel proofs remain an independent task. No direct YM/NS/Clay solution follows from these finite bounds.


## Exact TOPOLOGICAL mark discriminator (added after synthetic-collar test)

The local synthetic straight-cylinder coordinate family now does more
than declare `markMissing`: for each parent word of depths 0..6
(\(1+2+4+8+16+32+64=127\) selected parent loops), the
parent transverse circle has planar winding vector **(1,0)**
around the two child tube cores at the next level, whereas the
supposed Hatcher commutator \([m_{w0},m_{w1}]\) has
abelianized winding vector **(0,0)**. The mismatch is checked from
EXACT rational centre/radius inequalities
`|c_parent-c_child0|=0<R_parent<|c_parent-c_child1|`.
Thus the synthetic straight-cylinder control **provably fails**
the original required Hatcher marking, despite passing all
collar clearance and short-length checks. This is a real
finite stage *topological* no-go for the control, not merely
a comment about the absence of linking. The actual Hatcher
two-tube replacement block must supply a different van Kampen
inclusion map that sends parent to a child commutator.

Updated script `check_horn_a5_single_branch_collar_cut.py`
was byte-exact locally executed and has matching committed
Git blob `e0e6b6cad6f3c5653c1097759facc12c76846ad2`.
Local exact checks cover all 60 A5 permutations, 3600 A5
commutator pairs, 8 selected local collar levels and these
127 source-marking rejection controls. Source original
A5 horn quotient remains owned by #1244.


## 2026-10-25 sharper Hatcher one-branch SU3 theorem: 2^n rather than 4^n

**New canonical source/implementation:** docs/hyperfabric-horn-onefastbranch-sharp-unitary-maxcut-20261025.md and scripts/check_horn_single_fast_branch_unitary_cut.py in Agda #1249; Integration/DASHITOE/HornSingleFastBranchUnitaryCut.lean in Lean #84. Original Hatcher Example 2B.2 (printed pp.171–172), original horn A5/VOA #1244, original selected W/noninteger trace #1247 and existing FlatFormalDiskHolonomySurface retain authorship/ownership.

For any UNITARY A,B, the elementary exact identity ||[A,B]-I||op=||AB-BA||op gives the stronger d([A,B])<=2 min(d(A),d(B)); previous valid bound 2 d(A)d(B) <=4d(A) is nonoptimal for a chosen child. Thus for ANY selected TRUE FLAT Hatcher horn group representation G→SU3, and ANY one depth-n descendant w, d(Uroot)<=2^n d(Uw). Given a genuinely source-marked local meridian length L_w and compatible uniform connection bound M, d(Uroot)<=2^n M L_w. Exact previously checked selected W source character certifies d(W)>1. Therefore ANY chosen depth with 2^n M L_w<=1 contradicts W, without finite-image or full-depth-smallness assumptions. A geometrically marked path shrinking as L0*q^n with q<1/2 and M bounded would settle the bounded-FLAT-selected-W case conditionally. **Source-true linked marked geometry and loop LENGTH are STILL UNPROVED**; do not promote Hatcher's topological picture into metric q<1/2.

Exact local rational rates for hypothetical M=100,L0=1: q=1/8 depth4, q=1/5 depth6, q=1/4 depth7, q=1/3 depth12; q>=1/2 gives no crossing. Additional heterogenous *complete* binary tree certificate 2 d(root)<=∏(2 epsilon_leaf), checked across nine exact test trees, complements one-branch criterion. Agda Python reference PASS; current remote Git script exists. Lean new native theorem source conditional on explicit normed-commutator/flatness premises, **Lean/Lake kernel UNVERIFIED**.

For CURVED connections, π1 group relations do not imply equality of Wilson matrices on homotopic loops unless a curvature/homotopy (non-Abelian Stokes) error is controlled; a genuine literal loop concatenation is another possible source but must match the independently selected root loop. No claim of actual linked three-dimensional Z-block, Witten/Monster/TOE source action or Clay estimate.
