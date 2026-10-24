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
