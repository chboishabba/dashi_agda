# Actual nonflat 26D NS-NS string background: SU(2) flux × spacelike linear dilaton
Date 2026-10-24. Canonical continuation of [Agda hyperfabric #1249](https://github.com/chboishabba/dashi_agda/pull/1249) and [Lean TOE #84](https://github.com/chboishabba/dashi_lean4/pull/84).

## Prior-source status, not a new string discovery

This is the standard SU(2) WZW / round-S3 NS-NS flux and *spacelike linear dilaton* construction, transplanted into the source-selected 26D **bosonic closed-string effective field equations**. Established worldsheet Sugawara/WZW and NS-NS low-energy action theory remain original mathematical/physical authorities. The Dashi contribution is **an executable source-specific exact rational EOM, geometric connection and finite-level quantum discrepancy audit**, an attribution-respecting selected target for existing 369/VOA/KK/GR operators.

Source action (e.g. [Kevin Wray, *An Introduction to String Theory*, §13.26](https://math.berkeley.edu/~kwray/papers/string_theory.pdf)):
```text
S26 = (1/(2 kappa0²)) integral d26x sqrt(-g)e^(-2 Phi)
      [ R[g] + 4|grad Phi|² - H_ijk H^ijk/12 ],  H=dB locally.
```
Leading NS-NS beta / variational equations (string frame, D=26):
```text
E_g(i,j)  = Ric(i,j) + 2 HessPhi(i,j) - (1/4) H_i m n H_j^m n = 0
E_B(i,j)  = covdiv(e^(-2Phi) H^..._ij) = 0
E_Phi     = R + 4 LaplacePhi - 4|gradPhi|² - H²/12 = 0.
```
This is a two-derivative classical effective calculation, not a full quantized string or all-orders effective action.

## Selected genuine nonflat ansatz, no hidden zero coupling

Let `M26 = R^(1,22) × S³_r` with one Minkowski time direction, 22 flat spatial directions, and round 3-sphere radius `r>0`. Pick `x¹` one of those **flat spacelike** coordinates, not time. Set
```text
Phi = x¹ / r,
H3 = (2/r) vol_(S³_r).
```
On the sphere use the bi-invariant SU2 orthonormal left-invariant frame,
`[e_i,e_j]=(2/r) epsilon_ij^k e_k`,
`nabla_ei ej=(1/r)epsilon_ij^k e_k`. It is torsion-free and metric-compatible.
The actual nonzero curvature `Ric_S3=(2/r²)g_S3`, scalar `R=6/r²`,
`H_i mn H_j^mn = (8/r²)delta_ij`,
`H²=24/r²`, `gradPhi²=1/r²`, HessPhi=LaplacePhi=0.
Therefore:
```text
S³ Einstein beta: 2/r² - (1/4)(8/r²) = 0.
Flat Einstein beta: 0 + 2*0 - 0 = 0.
B EOM:             H parallel in S³, dPhi in orthogonal flat direction -> 0.
Dilaton beta:      6/r² -4/r² - (24/r²)/12 = 0.
```
**This is a literal nonflat coupled leading-order EOM solution** with nonzero source fields, unlike the earlier false flat metric/B example. The FULL 26D geometry exists analytically as the standard SU2 group manifold with the chosen round metric; the executable checks its orthonormal connection, curvature via the structure constants and all source terms exactly. It is not imported from the Agda *three time-slice warped* geometry: same general physical subject, different actual metric.

**GLOBAL B potential warning:** `H3` is a nontrivial closed class on `S³`, so there cannot be a single globally defined smooth `B2` on `S³` with H=dB. The proper global object is patchwise B plus gerbe transitions, subject to flux quantization. `∫_S³ H = 4*pi²*r²`; with standard WZW normalization `r²=k alphaPrime`, `k` is quantized. This local-global failure is part of the acceptance, not an ignorable anomaly.

## Actual 2D conformal/VOA cross-pollination and finite-level negative test

Source WZW Sugawara identity `c_SU2(k) = 3k/(k+2)`, integer `k>=1`; [WZW current algebra](https://adscft.org/cft/two-dimensional-cft-strings-ads3/current-algebras-wzw/). On `R^(1,22)` there are **23 worldsheet free bosons**; one of their spatial coordinate fields has linear-dilaton gradient V and adds `6 alphaPrime V²` to central charge (standard bosonic normalization). Total matter
```text
c_matter = 23 + 6 alphaPrime V² + 3k/(k+2).
```
The bosonic reparametrization ghosts contribute `c_bc=-26`. Thus EXACT criticality requires
```text
alphaPrime V² = 1/(k+2),   c_matter=26,   c_matter+c_bc=0.
```
But the **unshifted leading two-derivative geometry** above with `V=1/r`, `r²=k alphaPrime`, gives `alphaPrime V²=1/k`. Then
```text
c_matter - 26 = 12/[k(k+2)] > 0 at every finite positive k.
```
This explicitly identifies a finite-level quantum correction to the classical balance; the two are compatible at large `k` but NOT exactly the same finite-k physical sigma model. A worldsheet CFT using the source-selected corrected slope is a legitimate existing-construction candidate with central-charge cancellation, **not a kernel proof of BRST cohomology, complete modular sewing, stable vacuum, or α'-exact spacetime equations**. In particular, the bosonic tachyon and linear-dilaton strong-coupling end remain unaddressed.

## Source-owned deliverables and exact checks

- `scripts/check_k27_26d_su2_flux_linear_dilaton.py`: from SU2 Lie bracket, exact rational Koszul/Levi-Civita, Riemann and Ricci, parallel H, sphere/flat B/metric/dilaton NS-NS EOM for six rational radii. All local direct executions PASSED.
- Same script: thirty WZW `k=1..30` rational identities, quantum-corrected `c=26` positive, finite-k classical residual `12/[k(k+2)]` negative. Local PASS.
- Lean #84 `Integration/DASHITOE/K27NonflatNSNSLinearDilatonCut.lean` source writes general ℚ parameter proofs of sphere metric beta, full dilaton beta, timelike-dilaton **counterexample**, exact `k+2` worldsheet charge, and explicit unshifted-slope anomaly. It takes geometric SU2/NS identities as **source premises** (not Lean manifold theorems). Lean/Lake kernel UNVERIFIED.
- Existing SU2/SO3 and group cover formalisms in Agda supply **candidate language only**. The actual `S³=SU2` connected group manifold is not a 27-site balanced-ternary path cube, nor the `C3³` periodic Fourier torus, nor automatically a Monster VOA/BRST state.

## Max-cut roadmap after actual nonflat source completion

**D0** original literal 27D gravity+3form action **FAIL** (125/121) and coefficient-only scalar patch fails automatic EOM. This motivates using 26D theory directly, not unconditional 27D uplift.

**D1** correct physical 26D matter and fields **PASS at leading NS-NS continuum** for chosen S3 flux/linear dilaton. This is stronger than earlier flat toy or target-only EOM record and removes the *mathematical existence* blocker for one nonflat NS-NS continuum example.

**D2** source-published worldsheet CFT via SU2k/current algebra + spacelike background-charge flat boson has exact `c_matter=26` upon `alpha'V²=1/(k+2)`; the large-k geometric ansatz predicts only `1/k`. **Finite-level same-background matching OPEN**. It is crucial not to replace k+2 with k or equate central-charge arithmetic with a full local/unitary BRST CFT.

**D3** B2↔dual C22 positive local Hodge and physical 299+276+1 from the separate K27/M24 source ledger. A full K27 Lie-generator, dual 22-form in a globally nontrivial B gerbe, same stress/metric and genuine on-shell physical Hilbert state remain open.

**D4** M24 p276 ordinary duad != antisymmetric string B2 under natural M24 action, SOURCE-EXACT character 2A 36≠20 and 2B 12≠−12. The ORIENTED duad local Z2 line corrects the representation, but not a Monster Tate 276 or signed-neutral C3 meaning by fiat.

**D5** physical 369/Monster claim would require a selected operator-preserving state/field map from the original hypervoxel/VOA candidate to the SU2 WZW × linear-dilaton 26D CFT and continuum g,B,Phi. No such map is presently identified. NS/YM/RH/other Clay owner estimates receive no automatic theorem promotion from this background.

## Independent high-value subsequent experiment

Give the selected SU2 WZW k and level-corrected linear dilaton a precise physical worldsheet realization, compute Virasoro/BRST nilpotence and physical-state cohomology using existing VOA/TwistedModule owners, and compare the induced spacetime NS-NS background at alpha' corrected order. Fail closed if background level shift or stress does not match. Then ask if the 369 hyperfabric admits an action-preserving operator map at all; do not start from equal numerical labels.
