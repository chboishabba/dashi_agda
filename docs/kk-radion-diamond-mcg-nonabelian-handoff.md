# KK five-dimensional scalar-sector assistance for Diamond MCG PR #1238

## New concrete donor
PR #1239 adds `scripts/check_kk_radion_reduced_action.py`, which symbolically varies the **assumed standard** KK reduction (after discarding the total divergence):
```
S4 ∝ ∫d4x sqrt(-g) [ phi R4 - (kappa²/4) phi³ F_{μν}F^{μν} ].
```
It yields the Jordan-frame radion equation
```
R4 - 3 kappa² phi² F²/4 = 0
```
for this vacuum action. At constant phi, the 4D metric field equation has traceless Maxwell source, so R4=0 and the scalar condition requires F²=0. Thus the explicit PR #1238 **pure magnetic** field with F²=2b² cannot support a constant-radius vacuum solution. But a nonzero **null** Maxwell field, F²=0, is *not excluded by this one scalar equation* (further 5D Einstein/Maxwell equations still apply). This is the precise corrected scope of the obstruction: do not infer all nonzero electromagnetic fields are forbidden.

This script does **not** independently derive general R5 from G5. The follow-on owner's missing mathematical theorem is
```
R5 = R4 - (kappa² phi²/4) F² - 2 phi^{-1} Box_g phi,
sqrt(-G5) = phi sqrt(-g4)
```
for a smooth circle-invariant metric, with explicit metric signature / curvature convention. After integration over the fibre the Box(phi) term is a total derivative (subject to boundary conditions). Distinguish Jordan-frame field equations from Einstein-frame conformal transformed scalar kinetic terms.

## Correct dimension-selection audit
Master `DASHI/Geometry/LargePosetContinuumLorentz31.agda` defines `LargePosetContinuumLorentz31Authority` with a supplied `PhysicalLorentzSelection` and its classification mapping all admissible signatures to IsPhysical31. That proves **classification conditional on an input authority**; it does not construct an actual physical refinement system or prove only 3+1 exists from unconditioned axioms. A model in dimensions 2+1 or 4+1 can satisfy ordinary Lorentzian causality, isotropy and finite propagation; additional assumptions must be stated and independently justified to select 3+1.

## Nonabelian/strong-sector donors
In `DASHI/Physics/SFGC/NonAbelian/DepthQuotientIsoSU3.agda` the repo already reuses concrete `W3ToM3Iso`, a finite nonabelian SFGC carrier, and a depth quotient. The owning `SU3ColorSectorNote.agda` explicitly says SU3 is an extension route rather than an established physical gauge group. Separate `ColourFromNcThreeLanesReceipt` records unequal-metric obstruction; `QCDRunningFromCarrierScaleReceipt` leaves actual beta running and dimensional Lambda_QCD anchors open.

Use these exact owners for nonabelian/colour cross-pollination rather than recreating M3 matrices. **5D U1 circle alone is not an SU3 compactification.** Extra compact space or an independently defined nonabelian SU3 principal bundle plus gauge dynamics is necessary. Gravitational/matrix/Monster symmetry evidence cannot substitute for physical QCD beta-function and representation matching.

## Diamond MCG validation route
PR #1238 head 95b6bfd5d202c464e93784c2c29b7cc2c650478a was fetched and its 5D flat-Lorentz magnetic fixture inspected. It asserts R5=-F²/4, R55=F²/4, and mixed Ricci residual for that **particular constant phi=kappa=1**. It does not establish the general scalar identity above, and its own documentation acknowledges physical calibration of NV readout is independently required.

Extend its tests along three independent axes:
1. Phi(x) varying, initially A=0: verify R5=-2 phi^-1 Box phi for a flat four-dimensional base.
2. Nonzero F with phi variable: verify full formula in a tractable Lorentzian fixture and inspect the mixed/55 Einstein equations; compare to the action variation.
3. Curved base g4 and arbitrary smooth phi: derive coordinate-independent or checked tensor identity before claiming general reduction.
Then test measurable NV data with identified source geometry, calibration gains, uncertainties and forward-model consistency.

## Exact commands / certification
```sh
python3 scripts/check_kk_radion_reduced_action.py
python3 scripts/check_bioem_kk_5d_einstein_maxwell.py
```
First command is in #1239, second in sibling #1238. Neither a PR link nor symbolic test alone is an Agda kernel theorem or empirical validation. Preserve donor attribution when cherry-picking.
