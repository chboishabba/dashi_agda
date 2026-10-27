# KK/E6 orbifold anomaly max-cut: source audit and 2026 spectrum consumer (2026-10-25)

## Status and attribution
Owner: physical KK PR #1241 in `chboishabba/dashi_agda`. The first-Tits/trinification algebra stays owned by Agda #1106; Casimir/stress by #1165; the TOE bridge by #1217; Lean mirror #80 is downstream. This audit does not replace the original source implementations or constitute a kernel proof.

### Exact existing source checks
- `scripts/check_kk_e6_orbifold_fixed_plane_anomaly.py` proves **only** that opposite-boundary CS inflow cannot remove a nonzero *integrated* UV anomaly.
- `scripts/check_kk_e6_orbifold_cs_wz_anomaly_transfer.py` tests the stronger conditional ansatz: fermionic local variations `(I6/2,I6/2)`, CS transfer `(+I6/2,-I6/2)` and one-end `-theta X4/2` with `delta(theta)=2alpha`. It algebraically cancels independent endpoint parameters in the **declared unnormalised polynomial trace lattice**. It does **not** establish allowed quantised CS levels or globally well-defined exponentiated WZ action.
- `scripts/check_kk_e6_27_axion_charge_lattice.py` excludes an elementary colour/SU2L/SU2R-invariant charge-(1,-1) VEV in the **single selected 27**, not in all representations or composites. Its old symmetric two-endpoint half-phase obstruction is no longer a no-go for the one-end CS/WZ ansatz.
- `scripts/check_kk_e6_orbifold_interval_higgs_bvp.py` and `scripts/check_kk_e6_orbifold_interval_even_hessian.py` replace the invalid constant-profile extremum with a nonconstant *restricted* interval BVP and a numerical 18-component parity-even fluctuation check; a finite mesh spectrum is not a continuum certified spectral bound.

## Original literature; distinguish original results from these local tests
1. Scrucca, Serone, Silvestrini & Zwirner (2002), *Anomalies in orbifold field theories*, Phys. Lett. B **525**, 169–174, DOI **10.1016/S0370-2693(01)01430-7**, preprint **hep-th/0110073**: integrated cancellation can conceal nonzero fixed-point anomalies.
2. von Gersdorff & Quirós (2003), *Localized anomalies in orbifold gauge theories*, Phys. Rev. D **68**, 105002, DOI **10.1103/PhysRevD.68.105002**, preprint **hep-th/0305024**: globally surviving four-dimensional gauge anomalies are distinguished from globally vanishing fixed-point anomalies; four-form GS/CS cancellation alone does not remove arbitrary surviving 4D anomalies.
3. Hosotani (2026-08-19), *Anomaly flow and anomaly cancellation*, Phys. Rev. D **114**, 035026, DOI **10.1103/ds9g-5m21**: in the *studied warped gauge-Higgs-unification theory*, the full KK tower contributes to an anomaly flow with fifth-dimensional AB phase, and the total is expressible through brane gauge profiles. **Not automatically a theorem for this E6 interval model.**

## Pareto-ranked gates and executable consumers
**P0 — global anomaly (decisive admissibility):**
- Declare the **actual** orbifold gauge group `G=(SU(3)^3 ...)/Gamma`, spin/tangential structure, bundle and boundary gauge-transformation classes, and the physical generator normalisations. Do not silently identify naive integer trace monomials with integral characteristic classes.
- Derive consistent 5D fermion anomaly descent including APS/eta and the regulator, with fixed-point signs and chirality. Derive the exponentiated CS5 + one-boundary `Chi33` WZ phase for large allowed transformations.
- Test the same endpoint cancellation for *all* allowed small and large gauge transformations and for the `F_L-F_R` direction **without** giving a Stückelberg mass to the intended photon.
- Failure of any one is a model rejection or a forced changed source, not another numerical fit.

**P1 — full KK anomaly/spectral cross-check:**
- Replace the 18-real scalar-only fluctuation sector by coupled gauge, fermion, ghosts, odd scalar modes, boundary mixings, and full `y`-dependent background with canonical 5D kinetic normalisations.
- Compute anomaly contributions of successive KK cutoffs and their regulator-consistent limit; compare with independent endpoint descent. The 2026 Hosotani result motivates this *comparison*, not direct import of its warped-model formula.
- Independently certify the lowest complete physical fluctuation eigenvalue by interval variational/coercivity or rigorous enclosure, after quotienting genuine gauge zero modes. Grid refinement alone is not a continuum proof.

**P2 — actual observable same-action producer:**
- One action, with matched units, must generate the radion effective potential, backreacted interval background, matter masses, **one physical photon**, and bulk-plus-boundary stress. The smooth-circle Casimir coefficients cannot be transplanted unchanged to the orbifold.

**P3 — phenomenological discrimination:**
- Only after P0–P2 close, compute chiral generation count, exotic mass bounds, photon charge normalisation, electroweak data and gravity/KK observables. Compare with the vectorlike smooth-circle and brane-localised SM controls on equal assumptions.

## Snowball/Ibrahim/source-root discipline
For each cited paper, follow its *original references* and *later citing results* only where they introduce a new theorem, method, explicit counterexample or discriminating observable. Count the 2001 preprint and its 2002 published version as **one root**, likewise the 2003 preprint and journal version. Do not count reprints, concordant explanations, or code assertions as independent confirmation. New claims require source date, authors, exact model assumptions, and local same-object witness.

## Current verdict
The one-end CS/WZ computation is a genuine **conditional finite-algebra advance**, not quantum anomaly cancellation. The nonconstant interval background is a stronger **restricted classical/numerical** result, not a stable five-dimensional quantum vacuum. Global quantisation/descent is the most useful current max-cut; complete KK spectrum and same-action stress follow only if it succeeds.
