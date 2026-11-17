# KSW668 F8 geometry and dual-Weyl roadmap — max-cut XXVIII (2026-11-17)

**Status:** Agda source-written, pinned Agda 2.9 kernel NOT run; no curvature-convergence or physical signal acceptance.

## Provenance / reuse before construction

- Original original-model owners: `scripts/ksw668_f8_tt_multipole.py`, `ksw668_f8_fv_source_flux.py` and their KSW668/AdS5 physics owners. Preserve author attribution and original references (Caldwell–Langlois, Thorne, SBP/SAT, numerical wave-method papers). New algebraic cut is separate from original inventions.
- `DASHI/Physics/GR/RiemannTensor.agda` provides Riemann/Ricci/Bianchi **interfaces**, but its canonical model explicitly has a zero-table non-flat blocker.
- `DASHI/Geometry/LeviCivitaBridge.agda` provides the DCHoTT G-structure socket, not proved non-flat Levi-Civita uniqueness.
- `DASHI/Physics/Closure/ContinuumCurvatureSourceSpinTwo.agda` provides the **actual convergence, gauge and curvature-authority record** to instantiate.
- Reuse `KSW668AdS5TTFiniteVolumeFirstCellRationalExact.agda` and `KSW668AdS5MovingNeumannFluxRationalExact.agda`; do not duplicate the effective radial d=3,7,11 or wall-flux lemmas.
- `CMP119CosmologyFiniteWeylConventionFirewallExact.agda` concerns metric/partition Weyl rescaling, NOT the electric Weyl tensor.
- `EverythingTOESymmetryResolved369.agda` uses many ternary/369 carriers; F8 indexing q=0,1,2 for ell=0,2,4 is legitimate, but no Monster/369 geometric equivalence is known.

## New finite readout theorem, not a geometrical promotion

`DASHI/Physics/Gravity/KSW668F8DualElectricWeylReadoutAlgebraExact.agda` reproduces the original algebraic F8 receiver readouts with external rational input `scale=1/t²`, `etaeta=H_etaeta`, `eta=H_eta`, `rr=H_rr`, `lap=Delta3 H`.
Its `dualReadoutCancellation` and `dualReadoutReconstruction` prove the exact finite identity

```
E4 = -(H_etaeta + H_rr)/(4 t²)
E5 = -(H_etaeta + 2 H_eta - Delta3 H)/(2 t²)
E5 - 2 E4 = (Delta3 H + H_rr - 2 H_eta)/(2 t²)
```

These are ring identities. They do not establish 5D covariant Weyl curvature, gauge, Israel coupling, source-to-Weyl continuity or convergence. Independent SymPy algebra check PASS. Pinned Agda kernel OPEN.

## Measured fixed-dr normal/time factorial (max-cut XXVII)

Original TT source, dr=.008 fixed, normal_order=3, t=12:

| Run | dy | actual dt (approx) | E4 | E5 |
|---|---:|---:|---:|---:|
| R0 | .012 | .00179891 | -2.805311616714e-5 | -2.326215693090e-6 |
| RT | .012 | .00089975 | -2.757731022864e-5 | -2.272291814876e-6 |
| RY | .006 | .00089975 | -2.583942604706e-5 | -2.113092373841e-6 |
| RY4 | .003 | .00044995 | -2.537138442114e-5 | -2.061390601964e-6 |

The 32/32 preexisting regression tests passed. R0 to RY4: E4 magnitude -9.56%, E5 -11.38%. Time-only is ~2%, first normal-only relative RT ~6–7%. This does not isolate SAT from the normal bulk stencil and does not prove its convergence order. The separate dr=.004 same-original forward/adjoint outputs E4=-4.85860e-4 and E5=-8.42226e-5 remain strongly grid-sensitive.

## Pareto ordered gates

1. **G0 finite dual-Weyl readout cancellation:** code added and symbolic proof PASS; Agda kernel verification pending.
2. **G1 same-object AdS5 geometry adapter:** original Poincare metric, moving brane normal and induced metric, linearized Riemann/Ricci/Weyl electric projection, 3D TT tensor/gauge and sign conventions; instantiate existing spin-two curvature records with actual witnesses rather than Riemann zero tables.
3. **G2 joint (P,M,U) Israel wall:** same physical source, stage-resolved SAT target, boundary energy and physical trace; a nonzero pointwise SAT mismatch is not itself a continuum boundary error.
4. **G3 fully discrete moving SSPRK3 energy:** z^-3 norm, radial SBP FV, normal SBP2 SAT, time dependence and outer closures, explicit uniform CFL.
5. **G4 higher-Sobolev both-Weyl boundary trace:** H^(4+eps) regularity and bounded source-to-two-Weyl mapping; H1 energy is provably insufficient.
6. **G5 independent dr/dy/dt curvature convergence:** original TT field, intrinsic and projected Weyl, outside-cone negative control. Use 76-interval common seed-mass source carrier; piecewise-constant transfer does not commute with TT differentiation.
7. **G6 original FIO, matter action and detector:** remain OPEN; no physical graviton evidence or superluminal inference.

**Firewall:** source-written ≠ kernel accepted ≠ analytical physical theorem ≠ detected signal. No modification to ESD code or other external attribution owners.
