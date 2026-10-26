# 4+1 Kaluza–Klein Einstein–Maxwell exact magnetic fixture — 2026-10-22

## What was completed
`scripts/check_bioem_kk_5d_einstein_maxwell.py` constructs the genuine **five-coordinate** Kaluza–Klein metric, not the donor's representative 2+1 metric block, with base Lorentzian g=diag(-1,+1,+1,+1), fibre scalar phi=1, coupling kappa=1, cylinder condition, and A_y=b x. All nonzero field entries and metric coefficients are symbolic SymPy expressions over real symbols (b,x). Script computes the full 5×5 metric, inverse, all Christoffels, the 5×5 Ricci tensor and Ricci scalar. It explicitly computes F=dA, F² using g.

**Verified locally in this session** (not CI):
```
PASS 4+1 metric: detG=-1, R5=-F²/4=-b²/2, R55=F²/4=b²/2
NONVACUUM for b != 0: constant fibre radius with magnetic field violates R55=0
NOT established: universal Ricci decomposition, full Einstein-Maxwell PDE
```

The script additionally verifies the gauge-horizontal mixed equations `R_{mu 5}-A_mu R_{55}=0` for this fixture. This is a real, nontrivial differential-geometric calculation with a magnetic field, not merely a formally declared interface.

## Important consistency result
Even though the scalar-curvature term contains the Maxwell `-1/4 F²` contribution, `R_{55}=F²/4` here. Thus 5D vacuum Einstein equations `R_{AB}=0` at **constant radius** forbid this nonzero pure magnetic field fixture. Dropping the scalar/radion field equation to claim complete 4D Einstein–Maxwell equivalence would be incorrect. Four-dimensional Minkowski base with a nonzero uniform magnetic field is also not a coupled 4D Einstein–Maxwell solution unless gravitational backreaction or suitable stress-energy is included.

## Scope and relationships
- Donor [PR #1239] additive KK horizontal one-form invariance is imported and consumed in this branch; still no general differential-geometric theorem.
- This script independently calculates 4+1 curvature for a nontrivial fixed explicit metric. It does **not** prove the universal 5D scalar-curvature reduction, Einstein–Maxwell field equations with a dynamical scalar, matter currents, topology/smooth gluing, or a physical Kaluza–Klein realisation.
- Next cut: symbolic general 4+1 reduction including variable phi and arbitrary g_{mu nu}, correctly dimensioned action, boundary terms, scalar equation, and gauge/matter coupling. Then instantiate an independently calibrated biological current and NV optical response.
- Framing/C3 and mitochondrial SSP/Ogg frequencies remain independent mathematical and empirical lanes without an identified same-object reduction.

## Attribution and verification
Kaluza–Klein reduction is classical prior physics. Computed fixture and proof-status ledger are DASHI additions. Script executed successfully locally; no CI or Agda kernel verification requested. The computation is a symbolic fixture receipt, **not** a universal formally proved theorem.
