# Yang–Mills Round 41 continuation — concrete combined constraint and SZZ decision tranche

This continuation implements the highest-alpha Yang–Mills subset of the Round-41 roadmap. It does not promote the Clay theorem and does not identify a finite fixed-spacing stochastic gap with the continuum physical Hamiltonian gap.

## Literal P33 block-average rows

`BalabanSelectedBackgroundBlockAverageConstraintMatrixExact.agda` constructs the exact zero-mode/block-average constraint that is actually consumed by the side-four P33 coercivity lane.

A row is

```text
LieCoordinate3 × Axis4,
```

and its physical value is

```text
Q0(h)(a,mu) = sum_x h_mu^a(x).
```

The matrix is not passed by a caller. Its entry is the physical functional evaluated on the literal state basis vector:

```text
L_avg(r,c) = Q0(e_c)(r).
```

The finite-coordinate expansion theorem proves

```text
selectedBackgroundBlockAverageConstraintMatrixApplyExact :
  (L_avg v)(r) = Q0(v)(r),
```

and `selectedBackgroundBlockAverageConstraintPhysicalExact` identifies this with the decoded physical SU(2) bond field.

This closes the exact finite P33 zero-mode block constraint. It does **not** pretend that the transported nonlinear CMP98 block-average derivative has thereby been reconstructed. The repository's existing `BalabanSU2CMP98LiteralLinearization` remains the separate multiscale formula to be connected when the Gate-I lane is lifted beyond the P33 finite carrier.

Primary sources:

- Tadeusz Bałaban, *Averaging Operations for Lattice Gauge Theories*, DOI `10.1007/BF01211042`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- Roger A. Horn and Charles R. Johnson, *Matrix Analysis*, DOI `10.1017/CBO9781139020411`.

## One actual combined `L_A`

`BalabanSelectedBackgroundCombinedConstraintMatrixExact.agda` places the block-average rows and the already-literal covariant gauge rows on one tagged carrier:

```text
SelectedConstraintRow4
  = averageConstraintRow SelectedBlockAverageRow4
  | gaugeConstraintRow GaugeCoordinate4.
```

The combined matrix is defined by cases on this tag and acts on one and the same 3072-coordinate perturbation vector. The theorem

```text
selectedBackgroundCombinedConstraintApplyExact
```

reduces its average rows to the physical block average and its gauge rows to the physical covariant backward divergence. The same operator is also exposed through the generic same-source gluing producer, with exact projections and pointwise uniqueness.

The full Gram matrix is now literally

```text
K_A = L_A L_A*,
```

rather than a supplied compatible-looking matrix. Exact theorems identify its average-average and gauge-gauge blocks. A generic pointwise-disjointness theorem proves a Gram entry is zero whenever every common state-coordinate product is zero.

## Exact raw dimension ledger

`BalabanSelectedConstraintDimensionTowerExact.agda` proves the unreduced row counts:

```text
average rows = 3 × 4     = 12
gauge rows   = 3 × 4^4   = 768
total rows               = 780.
```

It also proves symmetry of the full literal Gram matrix directly from the finite sum. Any future reduced carrier must provide an explicit redundancy dimension satisfying

```text
reducedDimension + redundancyDimension = 780.
```

No rank is silently deleted merely because a pseudoinverse interface accepts a smaller carrier.

## Exact SZZ convention and threshold decision

`BalabanSZZStrongCouplingDecisionExact.agda` cites:

- Hao Shen, Rongchan Zhu and Xiangchan Zhu, *A Stochastic Analysis Approach to Lattice Yang–Mills at Strong Coupling*, DOI `10.1007/s00220-022-04609-1`.
- Dominique Bakry and Michel Émery, *Diffusions hypercontractives*, DOI `10.1007/BFb0075847`.
- Kenneth G. Wilson, *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`.

For SU(2), DASHI's normalized trace is

```text
q0 = (1/2) Re Tr U,
```

and its plaquette action is `1-q0`. The SZZ exponent contribution is `4 beta_SZZ q0`. The exact finite-list theorem proves

```text
SZZExponent(beta,traces)
  = -(4 beta) DASHIWilsonAction(traces)
    + (#plaquettes)(4 beta).
```

Thus the Gibbs measures agree after the explicit coupling conversion

```text
beta_DASHI = 4 beta_SZZ,
```

because the remaining term is configuration independent.

For SU(2) in four dimensions the implemented curvature is

```text
K_S(betaAbs) = 1 - 48 betaAbs
             = 48 (1/48 - betaAbs).
```

The normalized threshold theorem proves both directions

```text
betaAbs < 1/48
  <-> 0 < 1/48 - betaAbs.
```

The file also gives a literal counterexample to the false implication from the selected small-field radius `rho=1/8192` to the SZZ strong-coupling condition: the same radius statement can hold while `betaAbs=1`, which is not below `1/48`.

## RG-to-SZZ decision surface

The only useful hybrid question is represented by `SelectedRGEffectiveActionHessianData`. At some selected scale it requires

```text
Hess S_j(h,h) >= -kappa_j ||h||^2
```

and

```text
kappa_j < RicciFloor_j.
```

The theorem `selectedRGEffectiveBakryEmeryConstantPositive` then proves

```text
0 < RicciFloor_j - kappa_j.
```

This closes the arithmetic and order-theoretic decision step. It does not fabricate the missing physical RG Hessian estimate or a depth at which it holds.

## Remaining finite Gate-I producers

The exact immediate cut is now:

1. Construct the physical redundancy projection for the 780-row combined carrier and trivialize the reduced carrier across the selected-background neighbourhood.
2. Prove a positive reduced Gram floor and rank stability on that common carrier.
3. Construct the exact or certified Moore–Penrose inverse `K_A+` and prove its weighted Combes–Thomas decay.
4. Derive tangent first-variation annihilation from the actual selected minimizer.
5. Construct the literal fifteen source/defect atoms from the same `L_A` and prove exact reconstruction and support.
6. Prove the four physical owner estimates with coefficient sum at most `55/18874368` and preferably strict `Delta_YM>0`.
7. Construct `LiteralSelectedPlaquetteFamily` and invoke the existing `1/32` Hessian theorem.

The SZZ lane changes the later fixed-spacing/infrared options only if a real effective-action Hessian bound constructs `SelectedRGEffectiveActionHessianData`. It does not remove the ultraviolet Balaban RG, the reflection-positive OS bridge, the continuum limit, spectral identification or compact-simple-group coverage.
