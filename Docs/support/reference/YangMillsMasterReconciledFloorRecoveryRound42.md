# Yang–Mills Round 42 — master-reconciled floor and recovery

This note indexes the concrete theorem tranche on
`agent/ym-clay-alpha-round42-master-reconciled-floor-recovery`.
It is intentionally secondary to the Agda modules; the mathematical results
live in the checked theorem surfaces named below.

## Physical finite operator

The selected constraint remains the literal tagged operator

`L_A : Q^3072 -> Q^780`, with 12 block-average rows and 768 gauge rows.

The identity-background gauge transpose is proved pointwise to be the negative
periodic forward gradient.  On componentwise-mean-zero gauge multipliers,

`actualFlatGaugeGramReducedFloor`

proves

`(1/16) ||lambda||^2 <= ||L_gauge,1^* lambda||^2`.

The selected-background forward defect estimate is converted into an adjoint
estimate by a literal finite Cauchy–Schwarz/Frobenius theorem.  At
`rho = 1/8192`, the exact coefficient is

`3072 * 16 * (4 rho^2) = 3/1024`.

The finite perturbation identity then yields

`selectedBackgroundGaugeAdjointReducedFloor`:

`(29/1024) ||lambda||^2 <= ||L_gauge,A^* lambda||^2`

for every componentwise-mean-zero multiplier whenever the actual background
satisfies the repository's relaxed inverse-link radius.

## Redundancy correction

`flatConstantRedundancyNotAutomaticallyTransported` gives an exact rational
small-radius holonomy counterexample.  A constant Lie direction that is a flat
gauge zero mode is rotated by a non-central near-identity holonomy.  Therefore
one may not prove background rank stability by deleting the three flat
constant rows once and reusing that deletion at every background.

The remaining reduced-carrier theorem must either construct the actual moving
redundancy fibre, or prove equivalence to a fixed based/global/tree gauge.

## Exact flat regularized Green

`regularizedFlatGaugeGramIsConfiguredSiteOperator` proves that adding the
constant-mode projector to the actual flat gauge Gram gives the repository's
configured scalar operator `-Delta_periodic + P_const` componentwise.

`regularizedFlatGaugeGreenLeftInverse` and
`regularizedFlatGaugeGreenRightInverse` transport the existing explicit
256-site scalar Green kernel to a three-component two-sided gauge-multiplier
inverse.  This supplies a concrete reference operator for the fixed-gauge route
without pretending it is the background Moore–Penrose inverse.

## Continuum lower-gap route

`vacuumOrthogonalRecoveryTransfersUniformGap` lifts the corrected Mosco-upper
inequality to a proof-carrying vacuum-orthogonal family.  It needs only a
vacuum-compatible recovery vector with recovered norm and an energy upper
bound; it does not require trace-norm convergence of the entire transfer
operator.

## Immediate mathematical frontier

1. Prove the physical equivalence of a fixed based/global/tree gauge to the
   selected variational constraint, or construct the true moving redundancy
   fibre.
2. Use that fixed carrier to construct the background Green/pseudoinverse and
   its Combes–Thomas decay.
3. Derive first-variation annihilation from the actual selected minimizer.
4. Instantiate the literal fifteen source/defect atoms and four owner bounds,
   then invoke the existing `1/32` state-Hessian floor.
5. Move immediately to scale-uniform RG, tightness, a physical-unit vacuum gap,
   vacuum-stable recovery and OS Hamiltonian identification.

No Clay completion or continuum Yang–Mills construction is asserted here.
