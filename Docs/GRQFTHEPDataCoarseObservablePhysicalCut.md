# GRQFT / HEPData / hyperfabric observable recovery: constructive cut

**Implementation:** `DASHI.Physics.Foundations.CoarseObservableFactorisationBidiExact` and `CMSCoarseObservableContactBidiExact`.

This contribution reuses existing typed material; it does **not** certify continuum quantum gravity, the Standard Model, the Clay problems, or dark energy. No external source is asserted to prove physical recovery.

## Exact new mathematical result

Given a split coarse projection `P : Fine -> Coarse` and a section `s : Coarse -> Fine` with `P(s(c)) = c`, a consumer `O : Fine -> Observation` factors through `P` if it is constant on its fibres:

    P(x) = P(y) => O(x) = O(y).

The constructed coarse consumer is `O_coarse(c) = O(s(c))`. Conversely, any factorisation `O = O_coarse ∘ P` proves constancy on fibres. A section is explicitly required; no global quotient-choice theorem is silently assumed.

The reverse (failure) route reuses `CoarseFineFabricCalculusExact.consumerCannotFactorThroughProjection`: if `P(x)=P(y)` but `O(x)≠O(y)`, no coarse-only consumer can reconstruct `O`. A two-point signed example demonstrates that a sign-sensitive consumer fails while an address-only consumer succeeds on the *same* coarse projection. These are finite information-geometry facts, not physical NS or quantum gravity claims.

## Existing donors, unchanged

- `Core.ConsumerRelativeCoarseGrainingBidiExact`: consumer-indexed sufficiency and residual reopening.
- `Core.CoarseDynamicsTraceCongruenceExact`: step commutation implies trace compatibility under admitted-transition hypotheses.
- `Physics.Closure.NSTriadKNStage3Ternary369Ledger`: balanced/unbalanced 3/6/9 round trips; not continuum NS.
- `Physics.Closure.NSCriticalConeResidualFibre369CrossPollinationExact`: finite signed residual hidden by shell coarse observation.
- `Physics.Closure.NSTriadKNComCoarseFineNaturalityRound36Exact`: exact kernel transport commutator `P(Tf)-u_x P(f) = Σ_y K_y (u_y-u_x) f_y`; not GR dynamics.
- `Physics.YangMills.BalabanReflectionPositiveCoarseGrainingTransportExact`: reflection positivity transfers through a compatible pullback, conditional on the literal physical block map being compatible.
- `Physics.Foundations.GRQFTRecoveryBidiAttemptExact`: recovered versus selected GR/QFT comparison *after* coarse-graining.
- `Physics.Foundations.CommonEffectiveActionVariationExact`: common source variation and coarse commutation are explicit application-supplied physical hypotheses.
- `Geometry.NonconstantWarpedLorentzianModel` and `Physics.Closure.DiscreteWarpedEinsteinMatterModel`: exact finite warped/vacuum-like model, not continuum source-derived FLRW.
- `Physics.QFT.StressEnergyBridgeReceiptSurface`: Wald/renormalised expectation authority sockets, not constructed selected continuum tensor.
- `Physics.Chemistry.AtomicPeriodicTable369GenerativeExact`, `Physics.StandardModel.FiniteInternalAlgebraPruning`, `Physics.Foundations.FiniteHistoryFunctionalExact`: donors for separate charge-conjugate atomic observables; no anti-gravitational-coupling theorem follows.
- `Physics.Units.SIMetrologyBridge`: distinguish dimensionful physical calibration from dimensionless finite carrier arithmetic.

## Bounded CMS measurement, not a QG prediction

The CMS Collaboration's *Measurement of the mass dependence of the transverse momentum of lepton pairs in Drell–Yan production in proton–proton collisions at √s = 13 TeV*, Eur. Phys. J. C 83 (2023) 628, DOI **10.1140/epjc/s10052-023-11631-7**, analysis **CMS-SMP-20-003**, HEPData record **ins2079374**, t43 distribution and t44 covariance, is the source of the *external experimental measurements*. It is **not** the source of DASHI's theoretical predictions.

The repo-original `HEPDataW3ComparisonLawReceipt` freezes a computed external comparison with `χ²/DOF = 2.1565191176`, `χ² = 38.8173441173`, 18 effective degrees of freedom and mean prediction/data `0.9941233097`. The source-bound `HEPDataCMSBelowZDrellYanClaimExact` records the frozen commit `3205d746639568762c9e97adf4a3672c356bd491`, artifact SHA-256 and projection digest. The numerical calculation was performed outside Agda; Agda checks the typed frozen receipt, not floating-point covariance arithmetic. The bounded W3 pass is not an independent statistical validation of full quantum gravity, proof of zero fitted parameters, or recovery of the full canonical spine. The *early* broader wording remains an explicit **uninhabited authority target**, with flags false.

The generic HEPData residual bridge and external accepted-authority gate remain separate from the bounded W3 receipt. The 369 signed example is only a structural no-collapse donor; no identification with a CMS bin or actual physical residual is made here.

## Highest-value *physical* payments still missing

1. Select the same literal microscopic hyperfabric states, their coarse projection, physical temporal evolution and observable at each cutoff.
2. Either prove observable fibre invariance (and supply a section on the selected coarse carrier) or produce a **physical** non-factorisation pair; do not infer sufficiency from lossy representation equality.
3. Establish the selected CMP119 finite-measure metric derivative and a conserved, renormalised continuum `T_{μν}` with controlled regulator/scale dependence.
4. Identify this tensor with the same selected gravitational source and prove curvature/backreaction consistency. The full non-flat Levi-Civita, finite-to-continuum Ricci convergence and Hadamard-state obligations are not discharged by generic interfaces.
5. On the sourced FLRW geometry solve coupled evolution and compute `H(a)`, `w(a)`, `ä/a`, distances and growth, including anisotropic corrections where relevant.
6. Construct conjugate SM representations and anti-atom composites with the same physical couplings; compare antihydrogen/other anti-elements without presupposing `G -> -G`. Keep local tidal-field modification, apparent weight and cosmological acceleration separate.
7. Freeze theory, calibration, covariance, measurement revision and nuisance inventory *before* independent HEPData/BAO/antimatter/local-gravity predictions. Use SI dimensions and exact external attribution. Report failures and nonidentifiability, not fabricated promotion.

### Provenance boundary

Source identity is distinct from the truth of a claim. DASHI's mathematical constructions and the external CMS measurement have different authorship. A recorded numeric value and a verified Agda equality are not a proof that the calculation generating the value was formally checked. This integration provides new exact finite consumer-recovery and obstruction theorems; it does not pay the listed physical existence obligations.
