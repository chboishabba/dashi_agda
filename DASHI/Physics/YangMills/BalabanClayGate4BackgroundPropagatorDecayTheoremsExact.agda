module DASHI.Physics.YangMills.BalabanClayGate4BackgroundPropagatorDecayTheoremsExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bałaban background-field propagator package, Theorems 3.1--3.4.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- The source proves, under a regularity condition with constants depending only
-- on d and L:
--
-- * local and global bounds for G'(U), its covariant derivatives, and G(U);
-- * exponential kernel decay at rate delta_0;
-- * an exponential bound for (Q'(U)G'(U)^2Q'(U)^*)^{-1};
-- * analytic extension to a small complexified perturbation U'U, preserving
--   the same estimates.
--
-- This record preserves that theorem profile. Repository-specific operator and
-- norm identification remains a separate physical bridge.
------------------------------------------------------------------------

record BackgroundPropagatorDecayTheorems
    (Configuration Site Bond Source Operator Bound : Set) : Set₁ where
  field
    multiply add : Bound → Bound → Bound
    LessEqual StrictlyLess : Bound → Bound → Set

    dimension blockSide : Bound
    M M1 alpha0 a0 epsilon1 a1 delta0 B0 : Bound

    distance : Site → Site → Bound
    exponentialDecay : Bound → Bound → Bound

    RegularConfiguration : Configuration → Set
    SmallComplexPerturbation : Configuration → Set

    scalarPropagator gaugePropagator : Configuration → Operator
    constrainedInverse : Configuration → Operator

    scalarKernel : Operator → Site → Site → Bound
    gaugeKernel : Operator → Bond → Bond → Bound
    inverseKernel : Operator → Site → Site → Bound

    localScaleWeight : Site → Site → Bound
    inverseScaleWeight : Site → Site → Bound

    largeLocalizationParameter : LessEqual M1 M
    regularitySmallness : StrictlyLess (multiply M alpha0) a0

    scalarKernelDecay : ∀ configuration left right →
      RegularConfiguration configuration →
      LessEqual
        (scalarKernel (scalarPropagator configuration) left right)
        (multiply B0
          (multiply (localScaleWeight left right)
            (exponentialDecay delta0 (distance left right))))

    gaugeKernelDecay : ∀ configuration left right →
      RegularConfiguration configuration →
      LessEqual
        (gaugeKernel (gaugePropagator configuration) left right)
        (multiply B0
          (multiply (localScaleWeight left right)
            (exponentialDecay delta0 (distance left right))))

    constrainedInverseDecay : ∀ configuration left right →
      RegularConfiguration configuration →
      LessEqual
        (inverseKernel (constrainedInverse configuration) left right)
        (multiply B0
          (multiply (inverseScaleWeight left right)
            (exponentialDecay delta0 (distance left right))))

    AnalyticExtension : Configuration → Configuration → Operator → Set

    scalarAnalyticExtension : ∀ background perturbation →
      RegularConfiguration background →
      SmallComplexPerturbation perturbation →
      AnalyticExtension background perturbation
        (scalarPropagator background)

    gaugeAnalyticExtension : ∀ background perturbation →
      RegularConfiguration background →
      SmallComplexPerturbation perturbation →
      AnalyticExtension background perturbation
        (gaugePropagator background)

    inverseAnalyticExtension : ∀ background perturbation →
      RegularConfiguration background →
      SmallComplexPerturbation perturbation →
      AnalyticExtension background perturbation
        (constrainedInverse background)

    perturbationSmallness : StrictlyLess epsilon1 a1

open BackgroundPropagatorDecayTheorems public

balabanBackgroundPropagatorTheorem31Level : ProofLevel
balabanBackgroundPropagatorTheorem31Level = standardImported

balabanBackgroundConstrainedInverseTheorem32Level : ProofLevel
balabanBackgroundConstrainedInverseTheorem32Level = standardImported

balabanBackgroundGaugePropagatorTheorem33Level : ProofLevel
balabanBackgroundGaugePropagatorTheorem33Level = standardImported

balabanBackgroundAnalyticityTheorem34Level : ProofLevel
balabanBackgroundAnalyticityTheorem34Level = standardImported

physicalBackgroundPropagatorRepositoryIdentificationInputsLevel : ProofLevel
physicalBackgroundPropagatorRepositoryIdentificationInputsLevel = conditional

physicalBackgroundPropagatorScaleWeightInputsLevel : ProofLevel
physicalBackgroundPropagatorScaleWeightInputsLevel = conditional
