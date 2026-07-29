module DASHI.Physics.YangMills.BalabanClayT5LpPhysicalMeasureAdapterExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanClayT5LpUniformIntegrabilityExact as Lp
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS

------------------------------------------------------------------------
-- Exact replacement of the legacy reflected-product UI field by the L^p route.
--
-- Tapas Kumar Chandra,
-- "de La Vallee Poussin's theorem, uniform integrability, tightness and moments",
-- Statistics & Probability Letters 107 (2015), 136--141.
-- DOI: 10.1016/j.spl.2015.08.011.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Unlike a receipt-only bridge, the record expression below fills
-- `uniformIntegrabilityOfReflectedProducts` from
-- `reflectedProductUniformlyIntegrableFromLp` and then reuses the existing
-- thermodynamic, weak-convergence and OS-Gram machinery for every other field.
------------------------------------------------------------------------

lpPhysicalMeasureConvergenceData :
  ∀ {Measure Observable Scalar}
    {producer : Thermo.PhysicalExpectationProducerData Measure Observable Scalar} →
  Lp.LpExpectationProducerUpgrade producer →
  Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
lpPhysicalMeasureConvergenceData {producer = producer} upgrade = record
  { operations = Thermo.operations (Thermo.thermodynamic producer)
  ; scalarConvergence = Thermo.scalarConvergence (Thermo.thermodynamic producer)
  ; measureSequence = Thermo.diagonalMeasure producer
  ; continuumMeasure = Thermo.continuumMeasure (Thermo.thermodynamic producer)
  ; LocalGaugeInvariant =
      Thermo.LocalGaugeInvariant (Thermo.thermodynamic producer)
  ; RenormalizedObservable =
      Thermo.RenormalizedObservable (Thermo.thermodynamic producer)
  ; BoundedObservable =
      Thermo.BoundedObservable (Thermo.thermodynamic producer)
  ; UniformlyIntegrable = Thermo.UniformlyIntegrable producer
  ; finiteVolumeReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal →
        Thermo.diagonalReflectedPairExpectationConverges
          (Thermo.thermodynamic producer) left right leftLocal rightLocal
  ; thermodynamicReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal →
        Thermo.diagonalReflectedPairExpectationConverges
          (Thermo.thermodynamic producer) left right leftLocal rightLocal
  ; continuumReflectedPairExpectationConverges =
      λ left right leftRenormalized rightRenormalized →
        Thermo.renormalizedDiagonalReflectedPairExpectationConverges
          (Thermo.thermodynamic producer) left right
          leftRenormalized rightRenormalized
  ; wilsonCylinderObservableUniformlyBounded =
      Thermo.boundedObservableHasWitness producer
  ; boundedWeakConvergenceImpliesExpectationConvergence =
      Thermo.boundedWeakConvergenceFromTail producer
  ; uniformRenormalizedInsertionMomentBound =
      λ observable admissible →
        ∀ degree cutoff →
        Thermo.LessEqual (Thermo.moments producer)
          (Gram.expectation (Thermo.operations (Thermo.thermodynamic producer))
            (Thermo.diagonalMeasure producer cutoff)
            (Thermo.powerObservable (Thermo.moments producer) degree
              (Thermo.absoluteObservable (Thermo.moments producer) observable)))
          (Thermo.multiply (Thermo.moments producer)
            (Thermo.factorial (Thermo.moments producer) degree)
            (Thermo.divide (Thermo.moments producer)
              (Thermo.exponentialMomentBound (Thermo.moments producer) observable)
              (Thermo.lambda (Thermo.moments producer))))
  ; uniformIntegrabilityOfReflectedProducts =
      λ left right leftRenormalized rightRenormalized →
        Lp.uiPredicatesAgree upgrade
          (λ cutoff →
            Gram.multiplyObservable
              (Thermo.operations (Thermo.thermodynamic producer))
              (Gram.reflectObservable
                (Thermo.operations (Thermo.thermodynamic producer)) left)
              right)
          (Lp.reflectedProductUniformlyIntegrableFromLp
            (Lp.lpRoute upgrade) left right
            leftRenormalized rightRenormalized)
  ; weakConvergencePlusUniformIntegrability =
      Thermo.weakConvergencePlusUniformIntegrability producer
  }

record LpPhysicalMeasureToOSGramData
    {Measure Observable Scalar : Set}
    {producer : Thermo.PhysicalExpectationProducerData Measure Observable Scalar}
    (upgrade : Lp.LpExpectationProducerUpgrade producer) : Set₁ where
  field
    TestFamily : Set
    decodeFamily : TestFamily → Gram.PhysicalOSFiniteTestFamily Observable Scalar
    admissibleFamily : ∀ family →
      Gram.AdmissiblePhysicalTestFamily
        (lpPhysicalMeasureConvergenceData upgrade)
        (decodeFamily family)

    Nonnegative : Scalar → Set
    finiteGramNonnegative : ∀ cutoff family →
      Nonnegative
        (Gram.physicalReflectedGramQuadraticForm
          (Gram.operations (lpPhysicalMeasureConvergenceData upgrade))
          (Gram.measureSequence (lpPhysicalMeasureConvergenceData upgrade) cutoff)
          (decodeFamily family))

    nonnegativeConeClosed : ∀ sequence target →
      Gram.Converges
        (Gram.scalarConvergence (lpPhysicalMeasureConvergenceData upgrade))
        sequence target →
      (∀ cutoff → Nonnegative (sequence cutoff)) →
      Nonnegative target

open LpPhysicalMeasureToOSGramData public

lpPhysicalMeasureToGramData :
  ∀ {Measure Observable Scalar producer upgrade} →
  LpPhysicalMeasureToOSGramData
    {Measure} {Observable} {Scalar} {producer} upgrade →
  Gram.PhysicalMeasureToOSGramData Measure Observable Scalar
lpPhysicalMeasureToGramData {upgrade = upgrade} dataSet = record
  { convergenceData = lpPhysicalMeasureConvergenceData upgrade
  ; TestFamily = TestFamily dataSet
  ; decodeFamily = decodeFamily dataSet
  ; admissibleFamily = admissibleFamily dataSet
  ; Nonnegative = Nonnegative dataSet
  ; finiteGramNonnegative = finiteGramNonnegative dataSet
  ; nonnegativeConeClosed = nonnegativeConeClosed dataSet
  }

lpPhysicalMeasureFeedsOSGram :
  ∀ {Measure Observable Scalar producer upgrade}
    (dataSet : LpPhysicalMeasureToOSGramData
      {Measure} {Observable} {Scalar} {producer} upgrade) →
  OS.OSGramLimitData Measure (TestFamily dataSet) Scalar
lpPhysicalMeasureFeedsOSGram dataSet =
  Gram.physicalMeasureTopologyControlsOSGram
    (lpPhysicalMeasureToGramData dataSet)

lpPhysicalContinuumReflectionPositive :
  ∀ {Measure Observable Scalar producer upgrade}
    (dataSet : LpPhysicalMeasureToOSGramData
      {Measure} {Observable} {Scalar} {producer} upgrade) →
  OS.GramReflectionPositive
    (lpPhysicalMeasureFeedsOSGram dataSet)
    (Gram.continuumMeasure
      (lpPhysicalMeasureConvergenceData upgrade))
lpPhysicalContinuumReflectionPositive dataSet =
  Gram.physicalContinuumReflectionPositive
    (lpPhysicalMeasureToGramData dataSet)

lpPhysicalMeasureRecordAssemblyLevel : ProofLevel
lpPhysicalMeasureRecordAssemblyLevel = machineChecked

lpPhysicalOSGramAdapterLevel : ProofLevel
lpPhysicalOSGramAdapterLevel = machineChecked

lpPhysicalMomentAndTopologyInputsLevel : ProofLevel
lpPhysicalMomentAndTopologyInputsLevel = conditional
