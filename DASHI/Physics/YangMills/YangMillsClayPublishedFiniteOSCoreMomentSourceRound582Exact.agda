{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSCoreMomentSourceRound582Exact where

------------------------------------------------------------------------
-- GOAL-1 H2 / ROUND582:
-- THE PREFERRED FINITE -> PRE-GAP OS CORE SOURCE.
--
-- This is R581 with OS4 removed.  It constructs the exact pinned CMP119 core
-- consumed by H2 reconstruction:
--
--   finite Euclidean + bosonic + Wilson RP
--   + literal exponential moments
--   + standard OS0/OS5 closure
--   ------------------------------------------------
--   pinned OS0/1/2/3/5 core
--
-- Clustering is intentionally absent and is attached later from H1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureContinuumOS2Exact as FiniteOS2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as R461
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as R559
import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as R560
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PublishedFiniteOSCoreMomentSource
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState EuclideanAction Permutation : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          CompactSimpleGroup Spacetime Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState))
    : Set₂ where
  field
    family : ∀ group →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    euclidean :
      ∀ group →
      Euclidean.CMP119WholeLatticeEuclideanCovariance
        Configuration EuclideanAction (family group)

    bosonic :
      ∀ group →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation (family group)

    wilsonRP :
      ∀ group →
      R461.PublishedWilsonRPApplication
        Configuration (family group) observableAlgebra

    moments :
      ∀ group →
      R559.LiteralCMP119PreOSQuantitativeMomentSource
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division
        (family group) observableAlgebra

    os05Closure :
      ∀ group →
      R560.LiteralCMP119OS05ClosureAuthority
        Configuration
        (family group)
        (R560.PreOSFiniteMomentRegularity (moments group))
        (R560.PreOSFiniteExponentialGrowth (moments group))

open PublishedFiniteOSCoreMomentSource public

euclideanCoreLimitInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      PublishedFiniteOSCoreMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family source group))
    EuclideanAction
euclideanCoreLimitInputs source group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      Euclidean.actObservable (euclidean source group)
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      Euclidean.finiteEuclideanInvariant (euclidean source group)
  }

bosonicCoreLimitInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      PublishedFiniteOSCoreMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family source group))
    Permutation
bosonicCoreLimitInputs source group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      Bosonic.permuteObservable (bosonic source group)
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      Bosonic.finitePermutationInvariant (bosonic source group)
  }

asPinnedOSCoreInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  PublishedFiniteOSCoreMomentSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  Pinned.PinnedCMP119OSCoreInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedOSCoreInputs source = record
  { Pinned.PinnedCMP119OSCoreInputs.familyCore =
      family source
  ; Pinned.PinnedCMP119OSCoreInputs.cylinderEncodingCore =
      cylinderEncoding source
  ; Pinned.PinnedCMP119OSCoreInputs.observableAlgebraCore =
      observableAlgebra source
  ; Pinned.PinnedCMP119OSCoreInputs.finiteReflectionPositiveCore =
      λ group →
        R461.finiteReflectionPositiveFromPublishedWilson
          (wilsonRP source group)
  ; Pinned.PinnedCMP119OSCoreInputs.OS0RegularityCore =
      λ group →
        OS05.ContinuumRegularity
          (R560.asCanonicalPreOS05
            (moments source group)
            (os05Closure source group))
          (Limit.limitExpectation (family source group))
  ; Pinned.PinnedCMP119OSCoreInputs.OS1EuclideanCovarianceCore =
      λ group → ∀ action observable →
        Limit.limitExpectation (family source group)
          (Euclidean.actObservable
            (euclidean source group) action observable)
        Agda.Builtin.Equality.≡
        Limit.limitExpectation (family source group) observable
  ; Pinned.PinnedCMP119OSCoreInputs.OS3PermutationSymmetryCore =
      λ group → ∀ permutation observable →
        Limit.limitExpectation (family source group)
          (Bosonic.permuteObservable
            (bosonic source group) permutation observable)
        Agda.Builtin.Equality.≡
        Limit.limitExpectation (family source group) observable
  ; Pinned.PinnedCMP119OSCoreInputs.OS5GrowthControlCore =
      λ group →
        OS05.ContinuumGrowthControl
          (R560.asCanonicalPreOS05
            (moments source group)
            (os05Closure source group))
          (Limit.limitExpectation (family source group))
  ; Pinned.PinnedCMP119OSCoreInputs.os0Core =
      λ group →
        OS05.canonicalCMP119OS0
          (R560.asCanonicalPreOS05
            (moments source group)
            (os05Closure source group))
  ; Pinned.PinnedCMP119OSCoreInputs.os1Core =
      λ group →
        ActionLimit.continuumActionInvariant
          (euclideanCoreLimitInputs source group)
  ; Pinned.PinnedCMP119OSCoreInputs.os3Core =
      λ group →
        ActionLimit.continuumActionInvariant
          (bosonicCoreLimitInputs source group)
  ; Pinned.PinnedCMP119OSCoreInputs.os5Core =
      λ group →
        OS05.canonicalCMP119OS5
          (R560.asCanonicalPreOS05
            (moments source group)
            (os05Closure source group))
  }

round582PreGapOSCoreCompilerLevel : ProofLevel
round582PreGapOSCoreCompilerLevel = machineChecked

round582OS4RequiredByH2Core : Bool
round582OS4RequiredByH2Core = false

literalRound582PublishedFiniteOSCoreMomentSourceLevel : ProofLevel
literalRound582PublishedFiniteOSCoreMomentSourceLevel = conditional
