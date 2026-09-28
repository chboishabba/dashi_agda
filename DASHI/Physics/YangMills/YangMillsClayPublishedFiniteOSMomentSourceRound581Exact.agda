{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMomentSourceRound581Exact where

------------------------------------------------------------------------
-- GOAL-1 H2 / ROUND581:
-- PUBLISHED FINITE OS + LITERAL MOMENTS -> R462, WITHOUT PRIMITIVE OS0/OS5.
--
-- R462 is the preferred finite-OS source, but historically accepted a complete
-- CanonicalCMP119OS05LimitData as one input.  R559/R560 now expose a pre-OS
-- literal exponential-moment source on the exact finite CMP119 family and
-- compile finite regularity/growth plus standard canonical-limit closure into
-- that OS0/OS5 datum.
--
-- Therefore the preferred H2 finite source is:
--
--   published finite Euclidean covariance
--   + bosonic permutation symmetry
--   + published Wilson reflection positivity
--   + literal exponential moments on this SAME family
--   + standard OS0/OS5 closure
--   + selected OS4 clustering
--
-- and R462 is compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as R461
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as R559
import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as R560
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PublishedFiniteOSMomentSource
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

    OS4Clustering : CompactSimpleGroup → Set
    os4 : ∀ group → OS4Clustering group

open PublishedFiniteOSMomentSource public

asPublishedFiniteOSSource :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  PublishedFiniteOSMomentSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  R462.PublishedFiniteOSSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPublishedFiniteOSSource source = record
  { R462.PublishedFiniteOSSource.family =
      family source
  ; R462.PublishedFiniteOSSource.cylinderEncoding =
      cylinderEncoding source
  ; R462.PublishedFiniteOSSource.observableAlgebra =
      observableAlgebra source
  ; R462.PublishedFiniteOSSource.euclidean =
      euclidean source
  ; R462.PublishedFiniteOSSource.bosonic =
      bosonic source
  ; R462.PublishedFiniteOSSource.wilsonRP =
      wilsonRP source
  ; R462.PublishedFiniteOSSource.os05 =
      λ group →
        R560.asCanonicalPreOS05
          (moments source group)
          (os05Closure source group)
  ; R462.PublishedFiniteOSSource.OS4Clustering =
      OS4Clustering source
  ; R462.PublishedFiniteOSSource.os4 =
      os4 source
  }

round581FiniteOSMomentCompilerLevel : ProofLevel
round581FiniteOSMomentCompilerLevel = machineChecked

round581OS05IndependentSourceRequired : Agda.Builtin.Bool.Bool
round581OS05IndependentSourceRequired = Agda.Builtin.Bool.false

-- Physical leaves remaining in the preferred finite-OS source:
-- * published finite Euclidean/bosonic/Wilson-RP applicability;
-- * literal exponential moments on the exact family;
-- * standard canonical OS0/OS5 closure;
-- * selected OS4 clustering.
literalRound581PublishedFiniteOSMomentSourceLevel : ProofLevel
literalRound581PublishedFiniteOSMomentSourceLevel = conditional
