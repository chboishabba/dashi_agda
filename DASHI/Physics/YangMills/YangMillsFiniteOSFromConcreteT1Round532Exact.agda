{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Exact where

------------------------------------------------------------------------
-- GOAL-1 A/T1 / ROUND532:
-- BUILD THE PUBLISHED FINITE-OS SOURCE ON THE SAME CONCRETE T1 FAMILY
--
-- R516 already owns:
--   * the selected literal finite CMP119 family;
--   * its cylinder algebra;
--   * whole-lattice Euclidean covariance;
--   * published Wilson reflection positivity.
--
-- R462 must not independently choose those objects again.  Complete only the
-- pieces not contained in T1 (bosonic permutation symmetry, OS0/5 canonical
-- limit data, and the selected OS4 clustering input), then compile R462.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as T1
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as Endpoint
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record FiniteOSCompletion
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Algebra Event Projection EuclideanAction Permutation
     Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
     SmallFieldScale BlockRadius AnalyticRadius Decay : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (endpoint :
      Endpoint.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (t1 :
      T1.ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    : Set₂ where
  field
    bosonic :
      ∀ group →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation
        (Endpoint.family endpoint group)

    os05 :
      ∀ group →
      OS05.CanonicalCMP119OS05LimitData
        Configuration
        (Endpoint.family endpoint group)

    OS4Clustering : G → Set
    os4 : ∀ group → OS4Clustering group

open FiniteOSCompletion public

compilePublishedFiniteOSSource :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction Permutation
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division base endpoint t1} →
  FiniteOSCompletion
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection EuclideanAction Permutation
    Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
    SmallFieldScale BlockRadius AnalyticRadius Decay
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division base endpoint t1 →
  R462.PublishedFiniteOSSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division
    (Endpoint.concreteEndpointSemantics base endpoint)
compilePublishedFiniteOSSource
    {endpoint = endpoint} {t1 = t1} completion = record
  { R462.PublishedFiniteOSSource.family =
      Endpoint.family endpoint
  ; R462.PublishedFiniteOSSource.cylinderEncoding =
      Endpoint.cylinderEncoding endpoint
  ; R462.PublishedFiniteOSSource.observableAlgebra =
      T1.observableAlgebra t1
  ; R462.PublishedFiniteOSSource.euclidean =
      T1.euclidean t1
  ; R462.PublishedFiniteOSSource.bosonic =
      bosonic completion
  ; R462.PublishedFiniteOSSource.wilsonRP =
      T1.publishedWilsonRP t1
  ; R462.PublishedFiniteOSSource.os05 =
      os05 completion
  ; R462.PublishedFiniteOSSource.OS4Clustering =
      OS4Clustering completion
  ; R462.PublishedFiniteOSSource.os4 =
      os4 completion
  }

round532FiniteOSFromT1CompilerLevel : ProofLevel
round532FiniteOSFromT1CompilerLevel = machineChecked

-- Euclidean and Wilson-RP applicability are no longer independently selected
-- once the concrete T1 source has been chosen.
round532IndependentEuclideanApplicationRequired : Agda.Builtin.Bool.Bool
round532IndependentEuclideanApplicationRequired = Agda.Builtin.Bool.false

round532IndependentWilsonRPApplicationRequired : Agda.Builtin.Bool.Bool
round532IndependentWilsonRPApplicationRequired = Agda.Builtin.Bool.false

-- The only finite-OS source applicability not already owned by T1 is bosonic
-- permutation applicability.  OS0/5 and OS4 are supplied by their existing
-- quantitative/B source lanes.
literalRound532BosonicSameFamilyAttachmentLevel : ProofLevel
literalRound532BosonicSameFamilyAttachmentLevel =
  Bosonic.literalCMP119BosonicObservableAttachmentLevel
