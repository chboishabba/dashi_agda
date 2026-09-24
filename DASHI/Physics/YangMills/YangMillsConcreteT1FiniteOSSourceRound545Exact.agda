{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact where

------------------------------------------------------------------------
-- GOAL-1 A/T1 / ROUND545:
-- ONE T1 SOURCE OWNS THE REMAINING FINITE-OS SAME-FAMILY APPLICATION
--
-- R532 already reuses Euclidean covariance and Wilson RP from the concrete T1
-- source.  The only independent finite-OS applicability seam left there is
-- bosonic permutation symmetry.
--
-- R545 packages that bosonic witness with the SAME T1 source/family.  OS0/5
-- and OS4 are deliberately not folded into this source: they remain outputs
-- of the quantitative-moment and B/clustering lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as T1
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as Endpoint
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Exact as R532
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteT1FiniteOSSource
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
    (endpoint :
      Endpoint.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    : Set₂ where
  field
    t1 :
      T1.ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint

    bosonic :
      ∀ group →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation
        (Endpoint.family endpoint group)

open ConcreteT1FiniteOSSource public

record FiniteOSContinuation
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
    (endpoint :
      Endpoint.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (source :
      ConcreteT1FiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction Permutation
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    : Set₂ where
  field
    os05 :
      ∀ group →
      OS05.CanonicalCMP119OS05LimitData
        Configuration
        (Endpoint.family endpoint group)

    OS4Clustering : G → Set
    os4 : ∀ group → OS4Clustering group

open FiniteOSContinuation public

asFiniteOSCompletion :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction Permutation
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (source :
      ConcreteT1FiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction Permutation
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  FiniteOSContinuation
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection EuclideanAction Permutation
    Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
    SmallFieldScale BlockRadius AnalyticRadius Decay
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division endpoint source →
  R532.FiniteOSCompletion
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection EuclideanAction Permutation
    Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
    SmallFieldScale BlockRadius AnalyticRadius Decay
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division base endpoint (t1 source)
asFiniteOSCompletion base source continuation = record
  { R532.FiniteOSCompletion.bosonic =
      bosonic source
  ; R532.FiniteOSCompletion.os05 =
      os05 continuation
  ; R532.FiniteOSCompletion.OS4Clustering =
      OS4Clustering continuation
  ; R532.FiniteOSCompletion.os4 =
      os4 continuation
  }

round545T1FiniteOSSourceCompilerLevel : ProofLevel
round545T1FiniteOSSourceCompilerLevel = machineChecked

round545BosonicMayUseDifferentFiniteFamily : Bool
round545BosonicMayUseDifferentFiniteFamily = false

round545IndependentFiniteEuclideanApplicationRequired : Bool
round545IndependentFiniteEuclideanApplicationRequired = false

round545IndependentFiniteWilsonRPApplicationRequired : Bool
round545IndependentFiniteWilsonRPApplicationRequired = false

-- Bosonic applicability is still genuine source content, but is no longer an
-- independently selectable family/weld downstream of T1.
literalRound545BosonicSameFamilyContentLevel : ProofLevel
literalRound545BosonicSameFamilyContentLevel =
  Bosonic.literalCMP119BosonicObservableAttachmentLevel

literalRound545ConcreteT1FiniteOSSourceLevel : ProofLevel
literalRound545ConcreteT1FiniteOSSourceLevel = conditional
