{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedPublishedOSAssemblyRound526Exact where

------------------------------------------------------------------------
-- GOAL-1 A/T3 / ROUND526:
-- PUBLISHED FINITE OS SOURCES -> OS SYSTEM ON THE REPRESENTED MEASURE
--
-- R462 already constructs canonical-limit OS1/OS2/OS3 from:
--   published finite Euclidean covariance,
--   bosonic symmetry,
--   published Wilson reflection positivity.
-- Its OS0/OS5 come from the canonical quantitative limit and OS4 is the
-- selected clustering input.
--
-- R520 showed the correct represented-measure transport: use the least
-- pointwise-extensional closure of each expectation predicate.  Apply that
-- uniformly to OS0/OS1/OS2/OS3/OS5 and keep OS4 unchanged.
--
-- Hence R524's source OS system can be constructed directly on the represented
-- Schwinger function.  No source-OS/literal-Schwinger equality and no second OS
-- estimate remain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as GramOS
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsExtensionalizedRepresentedOS05Round520Exact as R520
import DASHI.Physics.YangMills.YangMillsRepresentedOSSystemRound524Exact as R524
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RepresentedPublishedOSSource
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     EuclideanAction Permutation : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    {S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    : Set₂ where
  field
    representation :
      ∀ group →
      R476.SourceLimitRepresentation
        (Configuration → ℝ)
        (Limit.limitExpectation (R462.family source group))

open RepresentedPublishedOSSource public

representedExpectation :
  ∀ {Configuration} →
  R476.RepresentedContinuum (Configuration → ℝ) →
  R520.ExpectationFunctional Configuration
representedExpectation represented =
  R520.representedExpectation represented

OS1Predicate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  R520.ExpectationFunctional Configuration → Set
OS1Predicate source group expectation =
  ∀ action observable →
  expectation
    (Euclidean.actObservable
      (R462.euclidean source group) action observable)
  ≡ expectation observable

OS3Predicate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  R520.ExpectationFunctional Configuration → Set
OS3Predicate source group expectation =
  ∀ permutation observable →
  expectation
    (Bosonic.permuteObservable
      (R462.bosonic source group) permutation observable)
  ≡ expectation observable

OS2Predicate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  R520.ExpectationFunctional Configuration → Set
OS2Predicate source group expectation =
  GramOS.GramReflectionPositive
    (OS2.asOSGramLimitData
      (Pinned.finiteOS2Inputs
        (R462.asPinnedOSAxiomInputs source) group))
    expectation

canonicalOS1 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  OS1Predicate source group
    (Limit.limitExpectation (R462.family source group))
canonicalOS1 source group =
  Pinned.os1 (R462.asPinnedOSAxiomInputs source) group

canonicalOS2 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  OS2Predicate source group
    (Limit.limitExpectation (R462.family source group))
canonicalOS2 source group =
  Pinned.continuumOS2 (R462.asPinnedOSAxiomInputs source) group

canonicalOS3 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  OS3Predicate source group
    (Limit.limitExpectation (R462.family source group))
canonicalOS3 source group =
  Pinned.os3 (R462.asPinnedOSAxiomInputs source) group

asRepresentedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    {source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (represented :
      RepresentedPublishedOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division source)
    group →
  R524.RepresentedOSAxiomInputs
    Configuration Position
    (R462.cylinderEncoding source)
    (R476.represented (representation represented group))
asRepresentedOSAxiomInputs {source = source} represented group =
  let
    canonical = R462.asPinnedOSAxiomInputs source
    rep = representation represented group
    target = R520.representedExpectation (R476.represented rep)
    pointwise = R476.sourceLimitIsIntegral rep
  in
  record
  { R524.RepresentedOSAxiomInputs.OS0Regularity =
      R520.ExtensionalClosure
        (OS05.ContinuumRegularity (R462.os05 source group))
        target
  ; R524.RepresentedOSAxiomInputs.OS1EuclideanCovariance =
      R520.ExtensionalClosure
        (OS1Predicate source group)
        target
  ; R524.RepresentedOSAxiomInputs.OS2ReflectionPositivity =
      R520.ExtensionalClosure
        (OS2Predicate source group)
        target
  ; R524.RepresentedOSAxiomInputs.OS3PermutationSymmetry =
      R520.ExtensionalClosure
        (OS3Predicate source group)
        target
  ; R524.RepresentedOSAxiomInputs.OS4Clustering =
      R462.OS4Clustering source group
  ; R524.RepresentedOSAxiomInputs.OS5GrowthControl =
      R520.ExtensionalClosure
        (OS05.ContinuumGrowthControl (R462.os05 source group))
        target
  ; R524.RepresentedOSAxiomInputs.os0 =
      Limit.limitExpectation (R462.family source group) ,
        ( Pinned.os0 canonical group , pointwise )
  ; R524.RepresentedOSAxiomInputs.os1 =
      Limit.limitExpectation (R462.family source group) ,
        ( canonicalOS1 source group , pointwise )
  ; R524.RepresentedOSAxiomInputs.os2 =
      Limit.limitExpectation (R462.family source group) ,
        ( canonicalOS2 source group , pointwise )
  ; R524.RepresentedOSAxiomInputs.os3 =
      Limit.limitExpectation (R462.family source group) ,
        ( canonicalOS3 source group , pointwise )
  ; R524.RepresentedOSAxiomInputs.os4 =
      R462.os4 source group
  ; R524.RepresentedOSAxiomInputs.os5 =
      Limit.limitExpectation (R462.family source group) ,
        ( Pinned.os5 canonical group , pointwise )
  }

representedOSSystem :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    {source :
      R462.PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (represented :
      RepresentedPublishedOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division source)
    group →
  OS.ContinuumSchwingerSystem
    (Configuration → ℝ) Position ℝ
representedOSSystem represented group =
  R524.representedOSSystem
    (asRepresentedOSAxiomInputs represented group)

round526RepresentedPublishedOSAssemblyLevel : ProofLevel
round526RepresentedPublishedOSAssemblyLevel = machineChecked

round526SourceOSLiteralSchwingerWeldRequired : Bool
round526SourceOSLiteralSchwingerWeldRequired = false

-- No new OS estimate is introduced.  Physical payments are exactly the source
-- applicability already carried by R462 plus the selected OS4 clustering input.
literalRound526AdditionalOSAnalysisLevel : ProofLevel
literalRound526AdditionalOSAnalysisLevel = machineChecked
