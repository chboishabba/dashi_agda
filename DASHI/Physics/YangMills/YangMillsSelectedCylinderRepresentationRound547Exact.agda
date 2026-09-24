{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND547:
-- DO NOT OVERSTATE REPRESENTATION BEYOND THE SELECTED CYLINDER CLASS
--
-- R534's standard projective extension theorem already proves agreement with
-- every finite cylinder event through extensionAgreesWithCylinderMass.
--
-- Requiring
--
--   limitExpectation F = integral F dmu
--
-- for every arbitrary Configuration -> Real is stronger than the extension
-- theorem supplies.  The Clay construction only needs the selected
-- cylinder/Wilson observable algebra first; extension to a larger completion
-- must come from a separate density/continuity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact as R538
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record SelectedCylinderObservableClass
    (Configuration Event : Set) : Set₁ where
  field
    SelectedObservable : Set
    asObservable : SelectedObservable → Configuration → ℝ
    cylinderIndicator : Event → SelectedObservable

open SelectedCylinderObservableClass public

record SelectedCylinderRepresentationInputs
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    : Set₂ where
  field
    projectiveEvents :
      R538.PhysicalPositiveProjectiveCylinderInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family

    eventAlgebraLaws :
      ∀ cutoff →
      R539.ProbabilityEventBooleanAlgebraLaws
        (R538.premeasure
          (R538.levelProbability
            (R538.asPositiveProjectiveCylinderProbability projectiveEvents)
            cutoff))

    continuity :
      R534.ProjectiveContinuityAtEmpty
        (R538.asPositiveProjectiveCylinderProbability projectiveEvents)

    extensionAuthority :
      R534.ProjectiveMeasureExtensionAuthority
        Nat Event (Configuration → ℝ) ℝ

    extensionIndicatorIsLiteralIndicator :
      ∀ cutoff event →
      R534.indicatorAt extensionAuthority cutoff event
      ≡
      R498.indicator
        (R538.events (R538.positiveEvents projectiveEvents))
        event

    selectedClass :
      SelectedCylinderObservableClass Configuration Event

    selectedCylinderIsLiteralIndicator :
      ∀ event →
      asObservable selectedClass (cylinderIndicator selectedClass event)
      ≡
      R498.indicator
        (R538.events (R538.positiveEvents projectiveEvents))
        event

open SelectedCylinderRepresentationInputs public

representedMeasure :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family) →
  R534.SigmaMeasure
    (extensionAuthority inputs)
representedMeasure inputs =
  R534.extendProjective
    (extensionAuthority inputs)
    (R538.asPositiveProjectiveCylinderProbability
      (projectiveEvents inputs))
    (eventAlgebraLaws inputs)
    (continuity inputs)

cylinderGeneratorIntegralIsProjectiveMass :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    cutoff event →
  R534.integrate
    (extensionAuthority inputs)
    (representedMeasure inputs)
    (asObservable
      (selectedClass inputs)
      (cylinderIndicator (selectedClass inputs) event))
  ≡
  R534.massAsScalar
    (extensionAuthority inputs)
    (R495.mass
      (R538.premeasure
        (R538.levelProbability
          (R538.asPositiveProjectiveCylinderProbability
            (projectiveEvents inputs))
          cutoff))
      event)
cylinderGeneratorIntegralIsProjectiveMass inputs cutoff event
  rewrite selectedCylinderIsLiteralIndicator inputs event
        | extensionIndicatorIsLiteralIndicator inputs cutoff event =
  R534.extensionAgreesWithCylinderMass
    (extensionAuthority inputs)
    (R538.asPositiveProjectiveCylinderProbability
      (projectiveEvents inputs))
    (eventAlgebraLaws inputs)
    (continuity inputs)
    cutoff event

round547CylinderGeneratorRepresentationCompilerLevel : ProofLevel
round547CylinderGeneratorRepresentationCompilerLevel = machineChecked

arbitraryBoundedObservableRepresentationAssumed : Bool
arbitraryBoundedObservableRepresentationAssumed = false

selectedCylinderClassRepresentationPreferred : Bool
selectedCylinderClassRepresentationPreferred = true

literalRound547SelectedObservableClosureRepresentationLevel : ProofLevel
literalRound547SelectedObservableClosureRepresentationLevel = conditional
