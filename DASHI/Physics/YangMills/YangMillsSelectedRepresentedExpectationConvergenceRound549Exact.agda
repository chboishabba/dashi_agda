{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND549:
-- SELECTED-CLASS FINITE EXPECTATIONS CONVERGE TO THE REPRESENTED INTEGRAL
--
-- This replaces the old R509 path through R499.
--
-- Preferred inputs:
--
--   R547 projective represented measure on the literal cylinder generators
--   + ONE closure theorem on the selected cylinder/Wilson observable class:
--
--       limitExpectation(F) = integral F dmu
--
--     for F in the selected class only
--   + the already-owned finite selected expectation convergence.
--
-- No theorem for arbitrary Configuration -> Real observables is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record SelectedObservableRepresentationClosure
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
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    : Set₂ where
  field
    selectedLimitIsRepresentedIntegral :
      ∀ selected →
      Limit.limitExpectation family
        (R547.asObservable
          (R547.selectedClass representation)
          selected)
      ≡
      R534.integrate
        (R547.extensionAuthority representation)
        (R547.representedMeasure representation)
        (R547.asObservable
          (R547.selectedClass representation)
          selected)

open SelectedObservableRepresentationClosure public

selectedRepresentedContinuum :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family) →
  R476.RepresentedContinuum (Configuration → ℝ)
selectedRepresentedContinuum representation = record
  { R476.RepresentedContinuum.MeasureObject =
      R534.SigmaMeasure (R547.extensionAuthority representation)
  ; R476.RepresentedContinuum.IsCountablyAdditive =
      R534.IsCountablyAdditive (R547.extensionAuthority representation)
  ; R476.RepresentedContinuum.measure =
      R547.representedMeasure representation
  ; R476.RepresentedContinuum.integrate =
      R534.integrate (R547.extensionAuthority representation)
  ; R476.RepresentedContinuum.countablyAdditive =
      R534.extensionCountablyAdditive
        (R547.extensionAuthority representation)
        (R538.asPositiveProjectiveCylinderProbability
          (R547.projectiveEvents representation))
        (R547.eventAlgebraLaws representation)
        (R547.continuity representation)
  }

selectedRepresentedExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (closure :
      SelectedObservableRepresentationClosure
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation)
    selected →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff
        (R547.asObservable
          (R547.selectedClass representation)
          selected))
    (R534.integrate
      (R547.extensionAuthority representation)
      (R547.representedMeasure representation)
      (R547.asObservable
        (R547.selectedClass representation)
        selected))
selectedRepresentedExpectationConverges
    {family = family} {limitLaws = limitLaws}
    representation closure selected =
  subst
    (λ target →
      Cylinder.Converges
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        (λ cutoff →
          Limit.finiteExpectation family cutoff
            (R547.asObservable
              (R547.selectedClass representation)
              selected))
        target)
    (selectedLimitIsRepresentedIntegral closure selected)
    (Cylinder.selectedConverges
      (Limit.asCylinderLimitData family)
      (R547.asObservable
        (R547.selectedClass representation)
        selected))

selectedRepresentedPhysicalExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (closure :
      SelectedObservableRepresentationClosure
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation)
    selected →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff
        (R547.asObservable
          (R547.selectedClass representation)
          selected))
    (Physical.expectation
      (R476.asPhysicalContinuum
        (selectedRepresentedContinuum representation))
      (R547.asObservable
        (R547.selectedClass representation)
        selected))
selectedRepresentedPhysicalExpectationConverges
    representation closure selected =
  selectedRepresentedExpectationConverges
    representation closure selected

round549SelectedRepresentedConvergenceCompilerLevel : ProofLevel
round549SelectedRepresentedConvergenceCompilerLevel = machineChecked

round549ArbitraryObservableRepresentationRequired : Bool
round549ArbitraryObservableRepresentationRequired = false

round549R499DependencyRequired : Bool
round549R499DependencyRequired = false

-- The only remaining A3 representation payment here is the selected-class
-- closure theorem itself.
literalRound549SelectedObservableClosureRepresentationLevel : ProofLevel
literalRound549SelectedObservableClosureRepresentationLevel = conditional
