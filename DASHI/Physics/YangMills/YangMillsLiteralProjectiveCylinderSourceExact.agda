{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralProjectiveCylinderSourceExact where

------------------------------------------------------------------------
-- A3 theorem-bearing source constructor.
--
-- This module adds no new semantic predicate.  It terminates directly in the
-- preferred R535 whole-projective representation input.  The arguments are
-- exactly the five physical payments left by the A3 cut:
--
--   * positive literal cylinder events;
--   * projective expectation consistency;
--   * literal Boolean event algebra;
--   * projective continuity at empty;
--   * extension/source-integral compatibility.
--
-- R568/R565 own Wilson finite factorization; no Lp/Prokhorov detour appears.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact as R538
import DASHI.Physics.YangMills.YangMillsCylinderEventBooleanAlgebraRound539Exact as R539
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

literalPositiveProjectiveCylinderInputs :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division}
    {family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division} →
  (positiveEvents :
    R538.PositiveCylinderEventSemantics Configuration Event) →
  (Restricts : Nat → Nat → Set) →
  (restrictEvent :
    ∀ lower upper → Restricts lower upper → Event → Event) →
  (projectiveEventExpectationConsistency :
    ∀ lower upper
      (restriction : Restricts lower upper)
      event →
    Limit.finiteExpectation family lower
      (R498.indicator (R538.events positiveEvents)
        (restrictEvent lower upper restriction event))
    ≡
    Limit.finiteExpectation family upper
      (R498.indicator (R538.events positiveEvents) event)) →
  R538.PhysicalPositiveProjectiveCylinderInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family
literalPositiveProjectiveCylinderInputs
    positiveEvents Restricts restrictEvent consistency = record
  { R538.PhysicalPositiveProjectiveCylinderInputs.positiveEvents =
      positiveEvents
  ; R538.PhysicalPositiveProjectiveCylinderInputs.Restricts =
      Restricts
  ; R538.PhysicalPositiveProjectiveCylinderInputs.restrictEvent =
      restrictEvent
  ; R538.PhysicalPositiveProjectiveCylinderInputs.projectiveEventExpectationConsistency =
      consistency
  }

literalPhysicalProjectiveCylinderSource :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division}
    {family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division}
    (projectiveEvents :
      R538.PhysicalPositiveProjectiveCylinderInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (eventAlgebraLaws :
      ∀ cutoff →
      R539.ProbabilityEventBooleanAlgebraLaws
        (R538.premeasure
          (R538.levelProbability
            (R538.asPositiveProjectiveCylinderProbability projectiveEvents)
            cutoff)))
    (continuity :
      R534.ProjectiveContinuityAtEmpty
        (R538.asPositiveProjectiveCylinderProbability projectiveEvents))
    (extensionAuthority :
      R534.ProjectiveMeasureExtensionAuthority
        Nat Event (Configuration → ℝ) ℝ)
    (extensionIndicatorIsLiteralIndicator :
      ∀ cutoff event →
      R534.indicatorAt extensionAuthority cutoff event
      ≡
      R498.indicator
        (R538.events (R538.positiveEvents projectiveEvents))
        event)
    (sourceExpectationIsExtendedIntegral :
      ∀ observable →
      Limit.limitExpectation family observable
      ≡
      R534.integrate extensionAuthority
        (R534.extendProjective extensionAuthority
          (R538.asPositiveProjectiveCylinderProbability projectiveEvents)
          eventAlgebraLaws
          continuity)
        observable) →
  R535.PhysicalProjectiveCylinderRepresentationInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family
literalPhysicalProjectiveCylinderSource
    projectiveEvents eventAlgebraLaws continuity extensionAuthority
    extensionIndicatorIsLiteralIndicator
    sourceExpectationIsExtendedIntegral = record
  { R535.PhysicalProjectiveCylinderRepresentationInputs.projectiveEvents =
      projectiveEvents
  ; R535.PhysicalProjectiveCylinderRepresentationInputs.eventAlgebraLaws =
      eventAlgebraLaws
  ; R535.PhysicalProjectiveCylinderRepresentationInputs.continuity =
      continuity
  ; R535.PhysicalProjectiveCylinderRepresentationInputs.extensionAuthority =
      extensionAuthority
  ; R535.PhysicalProjectiveCylinderRepresentationInputs.extensionIndicatorIsLiteralIndicator =
      extensionIndicatorIsLiteralIndicator
  ; R535.PhysicalProjectiveCylinderRepresentationInputs.sourceExpectationIsExtendedIntegral =
      sourceExpectationIsExtendedIntegral
  }
