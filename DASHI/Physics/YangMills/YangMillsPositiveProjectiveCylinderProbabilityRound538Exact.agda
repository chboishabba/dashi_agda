{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND538:
-- THE CYLINDER "PREMEASURE" MUST ACTUALLY BE A POSITIVE PROBABILITY
--
-- R498 proves finite additivity and normalization of event expectations.
-- Add the missing probability property:
--
--   event indicator >= 0 pointwise
--       -> finite normalized expectation >= 0
--       -> cylinder event mass >= 0.
--
-- The preferred projective extension therefore consumes a positive projective
-- cylinder probability, not a merely finitely-additive scalar assignment.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PositiveCylinderEventSemantics
    (Configuration Event : Set) : Set₁ where
  field
    events : R498.CylinderEventAlgebra Configuration Event

    indicatorNonnegative :
      ∀ event →
      Finite.PointwiseNonnegative
        (R498.indicator events event)

open PositiveCylinderEventSemantics public

record PositiveCylinderProbabilityPremeasure
    (Event : Set) : Set₁ where
  field
    premeasure :
      R495.CylinderProbabilityPremeasure Event ℝ

    massNonnegative :
      ∀ event →
      0ℝ ≤ℝ R495.mass premeasure event

open PositiveCylinderProbabilityPremeasure public

finitePositiveEventProbability :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (positiveEvents :
      PositiveCylinderEventSemantics Configuration Event)
    (cutoff : Nat) →
  PositiveCylinderProbabilityPremeasure Event
finitePositiveEventProbability family positiveEvents cutoff = record
  { PositiveCylinderProbabilityPremeasure.premeasure =
      R498.finiteEventProbability family (events positiveEvents) cutoff
  ; PositiveCylinderProbabilityPremeasure.massNonnegative =
      λ event →
        Limit.finiteExpectationPositive family cutoff
          (R498.indicator (events positiveEvents) event)
          (indicatorNonnegative positiveEvents event)
  }

record ProjectivePositiveCylinderProbability
    (Index Event : Set) : Set₂ where
  field
    levelProbability :
      Index → PositiveCylinderProbabilityPremeasure Event

    Restricts : Index → Index → Set
    restrictEvent :
      ∀ lower upper → Restricts lower upper → Event → Event

    projectiveMassConsistency :
      ∀ lower upper
        (restriction : Restricts lower upper)
        event →
      R495.mass (premeasure (levelProbability lower))
        (restrictEvent lower upper restriction event)
      ≡
      R495.mass (premeasure (levelProbability upper))
        event

open ProjectivePositiveCylinderProbability public

underlyingProjectiveProbability :
  ∀ {Index Event} →
  ProjectivePositiveCylinderProbability Index Event →
  R495.ProjectiveCylinderProbability Index Event ℝ
underlyingProjectiveProbability positive = record
  { R495.ProjectiveCylinderProbability.levelPremeasure =
      λ index → premeasure (levelProbability positive index)
  ; R495.ProjectiveCylinderProbability.Restricts =
      Restricts positive
  ; R495.ProjectiveCylinderProbability.restrictEvent =
      restrictEvent positive
  ; R495.ProjectiveCylinderProbability.projectiveMassConsistency =
      projectiveMassConsistency positive
  }

record PhysicalPositiveProjectiveCylinderInputs
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
    positiveEvents :
      PositiveCylinderEventSemantics Configuration Event

    Restricts : Nat → Nat → Set
    restrictEvent :
      ∀ lower upper → Restricts lower upper → Event → Event

    projectiveEventExpectationConsistency :
      ∀ lower upper
        (restriction : Restricts lower upper)
        event →
      Limit.finiteExpectation family lower
        (R498.indicator (events positiveEvents)
          (restrictEvent lower upper restriction event))
      ≡
      Limit.finiteExpectation family upper
        (R498.indicator (events positiveEvents) event)

open PhysicalPositiveProjectiveCylinderInputs public

asPositiveProjectiveCylinderProbability :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  PhysicalPositiveProjectiveCylinderInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  ProjectivePositiveCylinderProbability Nat Event
asPositiveProjectiveCylinderProbability {family = family} inputs = record
  { ProjectivePositiveCylinderProbability.levelProbability =
      λ cutoff →
        finitePositiveEventProbability
          family (positiveEvents inputs) cutoff
  ; ProjectivePositiveCylinderProbability.Restricts =
      Restricts inputs
  ; ProjectivePositiveCylinderProbability.restrictEvent =
      restrictEvent inputs
  ; ProjectivePositiveCylinderProbability.projectiveMassConsistency =
      projectiveEventExpectationConsistency inputs
  }

round538FiniteProbabilityPositivityCompilerLevel : ProofLevel
round538FiniteProbabilityPositivityCompilerLevel = machineChecked

round538PositiveProjectiveAssemblyCompilerLevel : ProofLevel
round538PositiveProjectiveAssemblyCompilerLevel = machineChecked

-- Same physical event interpretation/projective-consistency seam as before,
-- now with the previously implicit positivity of event indicators made explicit.
literalRound538PositiveCylinderEventSemanticsLevel : ProofLevel
literalRound538PositiveCylinderEventSemanticsLevel = conditional

literalRound538ProjectiveEventExpectationConsistencyLevel : ProofLevel
literalRound538ProjectiveEventExpectationConsistencyLevel = conditional
