{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND498:
-- FINITE NORMALIZED EXPECTATION -> CYLINDER PROBABILITY PREMEASURE
--
-- Finite additivity is not a new measure theorem.  Once a cylinder event has a
-- literal indicator observable and disjoint union is represented by addition of
-- indicators, the already-proved normalized expectation algebra gives:
--
--   P_n(empty)=0
--   P_n(whole)=1
--   P_n(A union B)=P_n(A)+P_n(B) for disjoint A,B.
--
-- The remaining source-facing M1 data are therefore:
--
--   E1 literal cylinder-event/indicator semantics;
--   E2 projective consistency of those event expectations across cutoffs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; cong; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; 1ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495

record CylinderEventAlgebra
    (Configuration Event : Set) : Set₁ where
  field
    empty whole : Event
    complement : Event → Event
    union : Event → Event → Event
    Disjoint : Event → Event → Set

    indicator : Event → Configuration → ℝ

    emptyIndicator :
      indicator empty ≡ Finite.zeroObservable

    wholeIndicator :
      indicator whole ≡ Finite.oneObservable

    disjointUnionIndicator :
      ∀ left right →
      Disjoint left right →
      indicator (union left right)
      ≡ Finite.addObservable (indicator left) (indicator right)

open CylinderEventAlgebra public

finiteEventProbability :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (events : CylinderEventAlgebra Configuration Event)
    (cutoff : Nat) →
  R495.CylinderProbabilityPremeasure Event ℝ
finiteEventProbability family events cutoff = record
  { R495.CylinderProbabilityPremeasure.empty =
      empty events
  ; R495.CylinderProbabilityPremeasure.whole =
      whole events
  ; R495.CylinderProbabilityPremeasure.complement =
      complement events
  ; R495.CylinderProbabilityPremeasure.union =
      union events
  ; R495.CylinderProbabilityPremeasure.Disjoint =
      Disjoint events
  ; R495.CylinderProbabilityPremeasure.zero =
      0ℝ
  ; R495.CylinderProbabilityPremeasure.one =
      1ℝ
  ; R495.CylinderProbabilityPremeasure.add =
      _+ℝ_
  ; R495.CylinderProbabilityPremeasure.mass =
      λ event → Limit.finiteExpectation family cutoff (indicator events event)
  ; R495.CylinderProbabilityPremeasure.emptyMass =
      trans
        (cong
          (Limit.finiteExpectation family cutoff)
          (emptyIndicator events))
        (Limit.finiteExpectationZero family cutoff)
  ; R495.CylinderProbabilityPremeasure.wholeMass =
      trans
        (cong
          (Limit.finiteExpectation family cutoff)
          (wholeIndicator events))
        (Limit.finiteExpectationOne family cutoff)
  ; R495.CylinderProbabilityPremeasure.finiteAdditivity =
      λ left right disjoint →
        trans
          (cong
            (Limit.finiteExpectation family cutoff)
            (disjointUnionIndicator events left right disjoint))
          (Limit.finiteExpectationAdd family cutoff
            (indicator events left)
            (indicator events right))
  }

record ProjectiveCylinderEventInputs
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
    events : CylinderEventAlgebra Configuration Event

    Restricts : Nat → Nat → Set
    restrictEvent :
      ∀ lower upper → Restricts lower upper → Event → Event

    -- Genuine source/projective payment: the SAME cylinder event seen at the
    -- lower cutoff has the same normalized probability as its upper-cutoff
    -- representative.
    projectiveEventExpectationConsistency :
      ∀ lower upper
        (restriction : Restricts lower upper)
        event →
      Limit.finiteExpectation family lower
        (indicator events
          (restrictEvent lower upper restriction event))
      ≡
      Limit.finiteExpectation family upper
        (indicator events event)

open ProjectiveCylinderEventInputs public

asProjectiveCylinderProbability :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  ProjectiveCylinderEventInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  R495.ProjectiveCylinderProbability Nat Event ℝ
asProjectiveCylinderProbability inputs = record
  { R495.ProjectiveCylinderProbability.levelPremeasure =
      λ cutoff →
        finiteEventProbability
          family (events inputs) cutoff
  ; R495.ProjectiveCylinderProbability.Restricts =
      Restricts inputs
  ; R495.ProjectiveCylinderProbability.restrictEvent =
      restrictEvent inputs
  ; R495.ProjectiveCylinderProbability.projectiveMassConsistency =
      projectiveEventExpectationConsistency inputs
  }

round498FinitePremeasureCompilerLevel : ProofLevel
round498FinitePremeasureCompilerLevel = machineChecked

round498ProjectivePremeasureCompilerLevel : ProofLevel
round498ProjectivePremeasureCompilerLevel = machineChecked

literalRound498CylinderEventIndicatorSemanticsLevel : ProofLevel
literalRound498CylinderEventIndicatorSemanticsLevel = conditional

literalRound498ProjectiveEventExpectationConsistencyLevel : ProofLevel
literalRound498ProjectiveEventExpectationConsistencyLevel = conditional
