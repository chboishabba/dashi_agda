module DASHI.Promotion.PluralSituatedHypothesisBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.SystemicDistressReframingBoundary as Distress

------------------------------------------------------------------------
-- A high distress or gluing-defect signal opens a field of hypotheses.  It
-- does not select one exclusive cause by itself.

data HypothesisKind : Set where
  personalHypothesis : HypothesisKind
  biologicalHypothesis : HypothesisKind
  relationalHypothesis : HypothesisKind
  environmentalHypothesis : HypothesisKind
  institutionalHypothesis : HypothesisKind
  economicHypothesis : HypothesisKind
  interpretiveHypothesis : HypothesisKind
  measurementHypothesis : HypothesisKind
  mixedHypothesis : HypothesisKind

data HypothesisStatus : Set where
  proposed supported qualified underdetermined rejected : HypothesisStatus

record HypothesisCandidate : Set where
  constructor hypothesisCandidate
  field
    kind : HypothesisKind
    status : HypothesisStatus
    label : String
    evidenceStillRequired : Bool
    exclusiveExplanationClaimed : Bool

open HypothesisCandidate public

canonicalHypothesisField : List HypothesisCandidate
canonicalHypothesisField =
  hypothesisCandidate personalHypothesis underdetermined
    "personal history and present constraints" true false
  ∷ hypothesisCandidate biologicalHypothesis underdetermined
    "biological, neurological, sleep, pain, medication, or other bodily factors" true false
  ∷ hypothesisCandidate relationalHypothesis underdetermined
    "relationship, care, conflict, attachment, or communication conditions" true false
  ∷ hypothesisCandidate environmentalHypothesis underdetermined
    "sensory, housing, work, place, climate, or material surroundings" true false
  ∷ hypothesisCandidate institutionalHypothesis underdetermined
    "institutional rules, service access, authority, or exclusion" true false
  ∷ hypothesisCandidate economicHypothesis underdetermined
    "resource, labour, debt, precarity, or profit feedback" true false
  ∷ hypothesisCandidate interpretiveHypothesis underdetermined
    "the current frame may be incomplete or distorting" true false
  ∷ hypothesisCandidate measurementHypothesis underdetermined
    "the operator, proxy, sample, or chart may be wrong" true false
  ∷ []

------------------------------------------------------------------------
-- Standpoint may supply access which another chart lacks.  Epistemic advantage
-- requires comparison and method; position alone is not infallibility.

record SituatedAccessReceipt : Set where
  constructor situatedAccessReceipt
  field
    livedConditionAccess : Bool
    dominantFrameAccess : Bool
    crossFrameComparison : Bool
    criticalMethodApplied : Bool
    potentialEpistemicAdvantage : Bool
    automaticInfallibility : Bool
    automaticInfallibilityIsFalse : automaticInfallibility ≡ false
    interpretation : String

canonicalSituatedAccessReceipt : SituatedAccessReceipt
canonicalSituatedAccessReceipt =
  situatedAccessReceipt
    true
    true
    true
    true
    true
    false refl
    "dual access to lived conditions and a governing frame may yield epistemic advantage when comparison and critical method are present; standpoint is not automatic completeness"

record PluralHypothesisBoundary : Set where
  constructor pluralHypothesisBoundary
  field
    sourceSignal : Distress.DistressSignal
    hypothesesRemainPlural : Bool
    personalFactorsRetained : Bool
    biologicalFactorsRetained : Bool
    relationalAndSystemicFactorsRetained : Bool
    measurementFailureRetained : Bool
    signalSelectsUniqueCause : Bool
    signalSelectsUniqueCauseIsFalse : signalSelectsUniqueCause ≡ false
    marginalPositionGuaranteesTruth : Bool
    marginalPositionGuaranteesTruthIsFalse :
      marginalPositionGuaranteesTruth ≡ false
    systemicExplanationExcludesOtherLanes : Bool
    systemicExplanationExcludesOtherLanesIsFalse :
      systemicExplanationExcludesOtherLanes ≡ false
    interpretation : String

canonicalPluralHypothesisBoundary : PluralHypothesisBoundary
canonicalPluralHypothesisBoundary =
  pluralHypothesisBoundary
    Distress.canonicalDistressSignal
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "situated distress may open personal, biological, relational, environmental, institutional, economic, interpretive, and measurement hypotheses without selecting an exclusive cause"
