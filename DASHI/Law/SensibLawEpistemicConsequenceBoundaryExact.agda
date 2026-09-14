module DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

------------------------------------------------------------------------
-- EPISTEMIC UNCERTAINTY × CONSEQUENCE SEVERITY × REVERSIBILITY
--
-- Analytical coordinates only.  This owner does not invent a legal threshold,
-- determine proportionality, prohibit action, or decide the truth of an
-- underlying inference.
------------------------------------------------------------------------

data EpistemicUncertainty : Set where
  lowUncertainty : EpistemicUncertainty
  mediumUncertainty : EpistemicUncertainty
  highUncertainty : EpistemicUncertainty
  unresolvedUncertainty : EpistemicUncertainty

data ConsequenceSeverity : Set where
  lowSeverity : ConsequenceSeverity
  moderateSeverity : ConsequenceSeverity
  severeConsequence : ConsequenceSeverity
  extremeConsequence : ConsequenceSeverity

data Reversibility : Set where
  readilyReversible : Reversibility
  partlyReversible : Reversibility
  difficultToReverse : Reversibility
  irreversible : Reversibility

record EpistemicConsequenceState : Set where
  constructor epistemicConsequenceState
  field
    uncertainty : EpistemicUncertainty
    severity : ConsequenceSeverity
    reversibility : Reversibility

open EpistemicConsequenceState public

record EpistemicConsequenceBoundary : Set where
  constructor epistemicConsequenceBoundary
  field
    highConsequenceAutomaticallyUnderlyingInferenceFalse : Bool
    highUncertaintyAutomaticallyProhibitsAction : Bool
    legalAvailabilityAutomaticallyAdequateForEveryConsumer : Bool
    highUncertaintyAutomaticallyEstablishesIllegality : Bool
    severeConsequenceAutomaticallyEstablishesDisproportionality : Bool
    severityAndReversibilityAreSeparateCoordinates : Bool
    uncertaintyAndTruthAreSeparateCoordinates : Bool

open EpistemicConsequenceBoundary public

canonicalEpistemicConsequenceBoundary : EpistemicConsequenceBoundary
canonicalEpistemicConsequenceBoundary =
  epistemicConsequenceBoundary
    false
    false
    false
    false
    false
    true
    true
