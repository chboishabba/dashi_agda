module DASHI.Cognition.PNF.SpokenTelescopeFutureEquivalenceExact where

------------------------------------------------------------------------
-- CURRENT QUERY EQUALITY IS STRICTLY WEAKER THAN FUTURE EQUIVALENCE
--
-- The telescope example already proves that both parses answer "who was seen?"
-- with John, while a later holder query separates them.  Here that example is
-- instantiated against the canonical proof-bearing future-observation language
-- relation.  Thus the parses are equal for one current consumer projection but
-- cannot inhabit the same future-safe quotient class.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpokenTelescopeConsumerProjectionExact as Spoken
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Deterministic discourse update embedded into DependentActionSystem.
------------------------------------------------------------------------

record ExactDiscoursePost
    (before : Spoken.SpokenPNFState)
    (action : Spoken.DiscourseAction)
    (after : Spoken.SpokenPNFState) : Set where
  constructor exactDiscoursePost
  field
    afterIsExact : after ≡ Spoken.advanceDiscourse action before

open ExactDiscoursePost public

discourseSystem :
  Dependency.DependentActionSystem
    Spoken.SpokenPNFState Spoken.DiscourseAction
discourseSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactDiscoursePost
  ; actionLabel = λ action → "continue discourse"
  }

continueAdmissible :
  (state : Spoken.SpokenPNFState) →
  Dependency.AdmissibleAction
    discourseSystem state Spoken.continueToHolderQuestion
continueAdmissible state = record
  { precondition = tt
  ; after = Spoken.advanceDiscourse Spoken.continueToHolderQuestion state
  ; postcondition = exactDiscoursePost refl
  ; dependencyReceipt = "deterministic holder-question continuation"
  }

continueTrace : Spoken.DiscourseAction ∷ []
continueTrace = Spoken.continueToHolderQuestion ∷ []

instrumentFutureHolderObservation :
  Future.FutureObservation
    discourseSystem
    Spoken.observeForCurrentQuestion
    Spoken.instrumentState
    continueTrace
    (Spoken.holderAnswer Spoken.speaker)
instrumentFutureHolderObservation =
  Future.futureObservation
    (Spoken.advanceDiscourse
      Spoken.continueToHolderQuestion Spoken.instrumentState)
    (Reachability.executesCons
      (continueAdmissible Spoken.instrumentState)
      Reachability.executesNil)
    refl

------------------------------------------------------------------------
-- The same holder=speaker observation cannot arise from the possession parse.
------------------------------------------------------------------------

possessionCannotReachSpeakerHolder :
  Future.FutureObservation
    discourseSystem
    Spoken.observeForCurrentQuestion
    Spoken.possessionState
    continueTrace
    (Spoken.holderAnswer Spoken.speaker)
  → ⊥
possessionCannotReachSpeakerHolder
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsExact (Dependency.postcondition admissible)
... | refl = contradiction observationProof
  where
    contradiction :
      Spoken.holderAnswer Spoken.john
      ≡ Spoken.holderAnswer Spoken.speaker → ⊥
    contradiction ()

currentWhoSeenStillEqual :
  Spoken.whoSeenProjection Spoken.instrumentState
  ≡ Spoken.whoSeenProjection Spoken.possessionState
currentWhoSeenStillEqual = Spoken.whoSeenConsumerMayCollapseCurrentParse

parsesAreNotFutureEquivalent :
  Future.FutureObservationEquivalent
    discourseSystem
    Spoken.observeForCurrentQuestion
    Spoken.instrumentState
    Spoken.possessionState
  → ⊥
parsesAreNotFutureEquivalent equivalent =
  possessionCannotReachSpeakerHolder
    (Future.forward
      (Future.sameFutureLanguage equivalent
        continueTrace
        (Spoken.holderAnswer Spoken.speaker))
      instrumentFutureHolderObservation)

------------------------------------------------------------------------
-- Exact boundary: present answer equality is valid for the bounded query, but
-- it cannot certify membership in the canonical future-safe quotient class.
------------------------------------------------------------------------
