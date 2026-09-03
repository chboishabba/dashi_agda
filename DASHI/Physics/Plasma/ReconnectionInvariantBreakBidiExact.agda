module DASHI.Physics.Plasma.ReconnectionInvariantBreakBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.IdealMHDReconnectionBidiExact as Reconnection
import DASHI.Physics.Plasma.MHDInvariantFibreBidiExact as Invariant

------------------------------------------------------------------------
-- RECONNECTION / INVARIANT BIDI CUT
--
-- Ideal invariants and topology preservation share hypotheses.  Once a
-- non-ideal reconnection producer is admitted, conservation cannot simply be
-- imported through the ideal lane; the relevant dissipation / boundary /
-- conversion budget must be supplied for the literal invariant.
------------------------------------------------------------------------

record InvariantBreakAssessment : Set₁ where
  constructor invariant-break-assessment
  field
    regime : Reconnection.PlasmaEvolutionRegime
    state : Reconnection.ReconnectionState
    mhdState : Invariant.MHDStateFibre
    observer : Invariant.InvariantObserver mhdState

    NonIdealContribution : Set
    BoundaryContribution : Set
    ConversionContribution : Set

    idealReceiptStillApplicable : Bool
    budgetRequired : Bool
    assessmentReference : String

open InvariantBreakAssessment public

record ReconnectionInvariantBudget
    (assessment : InvariantBreakAssessment) : Set₁ where
  constructor reconnection-invariant-budget
  field
    dissipativeBudget :
      Invariant.DissipativeInvariantBudget
        (mhdState assessment)
        (observer assessment)
    reconnectionCouplingReceipt : Set
    sameObjectInvariantWeld : Set
    budgetReference : String

open ReconnectionInvariantBudget public

record ReconnectionInvariantBoundary : Set where
  constructor reconnection-invariant-boundary
  field
    reconnectionImpliesAllMHDInvariantsVanish : Bool
    reconnectionImpliesAllMHDInvariantsVanishIsFalse :
      reconnectionImpliesAllMHDInvariantsVanish ≡ false

    nonIdealPhysicsAutomaticallyDestroysMagneticHelicity : Bool
    nonIdealPhysicsAutomaticallyDestroysMagneticHelicityIsFalse :
      nonIdealPhysicsAutomaticallyDestroysMagneticHelicity ≡ false

    idealConservationReceiptSurvivesNonIdealRegimeWithoutBudget : Bool
    idealConservationReceiptSurvivesNonIdealRegimeWithoutBudgetIsFalse :
      idealConservationReceiptSurvivesNonIdealRegimeWithoutBudget ≡ false

    reconnectionRequiresInvariantSpecificBalanceAudit : Bool
    reconnectionRequiresInvariantSpecificBalanceAuditIsTrue :
      reconnectionRequiresInvariantSpecificBalanceAudit ≡ true

    topologyChangeAndInvariantDecayAreSameObservable : Bool
    topologyChangeAndInvariantDecayAreSameObservableIsFalse :
      topologyChangeAndInvariantDecayAreSameObservable ≡ false

canonicalReconnectionInvariantBoundary : ReconnectionInvariantBoundary
canonicalReconnectionInvariantBoundary =
  reconnection-invariant-boundary false refl false refl false refl true refl false refl

------------------------------------------------------------------------
-- Reverse acquisition direction.
------------------------------------------------------------------------

record ReverseInvariantAcquisition : Set where
  constructor reverse-invariant-acquisition
  field
    observedTopologyChangeNeedsNonIdealProducer : Bool
    observedTopologyChangeNeedsNonIdealProducerIsTrue :
      observedTopologyChangeNeedsNonIdealProducer ≡ true

    observedInvariantChangeNeedsBalanceTerms : Bool
    observedInvariantChangeNeedsBalanceTermsIsTrue :
      observedInvariantChangeNeedsBalanceTerms ≡ true

    invariantChangeAloneIdentifiesReconnection : Bool
    invariantChangeAloneIdentifiesReconnectionIsFalse :
      invariantChangeAloneIdentifiesReconnection ≡ false

canonicalReverseInvariantAcquisition : ReverseInvariantAcquisition
canonicalReverseInvariantAcquisition =
  reverse-invariant-acquisition true refl true refl false refl
