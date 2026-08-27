module DASHI.Physics.Foundations.BidirectionalAdmissibleActionRealizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Action

------------------------------------------------------------------------
-- Bridge from a bidirectionally admissible history carrier to an additive
-- local-action carrier.
--
-- The bridge is deliberately explicit: having a history fibre and having a
-- transition kernel does not itself identify the states/steps of one with the
-- other.  A realization map is additional structure.
------------------------------------------------------------------------

record BidirectionalActionRealization
  (bidi : Bidi.BidirectionallyAdmissibleHistoryFibre)
  (action : Action.LocalActionSystem) : Set₁ where
  field
    realizeHistory :
      Bidi.History bidi →
      List (Action.Step action)

    realizationReading : String

open BidirectionalActionRealization public

actionOfRealizedHistory :
  {bidi : Bidi.BidirectionallyAdmissibleHistoryFibre} →
  {action : Action.LocalActionSystem} →
  BidirectionalActionRealization bidi action →
  Bidi.History bidi →
  Nat
actionOfRealizedHistory {action = action} realization history =
  Action.historyAction action (realizeHistory realization history)

record AdmissibleRealizedActionWitness
  {bidi : Bidi.BidirectionallyAdmissibleHistoryFibre}
  {action : Action.LocalActionSystem}
  (realization : BidirectionalActionRealization bidi action) : Set where
  field
    initialBoundary : Bidi.InitialBoundary bidi
    finalBoundary : Bidi.FinalBoundary bidi
    history : Bidi.History bidi

    admissibilityWitness :
      Bidi.admissibleFromBoth bidi initialBoundary finalBoundary history

    realizedAction : Nat
    realizedActionCorrect :
      realizedAction
      ≡
      actionOfRealizedHistory realization history

open AdmissibleRealizedActionWitness public

record BidirectionalActionRealizationBoundary : Set where
  constructor bidirectionalActionRealizationBoundary
  field
    historyFibreDeterminesStateEncoding : Bool
    historyFibreDeterminesStateEncodingIsFalse :
      historyFibreDeterminesStateEncoding ≡ false

    transitionKernelDeterminesHistoryRealization : Bool
    transitionKernelDeterminesHistoryRealizationIsFalse :
      transitionKernelDeterminesHistoryRealization ≡ false

    arbitraryRealizationIsPhysicalIdentification : Bool
    arbitraryRealizationIsPhysicalIdentificationIsFalse :
      arbitraryRealizationIsPhysicalIdentification ≡ false

canonicalBidirectionalActionRealizationBoundary :
  BidirectionalActionRealizationBoundary
canonicalBidirectionalActionRealizationBoundary =
  bidirectionalActionRealizationBoundary
    false refl
    false refl
    false refl
