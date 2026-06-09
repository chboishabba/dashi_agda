module DASHI.Physics.Closure.NextSessionPriorityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Phase2BlockerMapFinalReceipt as Map

------------------------------------------------------------------------
-- Ordered next-session research priorities.

data NextSessionPriorityStatus : Set where
  nextSessionPrioritiesRecordedNoPromotion :
    NextSessionPriorityStatus

data NextSessionPriority : Set where
  ymTightness :
    NextSessionPriority

  vubFromCPMechanism :
    NextSessionPriority

  su2su3FormalDecoupling :
    NextSessionPriority

canonicalNextSessionPriorities :
  List NextSessionPriority
canonicalNextSessionPriorities =
  ymTightness
  ∷ vubFromCPMechanism
  ∷ su2su3FormalDecoupling
  ∷ []

ymTightnessPriorityStatement : String
ymTightnessPriorityStatement =
  "YM tightness: prove the CS-level lattice measure family mu_k is tight by upgrading the weak-coupling string-tension/dimensional-transmutation argument to a uniform plaquette-action bound."

vubPriorityStatement : String
vubPriorityStatement =
  "Vub from CP mechanism: replace the failed direct (1,3) Hecke-degree route by computing Wolfenstein rho and eta from an identified carrier source of CP violation."

su2su3PriorityStatement : String
su2su3PriorityStatement =
  "SU2-SU3 formal decoupling: verify that the SM fermion representations satisfy the SET inequivalence conditions for breaking the SU(2)_3 <-> SU(3)_1 level-rank identification."

nextSessionPriorityStatement : String
nextSessionPriorityStatement =
  "Next session priorities are YM tightness, Vub from CP mechanism, and SU2-SU3 formal decoupling; all Clay and terminal promotions remain false."

data NextSessionPromotion : Set where

nextSessionPromotionImpossibleHere :
  NextSessionPromotion →
  ⊥
nextSessionPromotionImpossibleHere ()

record NextSessionPriorityReceipt : Setω where
  field
    status :
      NextSessionPriorityStatus

    blockerMap :
      Map.Phase2BlockerMapFinalReceipt

    blockerMapKeepsTerminalFalse :
      Map.terminalUnificationPromoted blockerMap ≡ false

    priorities :
      List NextSessionPriority

    prioritiesAreCanonical :
      priorities ≡ canonicalNextSessionPriorities

    ymTightnessPriority :
      String

    ymTightnessPriorityIsCanonical :
      ymTightnessPriority ≡ ymTightnessPriorityStatement

    vubPriority :
      String

    vubPriorityIsCanonical :
      vubPriority ≡ vubPriorityStatement

    su2su3Priority :
      String

    su2su3PriorityIsCanonical :
      su2su3Priority ≡ su2su3PriorityStatement

    nextSessionPrioritiesRecorded :
      Bool

    nextSessionPrioritiesRecordedIsTrue :
      nextSessionPrioritiesRecorded ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    promotionFlags :
      List NextSessionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nextSessionPriorityStatement

    receiptBoundary :
      List String

open NextSessionPriorityReceipt public

canonicalNextSessionPriorityReceipt :
  NextSessionPriorityReceipt
canonicalNextSessionPriorityReceipt =
  record
    { status =
        nextSessionPrioritiesRecordedNoPromotion
    ; blockerMap =
        Map.canonicalPhase2BlockerMapFinalReceipt
    ; blockerMapKeepsTerminalFalse =
        refl
    ; priorities =
        canonicalNextSessionPriorities
    ; prioritiesAreCanonical =
        refl
    ; ymTightnessPriority =
        ymTightnessPriorityStatement
    ; ymTightnessPriorityIsCanonical =
        refl
    ; vubPriority =
        vubPriorityStatement
    ; vubPriorityIsCanonical =
        refl
    ; su2su3Priority =
        su2su3PriorityStatement
    ; su2su3PriorityIsCanonical =
        refl
    ; nextSessionPrioritiesRecorded =
        true
    ; nextSessionPrioritiesRecordedIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nextSessionPriorityStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Priorities are ordered work targets, not completed theorem claims"
        ∷ "YM tightness is first because it is the most concrete remaining Clay-adjacent target"
        ∷ "Vub work is redirected through the unresolved carrier CP mechanism"
        ∷ "SU2-SU3 formal decoupling stays candidate until the SET representation-theory hypothesis is checked"
        ∷ []
    }

nextSessionPriorityKeepsClayFalse :
  clayYangMillsPromoted canonicalNextSessionPriorityReceipt ≡ false
nextSessionPriorityKeepsClayFalse =
  refl

nextSessionPriorityKeepsTerminalFalse :
  terminalUnificationPromoted canonicalNextSessionPriorityReceipt
  ≡
  false
nextSessionPriorityKeepsTerminalFalse =
  refl
