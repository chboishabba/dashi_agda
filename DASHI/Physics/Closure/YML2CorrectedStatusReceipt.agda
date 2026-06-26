module DASHI.Physics.Closure.YML2CorrectedStatusReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WilsonBetaFromCSLevelReceipt as WilsonBeta
import DASHI.Physics.Closure.YML2StatusReceipt as L2

------------------------------------------------------------------------
-- Corrected YM L2 status after separating CS level from Wilson beta.

data YML2CorrectedEstablishedItem : Set where
  finiteStrongCouplingDiagnosticsRetained :
    YML2CorrectedEstablishedItem

  csLevelWilsonBetaDerivationRejected :
    YML2CorrectedEstablishedItem

canonicalYML2CorrectedEstablishedItems :
  List YML2CorrectedEstablishedItem
canonicalYML2CorrectedEstablishedItems =
  finiteStrongCouplingDiagnosticsRetained
  ∷ csLevelWilsonBetaDerivationRejected
  ∷ []

data YML2CorrectedOpenItem : Set where
  continuumBetaRunningMissing :
    YML2CorrectedOpenItem

  betaToInfinityTrajectoryMissing :
    YML2CorrectedOpenItem

  continuumGapSurvivalMissing :
    YML2CorrectedOpenItem

  l3TightnessMissing :
    YML2CorrectedOpenItem

canonicalYML2CorrectedOpenItems :
  List YML2CorrectedOpenItem
canonicalYML2CorrectedOpenItems =
  continuumBetaRunningMissing
  ∷ betaToInfinityTrajectoryMissing
  ∷ continuumGapSurvivalMissing
  ∷ l3TightnessMissing
  ∷ []

data YML2CorrectedPromotion : Set where

yml2CorrectedPromotionImpossibleHere :
  YML2CorrectedPromotion →
  ⊥
yml2CorrectedPromotionImpossibleHere ()

yml2CorrectedStatusStatement : String
yml2CorrectedStatusStatement =
  "Corrected YM L2 keeps finite strong-coupling diagnostics only; CS levels do not derive Wilson beta, and continuum beta running, L3 tightness, and gap survival remain open."

record YML2CorrectedStatusReceipt : Setω where
  field
    priorYML2StatusReceipt :
      L2.YML2StatusReceipt

    priorL2Partial :
      L2.ymL2PartiallyInhabited priorYML2StatusReceipt ≡ true

    priorContinuumRunningFalse :
      L2.continuumBetaRunningConstructed priorYML2StatusReceipt ≡ false

    wilsonBetaReceipt :
      WilsonBeta.WilsonBetaFromCSLevelReceipt

    betaTrajectoryStillFalse :
      WilsonBeta.betaToInfinityTrajectoryConstructed wilsonBetaReceipt
        ≡ false

    establishedItems :
      List YML2CorrectedEstablishedItem

    establishedItemsAreCanonical :
      establishedItems ≡ canonicalYML2CorrectedEstablishedItems

    openItems :
      List YML2CorrectedOpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalYML2CorrectedOpenItems

    ymL2PartiallyInhabited :
      Bool

    ymL2PartiallyInhabitedIsTrue :
      ymL2PartiallyInhabited ≡ true

    correctedContinuumBetaRunningConstructed :
      Bool

    correctedContinuumBetaRunningConstructedIsFalse :
      correctedContinuumBetaRunningConstructed ≡ false

    correctedYML3TightnessConstructed :
      Bool

    correctedYML3TightnessConstructedIsFalse :
      correctedYML3TightnessConstructed ≡ false

    continuumGapSurvivalProved :
      Bool

    continuumGapSurvivalProvedIsFalse :
      continuumGapSurvivalProved ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ yml2CorrectedStatusStatement

    promotionFlags :
      List YML2CorrectedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML2CorrectedStatusReceipt public

canonicalYML2CorrectedStatusReceipt :
  YML2CorrectedStatusReceipt
canonicalYML2CorrectedStatusReceipt =
  record
    { priorYML2StatusReceipt =
        L2.canonicalYML2StatusReceipt
    ; priorL2Partial =
        refl
    ; priorContinuumRunningFalse =
        refl
    ; wilsonBetaReceipt =
        WilsonBeta.canonicalWilsonBetaFromCSLevelReceipt
    ; betaTrajectoryStillFalse =
        refl
    ; establishedItems =
        canonicalYML2CorrectedEstablishedItems
    ; establishedItemsAreCanonical =
        refl
    ; openItems =
        canonicalYML2CorrectedOpenItems
    ; openItemsAreCanonical =
        refl
    ; ymL2PartiallyInhabited =
        true
    ; ymL2PartiallyInhabitedIsTrue =
        refl
    ; correctedContinuumBetaRunningConstructed =
        false
    ; correctedContinuumBetaRunningConstructedIsFalse =
        refl
    ; correctedYML3TightnessConstructed =
        false
    ; correctedYML3TightnessConstructedIsFalse =
        refl
    ; continuumGapSurvivalProved =
        false
    ; continuumGapSurvivalProvedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        yml2CorrectedStatusStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Finite strong-coupling L2 diagnostics remain recorded"
        ∷ "The CS-level-to-Wilson-beta derivation is rejected"
        ∷ "Continuum beta running, L3 tightness, and continuum gap survival remain open"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

yml2CorrectedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML2CorrectedStatusReceipt ≡ false
yml2CorrectedKeepsClayFalse =
  refl

yml2CorrectedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML2CorrectedStatusReceipt ≡ false
yml2CorrectedKeepsTerminalFalse =
  refl
