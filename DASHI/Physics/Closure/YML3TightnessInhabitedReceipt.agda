module DASHI.Physics.Closure.YML3TightnessInhabitedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as Balaban
import DASHI.Physics.Closure.Phase2ProgrammeReceipt as Phase2
import DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt as Wilson
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as PriorL3

------------------------------------------------------------------------
-- YM L3 tightness candidate receipt.
--
-- This receipt corrects the prior overclaim.  The product lattice route is
-- retired, Balaban citation authority is valid only for genuine 4D lattices,
-- and those authority conditions are not met by the carrier three-site
-- spatial lattice.  The dimensional-transmutation argument is retained only as
-- a non-promoting argument surface.

data YML3ConditionalInhabitationStatus : Set where
  candidate :
    YML3ConditionalInhabitationStatus

  retiredConditionalOverclaim :
    YML3ConditionalInhabitationStatus

data YML3TightnessCondition : Set where
  conditionDimensionalTransmutationArgumentOnly :
    YML3TightnessCondition

  conditionBalabanAuthorityConditionsNotMet :
    YML3TightnessCondition

  conditionProductLatticeRetired :
    YML3TightnessCondition

  conditionCarrierSpatialLatticeNot4DHypercubic :
    YML3TightnessCondition

canonicalYML3TightnessConditions :
  List YML3TightnessCondition
canonicalYML3TightnessConditions =
  conditionDimensionalTransmutationArgumentOnly
  ∷ conditionBalabanAuthorityConditionsNotMet
  ∷ conditionProductLatticeRetired
  ∷ conditionCarrierSpatialLatticeNot4DHypercubic
  ∷ []

data YML3TightnessAuthority : Set where
  noBalabanAuthorityForCarrierThreeSiteSpatialLattice :
    YML3TightnessAuthority

canonicalYML3TightnessAuthorities :
  List YML3TightnessAuthority
canonicalYML3TightnessAuthorities =
  noBalabanAuthorityForCarrierThreeSiteSpatialLattice
  ∷ []

data YML3LimitOrderStep : Set where
  firstThermodynamicLimit :
    YML3LimitOrderStep

  secondContinuumLimit :
    YML3LimitOrderStep

canonicalYML3LimitOrder :
  List YML3LimitOrderStep
canonicalYML3LimitOrder =
  firstThermodynamicLimit
  ∷ secondContinuumLimit
  ∷ []

data YML3TightnessPromotion : Set where

yml3TightnessPromotionImpossibleHere :
  YML3TightnessPromotion →
  ⊥
yml3TightnessPromotionImpossibleHere ()

balaban1985TightnessAuthorityLabel : String
balaban1985TightnessAuthorityLabel =
  "Balaban 1985 citation authority is valid only for genuine 4D lattices; carrier three-site spatial lattice conditions are not met"

yml3TightnessInhabitedStatement : String
yml3TightnessInhabitedStatement =
  "YM L3 tightness remains candidate: dimensional transmutation is argument-only, the product lattice is retired, Balaban conditions are not met by the carrier three-site spatial lattice, and no tightness, Clay, or continuum promotion follows."

record YML3TightnessInhabitedReceipt : Setω where
  field
    priorCandidateReceipt :
      PriorL3.YML3TightnessFromKRunningReceipt

    priorCandidateWasNotInhabited :
      PriorL3.ymL3TightnessConstructed priorCandidateReceipt ≡ true

    phase2ReframeReceipt :
      Phase2.ManagerCClayReframeReceipt

    productLatticeBalabanRouteAlreadyRecorded :
      Phase2.productLatticeBalabanRouteRecorded phase2ReframeReceipt
        ≡ true

    productLatticeUniversalityStillOpenInPhase2 :
      Phase2.productLatticeUniversalityClassSettled phase2ReframeReceipt
        ≡ false

    wilsonReceipt :
      Wilson.WilsonActionOn3PlusOneLatticeReceipt

    wilsonActionDefined :
      Wilson.wilsonActionDefinedOnCarrierLattice wilsonReceipt ≡ true

    balabanSurface :
      Balaban.BalabanRGMassGapReceiptSurface

    balabanLocalFiniteCarrierGapRecorded :
      Balaban.localFiniteCarrierSpectralGapPromoted balabanSurface
        ≡ true

    balabanContinuumClayStillFalse :
      Balaban.continuumClayMassGapPromoted balabanSurface ≡ false

    ymL3Status :
      YML3ConditionalInhabitationStatus

    ymL3StatusIsCandidate :
      ymL3Status ≡ candidate

    dimensionalTransmutationArgumentOnly :
      Bool

    dimensionalTransmutationArgumentOnlyIsTrue :
      dimensionalTransmutationArgumentOnly ≡ true

    balabanAuthorityConditionsNotMet :
      Bool

    balabanAuthorityConditionsNotMetIsTrue :
      balabanAuthorityConditionsNotMet ≡ true

    productLatticeRetired :
      Bool

    productLatticeRetiredIsTrue :
      productLatticeRetired ≡ true

    carrierSpatialLatticeNot4DHypercubic :
      Bool

    carrierSpatialLatticeNot4DHypercubicIsTrue :
      carrierSpatialLatticeNot4DHypercubic ≡ true

    balaban1985CitationAuthorityAcceptedForTightness :
      Bool

    balaban1985CitationAuthorityAcceptedForTightnessIsFalse :
      balaban1985CitationAuthorityAcceptedForTightness ≡ false

    productLatticeWilsonMeasuresMuKRecorded :
      Bool

    productLatticeWilsonMeasuresMuKRecordedIsFalse :
      productLatticeWilsonMeasuresMuKRecorded ≡ false

    tightnessForMuKAboveK0 :
      Bool

    tightnessForMuKAboveK0IsFalse :
      tightnessForMuKAboveK0 ≡ false

    thermodynamicLimitFirst :
      Bool

    thermodynamicLimitFirstIsTrue :
      thermodynamicLimitFirst ≡ true

    continuumLimitSecond :
      Bool

    continuumLimitSecondIsTrue :
      continuumLimitSecond ≡ true

    ymL3TightnessInhabited :
      Bool

    ymL3TightnessInhabitedIsFalse :
      ymL3TightnessInhabited ≡ false

    unconditionalYML3TightnessPromoted :
      Bool

    unconditionalYML3TightnessPromotedIsFalse :
      unconditionalYML3TightnessPromoted ≡ false

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

    conditions :
      List YML3TightnessCondition

    conditionsAreCanonical :
      conditions ≡ canonicalYML3TightnessConditions

    authorities :
      List YML3TightnessAuthority

    authoritiesAreCanonical :
      authorities ≡ canonicalYML3TightnessAuthorities

    limitOrder :
      List YML3LimitOrderStep

    limitOrderIsCanonical :
      limitOrder ≡ canonicalYML3LimitOrder

    authorityLabel :
      String

    authorityLabelIsCanonical :
      authorityLabel ≡ balaban1985TightnessAuthorityLabel

    statement :
      String

    statementIsCanonical :
      statement ≡ yml3TightnessInhabitedStatement

    promotionFlags :
      List YML3TightnessPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML3TightnessInhabitedReceipt public

canonicalYML3TightnessInhabitedReceipt :
  YML3TightnessInhabitedReceipt
canonicalYML3TightnessInhabitedReceipt =
  record
    { priorCandidateReceipt =
        PriorL3.canonicalYML3TightnessFromKRunningReceipt
    ; priorCandidateWasNotInhabited =
        refl
    ; phase2ReframeReceipt =
        Phase2.canonicalManagerCClayReframeReceipt
    ; productLatticeBalabanRouteAlreadyRecorded =
        refl
    ; productLatticeUniversalityStillOpenInPhase2 =
        refl
    ; wilsonReceipt =
        Wilson.canonicalWilsonActionOn3PlusOneLatticeReceipt
    ; wilsonActionDefined =
        refl
    ; balabanSurface =
        Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; balabanLocalFiniteCarrierGapRecorded =
        refl
    ; balabanContinuumClayStillFalse =
        refl
    ; ymL3Status =
        candidate
    ; ymL3StatusIsCandidate =
        refl
    ; dimensionalTransmutationArgumentOnly =
        true
    ; dimensionalTransmutationArgumentOnlyIsTrue =
        refl
    ; balabanAuthorityConditionsNotMet =
        true
    ; balabanAuthorityConditionsNotMetIsTrue =
        refl
    ; productLatticeRetired =
        true
    ; productLatticeRetiredIsTrue =
        refl
    ; carrierSpatialLatticeNot4DHypercubic =
        true
    ; carrierSpatialLatticeNot4DHypercubicIsTrue =
        refl
    ; balaban1985CitationAuthorityAcceptedForTightness =
        false
    ; balaban1985CitationAuthorityAcceptedForTightnessIsFalse =
        refl
    ; productLatticeWilsonMeasuresMuKRecorded =
        false
    ; productLatticeWilsonMeasuresMuKRecordedIsFalse =
        refl
    ; tightnessForMuKAboveK0 =
        false
    ; tightnessForMuKAboveK0IsFalse =
        refl
    ; thermodynamicLimitFirst =
        true
    ; thermodynamicLimitFirstIsTrue =
        refl
    ; continuumLimitSecond =
        true
    ; continuumLimitSecondIsTrue =
        refl
    ; ymL3TightnessInhabited =
        false
    ; ymL3TightnessInhabitedIsFalse =
        refl
    ; unconditionalYML3TightnessPromoted =
        false
    ; unconditionalYML3TightnessPromotedIsFalse =
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
    ; conditions =
        canonicalYML3TightnessConditions
    ; conditionsAreCanonical =
        refl
    ; authorities =
        canonicalYML3TightnessAuthorities
    ; authoritiesAreCanonical =
        refl
    ; limitOrder =
        canonicalYML3LimitOrder
    ; limitOrderIsCanonical =
        refl
    ; authorityLabel =
        balaban1985TightnessAuthorityLabel
    ; authorityLabelIsCanonical =
        refl
    ; statement =
        yml3TightnessInhabitedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "YML3 remains candidate; the previous conditional-inhabitation claim is retired"
        ∷ "Dimensional transmutation is retained only as an argument surface"
        ∷ "Balaban citation authority is valid only for genuine 4D lattices and conditions are not met by the carrier three-site spatial lattice"
        ∷ "The product lattice route is retired, so no product-lattice Wilson-measure tightness is recorded here"
        ∷ "No tightness inhabitation, continuum Yang-Mills, Clay Yang-Mills, continuum mass-gap, or terminal Clay promotion follows"
        ∷ []
    }

yml3StatusCandidate :
  ymL3Status canonicalYML3TightnessInhabitedReceipt
  ≡
  candidate
yml3StatusCandidate =
  refl

yml3TightnessNotInhabited :
  ymL3TightnessInhabited canonicalYML3TightnessInhabitedReceipt
  ≡
  false
yml3TightnessNotInhabited =
  refl

yml3TightnessInhabitedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML3TightnessInhabitedReceipt ≡ false
yml3TightnessInhabitedKeepsClayFalse =
  refl

yml3TightnessInhabitedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML3TightnessInhabitedReceipt
  ≡
  false
yml3TightnessInhabitedKeepsTerminalFalse =
  refl
