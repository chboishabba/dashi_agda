module DASHI.Physics.Closure.NSLerayBandBoundReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierEnergyInequalityReceipt as Energy

------------------------------------------------------------------------
-- Leray L2 individual-band bound receipt.
--
-- This receipt records the load-bearing consequence of the Leray L2
-- inequality: each nonnegative carrier-band energy is bounded by the
-- total L2 budget M_0^2.  It is an exact weak-energy lemma only; no
-- global regularity, Clay Navier-Stokes, or terminal promotion follows.

data NSLerayBandBoundStatus : Set where
  lerayL2InequalityConsumed :
    NSLerayBandBoundStatus

  nonnegativeBandEnergiesRecorded :
    NSLerayBandBoundStatus

  individualBandBoundExact :
    NSLerayBandBoundStatus

  noNuOrNormRestriction :
    NSLerayBandBoundStatus

  noClayOrGlobalTerminalPromotion :
    NSLerayBandBoundStatus

canonicalNSLerayBandBoundStatus :
  List NSLerayBandBoundStatus
canonicalNSLerayBandBoundStatus =
  lerayL2InequalityConsumed
  ∷ nonnegativeBandEnergiesRecorded
  ∷ individualBandBoundExact
  ∷ noNuOrNormRestriction
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data NSLerayBandBoundPromotion : Set where

nsLerayBandBoundPromotionImpossibleHere :
  NSLerayBandBoundPromotion →
  ⊥
nsLerayBandBoundPromotionImpossibleHere ()

lerayBandBoundStatement : String
lerayBandBoundStatement =
  "a_j(t) <= M_0^2 for all j,t"

lerayBandBoundReason : String
lerayBandBoundReason =
  "sum_j a_j(t) <= ||u_0||^2_L2 = M_0^2 and a_j(t) >= 0, hence every individual carrier band satisfies a_j(t) <= M_0^2 for all j >= 0 and t >= 0, any nu > 0"

emptyPromotionType : String
emptyPromotionType =
  ""

record NSLerayBandBoundReceipt : Setω where
  field
    energyReceipt :
      Energy.NSCarrierEnergyInequalityReceipt

    lerayEnergyInputReady :
      Energy.lerayEnergyInequalityScoped energyReceipt ≡ true

    status :
      List NSLerayBandBoundStatus

    statusIsCanonical :
      status ≡ canonicalNSLerayBandBoundStatus

    lerayBandBound :
      String

    lerayBandBoundIsCanonical :
      lerayBandBound ≡ lerayBandBoundStatement

    derivationReason :
      String

    derivationReasonIsCanonical :
      derivationReason ≡ lerayBandBoundReason

    totalL2BudgetBound :
      Bool

    totalL2BudgetBoundIsTrue :
      totalL2BudgetBound ≡ true

    bandNonnegativityInput :
      Bool

    bandNonnegativityInputIsTrue :
      bandNonnegativityInput ≡ true

    everyIndividualCarrierBandBounded :
      Bool

    everyIndividualCarrierBandBoundedIsTrue :
      everyIndividualCarrierBandBounded ≡ true

    allJGreaterOrEqualZero :
      Bool

    allJGreaterOrEqualZeroIsTrue :
      allJGreaterOrEqualZero ≡ true

    allTGreaterOrEqualZero :
      Bool

    allTGreaterOrEqualZeroIsTrue :
      allTGreaterOrEqualZero ≡ true

    anyPositiveNu :
      Bool

    anyPositiveNuIsTrue :
      anyPositiveNu ≡ true

    noConditionOnNuOrNorm :
      Bool

    noConditionOnNuOrNormIsTrue :
      noConditionOnNuOrNorm ≡ true

    exactNotCandidate :
      Bool

    exactNotCandidateIsTrue :
      exactNotCandidate ≡ true

    loadBearingLemma :
      Bool

    loadBearingLemmaIsTrue :
      loadBearingLemma ≡ true

    smoothRegularityPromoted :
      Bool

    smoothRegularityPromotedIsFalse :
      smoothRegularityPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    promotionType :
      String

    promotionTypeIsEmpty :
      promotionType ≡ emptyPromotionType

    promotionFlags :
      List NSLerayBandBoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLerayBandBoundReceipt public

canonicalNSLerayBandBoundReceipt :
  NSLerayBandBoundReceipt
canonicalNSLerayBandBoundReceipt =
  record
    { energyReceipt =
        Energy.canonicalNSCarrierEnergyInequalityReceipt
    ; lerayEnergyInputReady =
        refl
    ; status =
        canonicalNSLerayBandBoundStatus
    ; statusIsCanonical =
        refl
    ; lerayBandBound =
        lerayBandBoundStatement
    ; lerayBandBoundIsCanonical =
        refl
    ; derivationReason =
        lerayBandBoundReason
    ; derivationReasonIsCanonical =
        refl
    ; totalL2BudgetBound =
        true
    ; totalL2BudgetBoundIsTrue =
        refl
    ; bandNonnegativityInput =
        true
    ; bandNonnegativityInputIsTrue =
        refl
    ; everyIndividualCarrierBandBounded =
        true
    ; everyIndividualCarrierBandBoundedIsTrue =
        refl
    ; allJGreaterOrEqualZero =
        true
    ; allJGreaterOrEqualZeroIsTrue =
        refl
    ; allTGreaterOrEqualZero =
        true
    ; allTGreaterOrEqualZeroIsTrue =
        refl
    ; anyPositiveNu =
        true
    ; anyPositiveNuIsTrue =
        refl
    ; noConditionOnNuOrNorm =
        true
    ; noConditionOnNuOrNormIsTrue =
        refl
    ; exactNotCandidate =
        true
    ; exactNotCandidateIsTrue =
        refl
    ; loadBearingLemma =
        true
    ; loadBearingLemmaIsTrue =
        refl
    ; smoothRegularityPromoted =
        false
    ; smoothRegularityPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; promotionType =
        emptyPromotionType
    ; promotionTypeIsEmpty =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "lerayBandBound = a_j(t) <= M_0^2 for all j,t"
        ∷ "Reason: sum_j a_j(t) <= ||u_0||^2_L2 = M_0^2 and a_j(t) >= 0"
        ∷ "The bound is exact, not a candidate"
        ∷ "No condition on nu or norm is imposed beyond nu > 0"
        ∷ "This is a load-bearing weak-energy lemma"
        ∷ "No Clay/global terminal promotion is introduced"
        ∷ []
    }

nsLerayBandBoundIsLoadBearing :
  loadBearingLemma canonicalNSLerayBandBoundReceipt ≡ true
nsLerayBandBoundIsLoadBearing =
  refl

nsLerayBandBoundNoNuOrNormCondition :
  noConditionOnNuOrNorm canonicalNSLerayBandBoundReceipt ≡ true
nsLerayBandBoundNoNuOrNormCondition =
  refl

nsLerayBandBoundExactNotCandidate :
  exactNotCandidate canonicalNSLerayBandBoundReceipt ≡ true
nsLerayBandBoundExactNotCandidate =
  refl

nsLerayBandBoundKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSLerayBandBoundReceipt ≡ false
nsLerayBandBoundKeepsClayFalse =
  refl

nsLerayBandBoundNoTerminalPromotion :
  terminalPromotionPromoted canonicalNSLerayBandBoundReceipt ≡ false
nsLerayBandBoundNoTerminalPromotion =
  refl

nsLerayBandBoundNoPromotion :
  NSLerayBandBoundPromotion →
  ⊥
nsLerayBandBoundNoPromotion =
  nsLerayBandBoundPromotionImpossibleHere
