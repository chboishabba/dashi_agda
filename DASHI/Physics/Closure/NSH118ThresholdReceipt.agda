module DASHI.Physics.Closure.NSH118ThresholdReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Corrected Navier-Stokes H^{11/8} carrier threshold receipt.
--
-- This receipt supersedes the prior A3 reading that subcritical
-- dissipation was available for every positive Sobolev index.  The recorded
-- threshold is s = 11/8: below it only small-data closure is recorded; at
-- and above it large-data carrier closure is allowed, with a Gronwall
-- constant uniform in depth.  This is a carrier-threshold correction receipt
-- only and does not promote the Clay Navier-Stokes claim.

record PositiveRationalDatum : Set where
  constructor positiveRationalDatum
  field
    numerator :
      Nat

    denominator :
      Nat

open PositiveRationalDatum public

elevenEighths : PositiveRationalDatum
elevenEighths =
  positiveRationalDatum 11 8

nsCarrierThreshold : PositiveRationalDatum
nsCarrierThreshold =
  elevenEighths

data NSH118ThresholdStatus : Set where
  correctedThresholdRecorded :
    NSH118ThresholdStatus

  belowThresholdSmallDataOnly :
    NSH118ThresholdStatus

  atOrAboveThresholdLargeDataAllowed :
    NSH118ThresholdStatus

  gronwallUniformInDepthAtOrAboveThreshold :
    NSH118ThresholdStatus

  priorA3AnyPositiveSOverstated :
    NSH118ThresholdStatus

  correctedA3ScopeSAtLeastElevenEighths :
    NSH118ThresholdStatus

  noClayPromotion :
    NSH118ThresholdStatus

canonicalNSH118ThresholdStatus :
  List NSH118ThresholdStatus
canonicalNSH118ThresholdStatus =
  correctedThresholdRecorded
  ∷ belowThresholdSmallDataOnly
  ∷ atOrAboveThresholdLargeDataAllowed
  ∷ gronwallUniformInDepthAtOrAboveThreshold
  ∷ priorA3AnyPositiveSOverstated
  ∷ correctedA3ScopeSAtLeastElevenEighths
  ∷ noClayPromotion
  ∷ []

data NSH118SubcriticalScope : Set where
  belowH118SmallDataOnlyScope :
    NSH118SubcriticalScope

  atLeastH118LargeDataAllowedScope :
    NSH118SubcriticalScope

data NSH118A3Replacement : Set where
  subcriticalDissipationForH118AndAboveReplacement :
    NSH118A3Replacement

data NSH118ThresholdPromotion : Set where

nsH118ThresholdPromotionImpossibleHere :
  NSH118ThresholdPromotion →
  ⊥
nsH118ThresholdPromotionImpossibleHere ()

nsH118ThresholdStatement : String
nsH118ThresholdStatement =
  "Corrected NS carrier threshold: nsCarrierThreshold = 11/8; for s in (0, 11/8), only small-data closure is recorded; for s >= 11/8, large-data closure is allowed; the Gronwall constant is uniform in depth for s >= 11/8; prior A3 subcriticalDissipationForAnySPositive was overstated and is replaced by subcriticalDissipationForS>=11/8; nsA3CorrectionRequired = true; no Clay promotion follows."

record NSH118ThresholdReceipt : Setω where
  field
    status :
      List NSH118ThresholdStatus

    statusIsCanonical :
      status ≡ canonicalNSH118ThresholdStatus

    carrierThreshold :
      PositiveRationalDatum

    carrierThresholdIsElevenEighths :
      carrierThreshold ≡ nsCarrierThreshold

    nsCarrierThresholdNumeratorIs11 :
      numerator carrierThreshold ≡ 11

    nsCarrierThresholdDenominatorIs8 :
      denominator carrierThreshold ≡ 8

    belowThresholdScope :
      NSH118SubcriticalScope

    belowThresholdScopeIsSmallDataOnly :
      belowThresholdScope ≡ belowH118SmallDataOnlyScope

    sInOpenZeroElevenEighthsSmallDataOnly :
      Bool

    sInOpenZeroElevenEighthsSmallDataOnlyIsTrue :
      sInOpenZeroElevenEighthsSmallDataOnly ≡ true

    belowThresholdLargeDataAllowed :
      Bool

    belowThresholdLargeDataAllowedIsFalse :
      belowThresholdLargeDataAllowed ≡ false

    atOrAboveThresholdScope :
      NSH118SubcriticalScope

    atOrAboveThresholdScopeIsLargeDataAllowed :
      atOrAboveThresholdScope ≡ atLeastH118LargeDataAllowedScope

    sAtLeastElevenEighthsLargeDataAllowed :
      Bool

    sAtLeastElevenEighthsLargeDataAllowedIsTrue :
      sAtLeastElevenEighthsLargeDataAllowed ≡ true

    gronwallConstantUniformInDepthForS>=11/8 :
      Bool

    gronwallConstantUniformInDepthForS>=11/8IsTrue :
      gronwallConstantUniformInDepthForS>=11/8 ≡ true

    priorA3SubcriticalDissipationForAnySPositiveOverstated :
      Bool

    priorA3SubcriticalDissipationForAnySPositiveOverstatedIsTrue :
      priorA3SubcriticalDissipationForAnySPositiveOverstated ≡ true

    subcriticalDissipationForAnySPositiveRetired :
      Bool

    subcriticalDissipationForAnySPositiveRetiredIsTrue :
      subcriticalDissipationForAnySPositiveRetired ≡ true

    a3Replacement :
      NSH118A3Replacement

    a3ReplacementIsSubcriticalDissipationForS>=11/8 :
      a3Replacement ≡ subcriticalDissipationForH118AndAboveReplacement

    subcriticalDissipationForS>=11/8 :
      Bool

    subcriticalDissipationForS>=11/8IsTrue :
      subcriticalDissipationForS>=11/8 ≡ true

    nsA3CorrectionRequired :
      Bool

    nsA3CorrectionRequiredIsTrue :
      nsA3CorrectionRequired ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsH118ThresholdStatement

    promotionFlags :
      List NSH118ThresholdPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSH118ThresholdReceipt public

canonicalNSH118ThresholdReceipt :
  NSH118ThresholdReceipt
canonicalNSH118ThresholdReceipt =
  record
    { status =
        canonicalNSH118ThresholdStatus
    ; statusIsCanonical =
        refl
    ; carrierThreshold =
        nsCarrierThreshold
    ; carrierThresholdIsElevenEighths =
        refl
    ; nsCarrierThresholdNumeratorIs11 =
        refl
    ; nsCarrierThresholdDenominatorIs8 =
        refl
    ; belowThresholdScope =
        belowH118SmallDataOnlyScope
    ; belowThresholdScopeIsSmallDataOnly =
        refl
    ; sInOpenZeroElevenEighthsSmallDataOnly =
        true
    ; sInOpenZeroElevenEighthsSmallDataOnlyIsTrue =
        refl
    ; belowThresholdLargeDataAllowed =
        false
    ; belowThresholdLargeDataAllowedIsFalse =
        refl
    ; atOrAboveThresholdScope =
        atLeastH118LargeDataAllowedScope
    ; atOrAboveThresholdScopeIsLargeDataAllowed =
        refl
    ; sAtLeastElevenEighthsLargeDataAllowed =
        true
    ; sAtLeastElevenEighthsLargeDataAllowedIsTrue =
        refl
    ; gronwallConstantUniformInDepthForS>=11/8 =
        true
    ; gronwallConstantUniformInDepthForS>=11/8IsTrue =
        refl
    ; priorA3SubcriticalDissipationForAnySPositiveOverstated =
        true
    ; priorA3SubcriticalDissipationForAnySPositiveOverstatedIsTrue =
        refl
    ; subcriticalDissipationForAnySPositiveRetired =
        true
    ; subcriticalDissipationForAnySPositiveRetiredIsTrue =
        refl
    ; a3Replacement =
        subcriticalDissipationForH118AndAboveReplacement
    ; a3ReplacementIsSubcriticalDissipationForS>=11/8 =
        refl
    ; subcriticalDissipationForS>=11/8 =
        true
    ; subcriticalDissipationForS>=11/8IsTrue =
        refl
    ; nsA3CorrectionRequired =
        true
    ; nsA3CorrectionRequiredIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; statement =
        nsH118ThresholdStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "nsCarrierThreshold = 11/8"
        ∷ "For s in (0, 11/8), small-data only"
        ∷ "For s >= 11/8, large-data allowed"
        ∷ "Gronwall constant uniform in depth for s >= 11/8"
        ∷ "Prior A3 subcriticalDissipationForAnySPositive was overstated"
        ∷ "Conceptual replacement: subcriticalDissipationForS>=11/8"
        ∷ "nsA3CorrectionRequired = true"
        ∷ "Clay/global regularity promotion flags remain false"
        ∷ []
    }

nsCarrierThresholdIs11Over8 :
  nsCarrierThreshold ≡ positiveRationalDatum 11 8
nsCarrierThresholdIs11Over8 =
  refl

nsBelowH118SmallDataOnly :
  sInOpenZeroElevenEighthsSmallDataOnly canonicalNSH118ThresholdReceipt
  ≡
  true
nsBelowH118SmallDataOnly =
  refl

nsBelowH118LargeDataNotAllowed :
  belowThresholdLargeDataAllowed canonicalNSH118ThresholdReceipt
  ≡
  false
nsBelowH118LargeDataNotAllowed =
  refl

nsAtOrAboveH118LargeDataAllowed :
  sAtLeastElevenEighthsLargeDataAllowed canonicalNSH118ThresholdReceipt
  ≡
  true
nsAtOrAboveH118LargeDataAllowed =
  refl

nsGronwallUniformInDepthAtOrAboveH118 :
  gronwallConstantUniformInDepthForS>=11/8 canonicalNSH118ThresholdReceipt
  ≡
  true
nsGronwallUniformInDepthAtOrAboveH118 =
  refl

nsSubcriticalDissipationForS>=11/8Recorded :
  subcriticalDissipationForS>=11/8 canonicalNSH118ThresholdReceipt
  ≡
  true
nsSubcriticalDissipationForS>=11/8Recorded =
  refl

nsA3CorrectionRequiredIsSet :
  nsA3CorrectionRequired canonicalNSH118ThresholdReceipt
  ≡
  true
nsA3CorrectionRequiredIsSet =
  refl

nsH118ThresholdDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSH118ThresholdReceipt ≡ false
nsH118ThresholdDoesNotPromoteClay =
  refl

nsH118ThresholdDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSH118ThresholdReceipt ≡ false
nsH118ThresholdDoesNotPromoteGlobalRegularity =
  refl

nsH118ThresholdNoPromotion :
  NSH118ThresholdPromotion →
  ⊥
nsH118ThresholdNoPromotion =
  nsH118ThresholdPromotionImpossibleHere
