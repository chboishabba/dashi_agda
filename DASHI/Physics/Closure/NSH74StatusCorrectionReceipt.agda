module DASHI.Physics.Closure.NSH74StatusCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C5 NS H74 status correction receipt.
--
-- This receipt records the corrected carrier threshold only.  It does not
-- promote Clay Navier-Stokes, global regularity, or the old H^{7/4} route.

record FractionLabel : Set where
  constructor fraction
  field
    numerator :
      Nat

    denominator :
      Nat

open FractionLabel public

canonicalH11/8Threshold : FractionLabel
canonicalH11/8Threshold =
  fraction 11 8

canonicalH7/4Threshold : FractionLabel
canonicalH7/4Threshold =
  fraction 7 4

canonicalBernsteinExponent11/4 : FractionLabel
canonicalBernsteinExponent11/4 =
  fraction 11 4

data NSH74StatusCorrectionStatus : Set where
  h74SupersededByH11/8NoPromotion :
    NSH74StatusCorrectionStatus

data NSH74StatusCorrectionItem : Set where
  oldH74ThresholdSuperseded :
    NSH74StatusCorrectionItem

  optimalThresholdIsH11/8 :
    NSH74StatusCorrectionItem

  dyadicBaseP2CarrierStructure :
    NSH74StatusCorrectionItem

  bernsteinExponent11/4AtJ0 :
    NSH74StatusCorrectionItem

canonicalNSH74StatusCorrectionItems :
  List NSH74StatusCorrectionItem
canonicalNSH74StatusCorrectionItems =
  oldH74ThresholdSuperseded
  ∷ optimalThresholdIsH11/8
  ∷ dyadicBaseP2CarrierStructure
  ∷ bernsteinExponent11/4AtJ0
  ∷ []

nsOptimalThresholdStatement : String
nsOptimalThresholdStatement =
  "nsOptimalThreshold = 11/8 (not 7/4)"

h11/8OptimalDyadicCarrierStatement : String
h11/8OptimalDyadicCarrierStatement =
  "The H^11/8 threshold is optimal for the base-p=2 dyadic carrier structure from the Bernstein exponent 11/4 at j=0."

nsH74StatusCorrectionStatement : String
nsH74StatusCorrectionStatement =
  "NS H74 status correction: H^7/4 is superseded by H^11/8; nsOptimalThreshold = 11/8 (not 7/4); the H^11/8 threshold is optimal for the base-p=2 dyadic carrier structure from Bernstein exponent 11/4 at j=0; no promotion follows."

data NSH74StatusCorrectionPromotion : Set where

nsH74StatusCorrectionPromotionImpossibleHere :
  NSH74StatusCorrectionPromotion →
  ⊥
nsH74StatusCorrectionPromotionImpossibleHere ()

record NSH74StatusCorrectionReceipt : Setω where
  field
    status :
      NSH74StatusCorrectionStatus

    correctionItems :
      List NSH74StatusCorrectionItem

    correctionItemsAreCanonical :
      correctionItems ≡ canonicalNSH74StatusCorrectionItems

    supersededThreshold :
      FractionLabel

    supersededThresholdIsH7/4 :
      supersededThreshold ≡ canonicalH7/4Threshold

    nsOptimalThreshold :
      FractionLabel

    nsOptimalThresholdIs11/8 :
      nsOptimalThreshold ≡ canonicalH11/8Threshold

    nsOptimalThresholdNot7/4 :
      Bool

    nsOptimalThresholdNot7/4IsTrue :
      nsOptimalThresholdNot7/4 ≡ true

    nsOptimalThresholdLabel :
      String

    nsOptimalThresholdLabelIsCanonical :
      nsOptimalThresholdLabel ≡ nsOptimalThresholdStatement

    h74ThresholdSupersededBy118 :
      Bool

    h74ThresholdSupersededBy118IsTrue :
      h74ThresholdSupersededBy118 ≡ true

    basePrime :
      Nat

    basePrimeIsTwo :
      basePrime ≡ 2

    dyadicCarrierStructure :
      Bool

    dyadicCarrierStructureIsTrue :
      dyadicCarrierStructure ≡ true

    bernsteinExponent :
      FractionLabel

    bernsteinExponentIs11/4 :
      bernsteinExponent ≡ canonicalBernsteinExponent11/4

    bernsteinIndexJ :
      Nat

    bernsteinIndexJIsZero :
      bernsteinIndexJ ≡ zero

    h11/8OptimalForBaseP2DyadicCarrierStructure :
      Bool

    h11/8OptimalForBaseP2DyadicCarrierStructureIsTrue :
      h11/8OptimalForBaseP2DyadicCarrierStructure ≡ true

    optimalitySource :
      String

    optimalitySourceIsCanonical :
      optimalitySource ≡ h11/8OptimalDyadicCarrierStatement

    h74RoutePromoted :
      Bool

    h74RoutePromotedIsFalse :
      h74RoutePromoted ≡ false

    globalRegularityClaimed :
      Bool

    globalRegularityClaimedIsFalse :
      globalRegularityClaimed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List NSH74StatusCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsH74StatusCorrectionStatement

    receiptBoundary :
      List String

open NSH74StatusCorrectionReceipt public

canonicalNSH74StatusCorrectionReceipt :
  NSH74StatusCorrectionReceipt
canonicalNSH74StatusCorrectionReceipt =
  record
    { status =
        h74SupersededByH11/8NoPromotion
    ; correctionItems =
        canonicalNSH74StatusCorrectionItems
    ; correctionItemsAreCanonical =
        refl
    ; supersededThreshold =
        canonicalH7/4Threshold
    ; supersededThresholdIsH7/4 =
        refl
    ; nsOptimalThreshold =
        canonicalH11/8Threshold
    ; nsOptimalThresholdIs11/8 =
        refl
    ; nsOptimalThresholdNot7/4 =
        true
    ; nsOptimalThresholdNot7/4IsTrue =
        refl
    ; nsOptimalThresholdLabel =
        nsOptimalThresholdStatement
    ; nsOptimalThresholdLabelIsCanonical =
        refl
    ; h74ThresholdSupersededBy118 =
        true
    ; h74ThresholdSupersededBy118IsTrue =
        refl
    ; basePrime =
        2
    ; basePrimeIsTwo =
        refl
    ; dyadicCarrierStructure =
        true
    ; dyadicCarrierStructureIsTrue =
        refl
    ; bernsteinExponent =
        canonicalBernsteinExponent11/4
    ; bernsteinExponentIs11/4 =
        refl
    ; bernsteinIndexJ =
        zero
    ; bernsteinIndexJIsZero =
        refl
    ; h11/8OptimalForBaseP2DyadicCarrierStructure =
        true
    ; h11/8OptimalForBaseP2DyadicCarrierStructureIsTrue =
        refl
    ; optimalitySource =
        h11/8OptimalDyadicCarrierStatement
    ; optimalitySourceIsCanonical =
        refl
    ; h74RoutePromoted =
        false
    ; h74RoutePromotedIsFalse =
        refl
    ; globalRegularityClaimed =
        false
    ; globalRegularityClaimedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsH74StatusCorrectionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "H^7/4 is superseded by H^11/8"
        ∷ "nsOptimalThreshold = 11/8 (not 7/4)"
        ∷ "h74ThresholdSupersededBy118 = true"
        ∷ "H^11/8 is optimal for the base-p=2 dyadic carrier structure"
        ∷ "The optimality source is the Bernstein exponent 11/4 at j=0"
        ∷ "No H74 route, global regularity, Clay NS, or terminal promotion is asserted"
        ∷ []
    }

nsOptimalThresholdCanonical :
  nsOptimalThreshold canonicalNSH74StatusCorrectionReceipt
  ≡
  canonicalH11/8Threshold
nsOptimalThresholdCanonical =
  refl

h74ThresholdSupersededBy118True :
  h74ThresholdSupersededBy118 canonicalNSH74StatusCorrectionReceipt
  ≡
  true
h74ThresholdSupersededBy118True =
  refl

h11/8OptimalForDyadicCarrierTrue :
  h11/8OptimalForBaseP2DyadicCarrierStructure
    canonicalNSH74StatusCorrectionReceipt
  ≡
  true
h11/8OptimalForDyadicCarrierTrue =
  refl

nsH74StatusCorrectionNoClayPromotion :
  clayNavierStokesPromoted canonicalNSH74StatusCorrectionReceipt
  ≡
  false
nsH74StatusCorrectionNoClayPromotion =
  refl

nsH74StatusCorrectionNoPromotion :
  NSH74StatusCorrectionPromotion →
  ⊥
nsH74StatusCorrectionNoPromotion =
  nsH74StatusCorrectionPromotionImpossibleHere
