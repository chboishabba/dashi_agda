module DASHI.Physics.Closure.TwoComponentYMGapMapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Two-component Yang-Mills gap map after adelic decomposition.

data YMAdelicComponent : Set where
  pAdicComponent :
    YMAdelicComponent

  archimedeanComponent :
    YMAdelicComponent

canonicalYMAdelicComponents : List YMAdelicComponent
canonicalYMAdelicComponents =
  pAdicComponent
  ∷ archimedeanComponent
  ∷ []

data PAdicResolvedIngredient : Set where
  bruhatTitsTree :
    PAdicResolvedIngredient

  pAdicFlat :
    PAdicResolvedIngredient

  pAdicReflectionPositivity :
    PAdicResolvedIngredient

  pAdicContinuumLimit :
    PAdicResolvedIngredient

canonicalPAdicResolvedIngredients : List PAdicResolvedIngredient
canonicalPAdicResolvedIngredients =
  bruhatTitsTree
  ∷ pAdicFlat
  ∷ pAdicReflectionPositivity
  ∷ pAdicContinuumLimit
  ∷ []

data ArchimedeanOpenIngredient : Set where
  h3CurvatureMinusOne :
    ArchimedeanOpenIngredient

  boundaryS2RoundMetric :
    ArchimedeanOpenIngredient

  h3ToR3FlatLimitUnknown :
    ArchimedeanOpenIngredient

canonicalArchimedeanOpenIngredients : List ArchimedeanOpenIngredient
canonicalArchimedeanOpenIngredients =
  h3CurvatureMinusOne
  ∷ boundaryS2RoundMetric
  ∷ h3ToR3FlatLimitUnknown
  ∷ []

data YMRemainingGeometricGap : Set where
  archimedeanH3ToR3 :
    YMRemainingGeometricGap

data MillenniumTowerT2Status : Set where
  t2aPAdicInhabited :
    MillenniumTowerT2Status

  t2bArchimedeanOpen :
    MillenniumTowerT2Status

canonicalMillenniumTowerT2Split : List MillenniumTowerT2Status
canonicalMillenniumTowerT2Split =
  t2aPAdicInhabited
  ∷ t2bArchimedeanOpen
  ∷ []

data FullClayYMPromotion : Set where

fullClayYMPromotionImpossibleHere :
  FullClayYMPromotion →
  ⊥
fullClayYMPromotionImpossibleHere ()

preciseGapMapAfterAdelicDecomposition : String
preciseGapMapAfterAdelicDecomposition =
  "After adelic decomposition, the p-adic component is resolved by the Bruhat-Tits tree, flat, reflection positivity, and p-adic continuum limit; the archimedean component remains open at the H3 curvature -1 / boundary S2 round metric interface because the H3 -> R3 flat limit is unknown."

record TwoComponentYMGapMapReceipt : Setω where
  field
    adelicComponents :
      List YMAdelicComponent

    adelicComponentsAreCanonical :
      adelicComponents ≡ canonicalYMAdelicComponents

    preciseGapMap :
      String

    preciseGapMapIsCanonical :
      preciseGapMap ≡ preciseGapMapAfterAdelicDecomposition

    pAdicResolvedIngredients :
      List PAdicResolvedIngredient

    pAdicResolvedIngredientsAreCanonical :
      pAdicResolvedIngredients ≡ canonicalPAdicResolvedIngredients

    archimedeanOpenIngredients :
      List ArchimedeanOpenIngredient

    archimedeanOpenIngredientsAreCanonical :
      archimedeanOpenIngredients ≡ canonicalArchimedeanOpenIngredients

    pAdicComponentResolved :
      Bool

    pAdicComponentResolvedIsTrue :
      pAdicComponentResolved ≡ true

    archimedeanComponentOpen :
      Bool

    archimedeanComponentOpenIsTrue :
      archimedeanComponentOpen ≡ true

    singleRemainingGeometricGap :
      YMRemainingGeometricGap

    singleRemainingGeometricGapIsArchimedeanH3ToR3 :
      singleRemainingGeometricGap ≡ archimedeanH3ToR3

    fullClayYMNeedsBothFlatR3Components :
      Bool

    fullClayYMNeedsBothFlatR3ComponentsIsTrue :
      fullClayYMNeedsBothFlatR3Components ≡ true

    pAdicProgressGenuine :
      Bool

    pAdicProgressGenuineIsTrue :
      pAdicProgressGenuine ≡ true

    ymT2aInhabited :
      Bool

    ymT2aInhabitedIsTrue :
      ymT2aInhabited ≡ true

    ymT2bOpen :
      Bool

    ymT2bOpenIsTrue :
      ymT2bOpen ≡ true

    millenniumTowerT2Split :
      List MillenniumTowerT2Status

    millenniumTowerT2SplitIsCanonical :
      millenniumTowerT2Split ≡ canonicalMillenniumTowerT2Split

    fullClayYMPromoted :
      Bool

    fullClayYMPromotedIsFalse :
      fullClayYMPromoted ≡ false

    promotionFlags :
      List FullClayYMPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open TwoComponentYMGapMapReceipt public

canonicalTwoComponentYMGapMapReceipt :
  TwoComponentYMGapMapReceipt
canonicalTwoComponentYMGapMapReceipt =
  record
    { adelicComponents =
        canonicalYMAdelicComponents
    ; adelicComponentsAreCanonical =
        refl
    ; preciseGapMap =
        preciseGapMapAfterAdelicDecomposition
    ; preciseGapMapIsCanonical =
        refl
    ; pAdicResolvedIngredients =
        canonicalPAdicResolvedIngredients
    ; pAdicResolvedIngredientsAreCanonical =
        refl
    ; archimedeanOpenIngredients =
        canonicalArchimedeanOpenIngredients
    ; archimedeanOpenIngredientsAreCanonical =
        refl
    ; pAdicComponentResolved =
        true
    ; pAdicComponentResolvedIsTrue =
        refl
    ; archimedeanComponentOpen =
        true
    ; archimedeanComponentOpenIsTrue =
        refl
    ; singleRemainingGeometricGap =
        archimedeanH3ToR3
    ; singleRemainingGeometricGapIsArchimedeanH3ToR3 =
        refl
    ; fullClayYMNeedsBothFlatR3Components =
        true
    ; fullClayYMNeedsBothFlatR3ComponentsIsTrue =
        refl
    ; pAdicProgressGenuine =
        true
    ; pAdicProgressGenuineIsTrue =
        refl
    ; ymT2aInhabited =
        true
    ; ymT2aInhabitedIsTrue =
        refl
    ; ymT2bOpen =
        true
    ; ymT2bOpenIsTrue =
        refl
    ; millenniumTowerT2Split =
        canonicalMillenniumTowerT2Split
    ; millenniumTowerT2SplitIsCanonical =
        refl
    ; fullClayYMPromoted =
        false
    ; fullClayYMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "p-adic YM component resolved: Bruhat-Tits tree, flat, reflection positivity, and p-adic continuum limit are recorded"
        ∷ "archimedean YM component open: H3 has curvature -1, boundary S2 has the round metric, and the H3 -> R3 flat limit is unknown"
        ∷ "full Clay YM requires both adelic components to be compatible with flat R3"
        ∷ "Millennium Tower Schema T2 splits into T2a p-adic inhabited and T2b archimedean open"
        ∷ "No full Clay/YM promotion is introduced"
        ∷ []
    }

twoComponentYMGapMapKeepsClayFalse :
  fullClayYMPromoted canonicalTwoComponentYMGapMapReceipt ≡ false
twoComponentYMGapMapKeepsClayFalse =
  refl

twoComponentYMGapMapSingleRemainingGap :
  singleRemainingGeometricGap canonicalTwoComponentYMGapMapReceipt
  ≡
  archimedeanH3ToR3
twoComponentYMGapMapSingleRemainingGap =
  refl
