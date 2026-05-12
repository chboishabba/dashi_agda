module DASHI.Algebra.Trit.HalfTrit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- DASHI-internal half-trit carrier.
--
-- The existing Trit API is exactly neg / zer / pos.  HalfTrit refines this
-- into five signed half-step coordinates, but the forgetful map back to Trit
-- necessarily collapses negOne with negHalf and posHalf with posOne.

data HalfTrit : Set where
  negOne :
    HalfTrit
  negHalf :
    HalfTrit
  zero :
    HalfTrit
  posHalf :
    HalfTrit
  posOne :
    HalfTrit

embedTrit :
  HalfTrit →
  Trit.Trit
embedTrit negOne =
  Trit.neg
embedTrit negHalf =
  Trit.neg
embedTrit zero =
  Trit.zer
embedTrit posHalf =
  Trit.pos
embedTrit posOne =
  Trit.pos

invHalfTrit :
  HalfTrit →
  HalfTrit
invHalfTrit negOne =
  posOne
invHalfTrit negHalf =
  posHalf
invHalfTrit zero =
  zero
invHalfTrit posHalf =
  negHalf
invHalfTrit posOne =
  negOne

invHalfTrit-invol :
  (x : HalfTrit) →
  invHalfTrit (invHalfTrit x) ≡ x
invHalfTrit-invol negOne = refl
invHalfTrit-invol negHalf = refl
invHalfTrit-invol zero = refl
invHalfTrit-invol posHalf = refl
invHalfTrit-invol posOne = refl

embedTrit-negOne-collapses-with-negHalf :
  embedTrit negOne ≡ embedTrit negHalf
embedTrit-negOne-collapses-with-negHalf = refl

embedTrit-posHalf-collapses-with-posOne :
  embedTrit posHalf ≡ embedTrit posOne
embedTrit-posHalf-collapses-with-posOne = refl

data HalfTritConstructionStatus : Set where
  halfTritCarrierConstructedEmbedNonInjective :
    HalfTritConstructionStatus

data HalfTritDuplicateFreedomStatus : Set where
  duplicateFreedomAvailableOnHalfTritCarrierOnly :
    HalfTritDuplicateFreedomStatus
  duplicateFreedomObstructedForEmbedTrit :
    HalfTritDuplicateFreedomStatus

data HalfTritResidualObligation : Set where
  e8EightCoordinateCarrierStillMissing :
    HalfTritResidualObligation
  e8RootEqualityDecisionStillMissing :
    HalfTritResidualObligation
  e8RootEnumeratorStillMissing :
    HalfTritResidualObligation
  e8DuplicateFreedomNotDerivableFromEmbedTrit :
    HalfTritResidualObligation
  e8CompletenessStillMissing :
    HalfTritResidualObligation

canonicalHalfTritResidualObligations :
  List HalfTritResidualObligation
canonicalHalfTritResidualObligations =
  e8EightCoordinateCarrierStillMissing
  ∷ e8RootEqualityDecisionStillMissing
  ∷ e8RootEnumeratorStillMissing
  ∷ e8DuplicateFreedomNotDerivableFromEmbedTrit
  ∷ e8CompletenessStillMissing
  ∷ []

record HalfTritComplete : Setω where
  field
    status :
      HalfTritConstructionStatus

    carrier :
      Set

    negativeOne :
      carrier

    negativeHalf :
      carrier

    neutral :
      carrier

    positiveHalf :
      carrier

    positiveOne :
      carrier

    tritCarrier :
      Set

    tritNegative :
      tritCarrier

    tritZero :
      tritCarrier

    tritPositive :
      tritCarrier

    forgetfulMap :
      carrier →
      tritCarrier

    inverse :
      carrier →
      carrier

    inverseInvolutive :
      (x : carrier) →
      inverse (inverse x) ≡ x

    negativeCollapseWitness :
      forgetfulMap negativeOne ≡ forgetfulMap negativeHalf

    positiveCollapseWitness :
      forgetfulMap positiveHalf ≡ forgetfulMap positiveOne

    embedDuplicateFreedom :
      HalfTritDuplicateFreedomStatus

    residualObligations :
      List HalfTritResidualObligation

    residualObligationsAreCanonical :
      residualObligations ≡ canonicalHalfTritResidualObligations

    constructsE8RootEnumeration :
      Bool

    constructsPromotionClaim :
      Bool

    noPromotionBoundary :
      List String

canonicalHalfTritComplete :
  HalfTritComplete
canonicalHalfTritComplete =
  record
    { status =
        halfTritCarrierConstructedEmbedNonInjective
    ; carrier =
        HalfTrit
    ; negativeOne =
        negOne
    ; negativeHalf =
        negHalf
    ; neutral =
        zero
    ; positiveHalf =
        posHalf
    ; positiveOne =
        posOne
    ; tritCarrier =
        Trit.Trit
    ; tritNegative =
        Trit.neg
    ; tritZero =
        Trit.zer
    ; tritPositive =
        Trit.pos
    ; forgetfulMap =
        embedTrit
    ; inverse =
        invHalfTrit
    ; inverseInvolutive =
        invHalfTrit-invol
    ; negativeCollapseWitness =
        embedTrit-negOne-collapses-with-negHalf
    ; positiveCollapseWitness =
        embedTrit-posHalf-collapses-with-posOne
    ; embedDuplicateFreedom =
        duplicateFreedomObstructedForEmbedTrit
    ; residualObligations =
        canonicalHalfTritResidualObligations
    ; residualObligationsAreCanonical =
        refl
    ; constructsE8RootEnumeration =
        false
    ; constructsPromotionClaim =
        false
    ; noPromotionBoundary =
        "HalfTrit is an internal five-point carrier construction only"
        ∷ "The forgetful embedTrit map intentionally collapses negOne/negHalf and posHalf/posOne"
        ∷ "Duplicate freedom for E8 roots cannot be derived from embedTrit"
        ∷ "No E8 root enumeration, empirical promotion, or physics promotion is claimed here"
        ∷ []
    }

halfTritConstructed :
  HalfTritConstructionStatus
halfTritConstructed =
  halfTritCarrierConstructedEmbedNonInjective

halfTritDoesNotConstructE8RootEnumeration :
  HalfTritComplete.constructsE8RootEnumeration canonicalHalfTritComplete
  ≡
  false
halfTritDoesNotConstructE8RootEnumeration = refl

halfTritDoesNotPromote :
  HalfTritComplete.constructsPromotionClaim canonicalHalfTritComplete
  ≡
  false
halfTritDoesNotPromote = refl

data EmbedTritInjective : Set where

embedTritInjectiveObstructed :
  EmbedTritInjective →
  ⊥
embedTritInjectiveObstructed ()
