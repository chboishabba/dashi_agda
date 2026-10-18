module DASHI.Moonshine.OggSSP2BPureKleinFourThreeTateFibreExact where

------------------------------------------------------------------------
-- THREE 2B TATE FIBRES FROM A 2B-PURE KLEIN FOUR
--
-- Let V4 = {1,a,b,ab} be a Klein four whose three nonidentity elements are
-- Monster class 2B.  The sourced local normalizer quotient contains an S3
-- factor.  Its natural role is to permute the three nonidentity elements,
-- hence to transport among the three corresponding cyclic C2 Tate theories.
--
-- This gives a source-native interpretation of the repo's regular-C3
-- "3 x Completion10" step:
--
--   one selected Q10 in each of the three conjugate 2B Tate fibres
--   -> 3 x 10 = 30 states.
--
-- Crucial distinction:
-- the C3 does NOT need to act nontrivially inside one fixed bare duad/Tate
-- carrier.  It may instead cycle three same-shaped Tate fibres.
--
-- This file records that architecture and its arithmetic, but does not
-- construct the actual transport maps on Moonshine Tate cohomology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BPureKleinFourM24S3LocalRouteExact as Local
import DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact as P279

------------------------------------------------------------------------
-- 1. Three nonidentity elements / Tate fibres.
------------------------------------------------------------------------

data TwoBElementOfPureKlein : Set where
  twoB-a twoB-b twoB-ab : TwoBElementOfPureKlein

twoBElementCount : Nat
twoBElementCount = 3

twoBElementCountIsThree : twoBElementCount ≡ 3
twoBElementCountIsThree = refl

data TateFibre : TwoBElementOfPureKlein → Set where
  fibre-token : {x : TwoBElementOfPureKlein} → TateFibre x

------------------------------------------------------------------------
-- 2. C3 cycle on the three 2B elements.
------------------------------------------------------------------------

cycleTwoB : TwoBElementOfPureKlein → TwoBElementOfPureKlein
cycleTwoB twoB-a = twoB-b
cycleTwoB twoB-b = twoB-ab
cycleTwoB twoB-ab = twoB-a

cycleTwoBCubed :
  (x : TwoBElementOfPureKlein) →
  cycleTwoB (cycleTwoB (cycleTwoB x)) ≡ x
cycleTwoBCubed twoB-a = refl
cycleTwoBCubed twoB-b = refl
cycleTwoBCubed twoB-ab = refl

cycleTwoBHasNoFixedPoint :
  (x : TwoBElementOfPureKlein) →
  cycleTwoB x ≡ x → ⊥
cycleTwoBHasNoFixedPoint twoB-a ()
cycleTwoBHasNoFixedPoint twoB-b ()
cycleTwoBHasNoFixedPoint twoB-ab ()

------------------------------------------------------------------------
-- 3. Completion10 selected in each fibre gives thirty.
------------------------------------------------------------------------

completionTenPerFibre : Nat
completionTenPerFibre = P279.completionTen

threeFibreCompletionCount : Nat
threeFibreCompletionCount = twoBElementCount * completionTenPerFibre

threeFibreCompletionCountIsThirty :
  threeFibreCompletionCount ≡ 30
threeFibreCompletionCountIsThirty = refl

pointedThreeFibreCompletionIsP31 :
  1 + threeFibreCompletionCount ≡ P279.p31Value
pointedThreeFibreCompletionIsP31 = refl

nonaryPointedThreeFibreCompletionIs279 :
  P279.nonaryScale * (1 + threeFibreCompletionCount) ≡ 279
nonaryPointedThreeFibreCompletionIs279 = refl

------------------------------------------------------------------------
-- 4. Actual transport receipt required from the Monster-local action.
------------------------------------------------------------------------

record ActualThreeTateFibreTransport
    (FibreObject : TwoBElementOfPureKlein → Set) : Set₁ where
  field
    transport :
      (x : TwoBElementOfPureKlein) →
      FibreObject x →
      FibreObject (cycleTwoB x)

    transportCubed :
      (x : TwoBElementOfPureKlein) →
      (v : FibreObject x) →
      Set

    inducedBySourcedLocalC3 : Bool

open ActualThreeTateFibreTransport public

------------------------------------------------------------------------
-- 5. Selected Q10 family and same-object C3 recognition target.
------------------------------------------------------------------------

record SelectedCompletionTenFamily
    (FibreObject : TwoBElementOfPureKlein → Set) : Set₁ where
  field
    selectedQ10 : (x : TwoBElementOfPureKlein) → Set
    embedSelected :
      (x : TwoBElementOfPureKlein) →
      selectedQ10 x →
      FibreObject x

    selectedCardinality : (x : TwoBElementOfPureKlein) → Nat
    selectedCardinalityIsTen :
      (x : TwoBElementOfPureKlein) →
      selectedCardinality x ≡ 10

open SelectedCompletionTenFamily public

record ThreeFibreCompletionRecognition
    (FibreObject : TwoBElementOfPureKlein → Set)
    (T : ActualThreeTateFibreTransport FibreObject)
    (Q : SelectedCompletionTenFamily FibreObject) : Set₁ where
  field
    transportPreservesSelectedFamily : Set
    sameObjectC3CycleOnSelectedQ10 : Set
    completion10ChartInEachFibre : Set
    totalSelectedCountIsThirty :
      twoBElementCount * 10 ≡ 30

open ThreeFibreCompletionRecognition public

------------------------------------------------------------------------
-- 6. Firewalls.
------------------------------------------------------------------------

data S3OnNormalizerAutomaticallyActsInsideOneFixedTateFibre : Set where
data ThreeEqualDimensionsConstructTransport : Set where
data ThirtyArithmeticConstructsP31SameObject : Set where

s3NormalizerDoesNotAutomaticallyActInsideFixedFibre :
  S3OnNormalizerAutomaticallyActsInsideOneFixedTateFibre → ⊥
s3NormalizerDoesNotAutomaticallyActInsideFixedFibre ()

equalDimensionsDoNotConstructTransport :
  ThreeEqualDimensionsConstructTransport → ⊥
equalDimensionsDoNotConstructTransport ()

thirtyArithmeticDoesNotConstructP31SameObject :
  ThirtyArithmeticConstructsP31SameObject → ⊥
thirtyArithmeticDoesNotConstructP31SameObject ()

------------------------------------------------------------------------
-- 7. Frontier status.
------------------------------------------------------------------------

record ThreeTateFibreFrontier : Set where
  constructor three-tate-fibre-frontier
  field
    pureKleinFourSourced : Bool
    s3FactorSourced : Bool
    threeNonidentity2BElements : Bool
    c3CycleCarrierConstructed : Bool
    completionTenPerFibreArithmetic : Bool
    thirtyPointedToP31Arithmetic : Bool
    actualTateTransportConstructed : Bool
    actualSelectedQ10FamilyConstructed : Bool
    sameObjectC3RecognitionPaid : Bool
    nextResidual : String

canonicalThreeTateFibreFrontier : ThreeTateFibreFrontier
canonicalThreeTateFibreFrontier =
  three-tate-fibre-frontier
    true true true true true true
    false false false
    "construct the actual Monster-local transport among Tate cohomologies of the three nontrivial elements of the 2B-pure Klein four; then show the selected 10d M22/Completion10 subquotient is preserved cyclically"

