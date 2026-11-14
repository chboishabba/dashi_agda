module DASHI.Analysis.BishopSetoidWeldExact where

------------------------------------------------------------------------
-- SOURCE-FAITHFUL SETOID WELD AND RATIONAL-IRRATIONAL TRANSPORT.
--
-- Source owners:
-- Geuvers--Niqui (2002) rational-Cauchy completion categoricity;
-- Bishop--Bridges; Zachary Murray (2022); Viktor Csimma Bishop library.
-- Existing DASHI instances:
-- BishopFastCauchyRealEquivalenceExact,
-- BishopFastCauchyCommonCompletionExact,
-- BishopFastCauchyCategoricityInstanceExact.
--
-- DASHI contribution: discharge rationality/irrationality transport
-- and finite existential witness transport FROM a genuinely supplied
-- setoid equivalence and rational embedding agreement.
--
-- This does NOT manufacture the missing rational-reindexing/canonical
-- categoricity instance or a cross-kernel Lean-to-Agda theorem.
-- Reindexing Bishop reciprocal-natural vs Fast dyadic moduli generally
-- is NOT a definitional identity of sequence terms.
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

record RationalSetoidWeld
    (Left Right : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    equivalence : Spine.SetoidRealEquivalence Left Right
    Rational : Set
    leftEmbed : Rational → Spine.Carrier Left
    rightEmbed : Rational → Spine.Carrier Right

    -- The one actual source-level identification required from rational
    -- approximation/reindexing. No synthetic equality of Real TYPES.
    rationalAgreement : (q : Rational) →
      Spine._≈_ Right
        (Spine.map (Spine.toRight equivalence) (leftEmbed q))
        (rightEmbed q)

open RationalSetoidWeld public

module _ {Left Right : Spine.SetoidOrderedCompleteReal}
         (W : RationalSetoidWeld Left Right) where

  toRightValue : Spine.Carrier Left → Spine.Carrier Right
  toRightValue = Spine.map (Spine.toRight (equivalence W))

  toLeftValue : Spine.Carrier Right → Spine.Carrier Left
  toLeftValue = Spine.map (Spine.toLeft (equivalence W))

  rightOfLeftRoundTrip : (x : Spine.Carrier Left) →
    Spine._≈_ Left (toLeftValue (toRightValue x)) x
  rightOfLeftRoundTrip = Spine.leftRoundTrip (equivalence W)

  leftOfRightRoundTrip : (y : Spine.Carrier Right) →
    Spine._≈_ Right (toRightValue (toLeftValue y)) y
  leftOfRightRoundTrip = Spine.rightRoundTrip (equivalence W)

  rationalAgreementBackwards : (q : Rational W) →
    Spine._≈_ Left (toLeftValue (rightEmbed W q)) (leftEmbed W q)
  rationalAgreementBackwards q =
    Spine.≈-trans Left
      (Spine.respectsEquality (Spine.toLeft (equivalence W))
        (Spine.≈-sym Right (rationalAgreement W q)))
      (rightOfLeftRoundTrip (leftEmbed W q))

  RationalLeft : Spine.Carrier Left → Set
  RationalLeft x =
    Σ (Rational W) (λ q → Spine._≈_ Left x (leftEmbed W q))

  RationalRight : Spine.Carrier Right → Set
  RationalRight y =
    Σ (Rational W) (λ q → Spine._≈_ Right y (rightEmbed W q))

  IrrationalLeft : Spine.Carrier Left → Set
  IrrationalLeft x = RationalLeft x → ⊥

  IrrationalRight : Spine.Carrier Right → Set
  IrrationalRight y = RationalRight y → ⊥

  rationalLeftToRight : (x : Spine.Carrier Left) →
    RationalLeft x → RationalRight (toRightValue x)
  rationalLeftToRight x (q , eq) =
    q ,
      Spine.≈-trans Right
        (Spine.respectsEquality (Spine.toRight (equivalence W)) eq)
        (rationalAgreement W q)

  rationalRightToLeft : (x : Spine.Carrier Left) →
    RationalRight (toRightValue x) → RationalLeft x
  rationalRightToLeft x (q , eq) =
    q ,
      Spine.≈-trans Left
        (Spine.≈-sym Left (rightOfLeftRoundTrip x))
        (Spine.≈-trans Left
          (Spine.respectsEquality (Spine.toLeft (equivalence W)) eq)
          (rationalAgreementBackwards q))

  irrationalLeftToRight : (x : Spine.Carrier Left) →
    IrrationalLeft x → IrrationalRight (toRightValue x)
  irrationalLeftToRight x notRational rational =
    notRational (rationalRightToLeft x rational)

  irrationalRightToLeft : (x : Spine.Carrier Left) →
    IrrationalRight (toRightValue x) → IrrationalLeft x
  irrationalRightToLeft x notRational rational =
    notRational (rationalLeftToRight x rational)

  irrationalRightCongruent : {x y : Spine.Carrier Right} →
    Spine._≈_ Right x y → IrrationalRight x → IrrationalRight y
  irrationalRightCongruent eq notRational (q , rational) =
    notRational
      (q , Spine.≈-trans Right eq rational)

  -- Same-object finite (or infinite) existential transport.
  -- Only the supplied comparison of ACTUAL selected values can
  -- identify a source analytic function with the target function.
  existentialIrrationalityTransport :
    (Index : Set)
    (source : Index → Spine.Carrier Left)
    (target : Index → Spine.Carrier Right) →
    ((i : Index) → Spine._≈_ Right
      (toRightValue (source i)) (target i)) →
    Σ Index (λ i → IrrationalLeft (source i)) →
    Σ Index (λ i → IrrationalRight (target i))
  existentialIrrationalityTransport Index source target sameValue
      (i , irrational) =
    i , irrationalRightCongruent
      (sameValue i)
      (irrationalLeftToRight (source i) irrational)
