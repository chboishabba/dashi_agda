module DASHI.Arithmetic.WeightedPressure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_≤_; _*_)
open import Data.Nat.Properties as NatP using (+-mono-≤; *-mono-≤)

open import MonsterOntos using
  ( SSP
  ; toNat
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  ; gammaAt
  )
open import DASHI.Arithmetic.TrackedSupport using
  ( supportAt
  ; deltaAt≤supportAt
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15
  )

------------------------------------------------------------------------
-- Weighted quantities over the tracked 15-prime carrier.
--
-- The weight is a simple Nat proxy for prime size. This keeps the layer
-- constructive and lets the new inequality live on top of the landed
-- unweighted support bound.

weight : SSP → Nat
weight = toNat

weightedDeltaAt : SSP → Int → Int → Nat
weightedDeltaAt p x y = weight p * deltaAt p x y

weightedSupportAt : SSP → Int → Int → Nat
weightedSupportAt p x y = weight p * supportAt p x y

weightedDelta15 : Int → Int → Vec15 Nat
weightedDelta15 x y =
  mkVec15
    (weightedDeltaAt p2 x y) (weightedDeltaAt p3 x y) (weightedDeltaAt p5 x y) (weightedDeltaAt p7 x y)
    (weightedDeltaAt p11 x y) (weightedDeltaAt p13 x y) (weightedDeltaAt p17 x y) (weightedDeltaAt p19 x y)
    (weightedDeltaAt p23 x y) (weightedDeltaAt p29 x y) (weightedDeltaAt p31 x y) (weightedDeltaAt p41 x y)
    (weightedDeltaAt p47 x y) (weightedDeltaAt p59 x y) (weightedDeltaAt p71 x y)

weightedSupport15 : Int → Int → Vec15 Nat
weightedSupport15 x y =
  mkVec15
    (weightedSupportAt p2 x y) (weightedSupportAt p3 x y) (weightedSupportAt p5 x y) (weightedSupportAt p7 x y)
    (weightedSupportAt p11 x y) (weightedSupportAt p13 x y) (weightedSupportAt p17 x y) (weightedSupportAt p19 x y)
    (weightedSupportAt p23 x y) (weightedSupportAt p29 x y) (weightedSupportAt p31 x y) (weightedSupportAt p41 x y)
    (weightedSupportAt p47 x y) (weightedSupportAt p59 x y) (weightedSupportAt p71 x y)

weightedPressure : Int → Int → Nat
weightedPressure x y = sum15 (weightedDelta15 x y)

weightedSupport : Int → Int → Nat
weightedSupport x y = sum15 (weightedSupport15 x y)

------------------------------------------------------------------------
-- Local weighted bound.
--
-- This is the only place where multiplication monotonicity is needed.

weightedLocalBound :
  ∀ p x y →
  weightedDeltaAt p x y ≤ weightedSupportAt p x y
weightedLocalBound p x y =
  NatP.*-monoʳ-≤ (weight p) (deltaAt≤supportAt p x y)

------------------------------------------------------------------------
-- Lift the local bound across the 15 tracked primes.

weightedSum15≤ :
  ∀ a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71
    b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71 →
  a2 ≤ b2 →
  a3 ≤ b3 →
  a5 ≤ b5 →
  a7 ≤ b7 →
  a11 ≤ b11 →
  a13 ≤ b13 →
  a17 ≤ b17 →
  a19 ≤ b19 →
  a23 ≤ b23 →
  a29 ≤ b29 →
  a31 ≤ b31 →
  a41 ≤ b41 →
  a47 ≤ b47 →
  a59 ≤ b59 →
  a71 ≤ b71 →
  sum15
    (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71)
    ≤
  sum15
    (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71)
weightedSum15≤ a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71
               b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71
               a2≤b2 a3≤b3 a5≤b5 a7≤b7 a11≤b11 a13≤b13 a17≤b17 a19≤b19
               a23≤b23 a29≤b29 a31≤b31 a41≤b41 a47≤b47 a59≤b59 a71≤b71 =
  step15
  where
    step2  = +-mono-≤ a2≤b2 a3≤b3
    step3  = +-mono-≤ step2 a5≤b5
    step4  = +-mono-≤ step3 a7≤b7
    step5  = +-mono-≤ step4 a11≤b11
    step6  = +-mono-≤ step5 a13≤b13
    step7  = +-mono-≤ step6 a17≤b17
    step8  = +-mono-≤ step7 a19≤b19
    step9  = +-mono-≤ step8 a23≤b23
    step10 = +-mono-≤ step9 a29≤b29
    step11 = +-mono-≤ step10 a31≤b31
    step12 = +-mono-≤ step11 a41≤b41
    step13 = +-mono-≤ step12 a47≤b47
    step14 = +-mono-≤ step13 a59≤b59
    step15 = +-mono-≤ step14 a71≤b71

------------------------------------------------------------------------
-- Global weighted inequality.

weightedPressure≤weightedSupport :
  ∀ x y →
  weightedPressure x y ≤ weightedSupport x y
weightedPressure≤weightedSupport x y =
  weightedSum15≤
    (weightedDeltaAt p2 x y) (weightedDeltaAt p3 x y) (weightedDeltaAt p5 x y) (weightedDeltaAt p7 x y)
    (weightedDeltaAt p11 x y) (weightedDeltaAt p13 x y) (weightedDeltaAt p17 x y) (weightedDeltaAt p19 x y)
    (weightedDeltaAt p23 x y) (weightedDeltaAt p29 x y) (weightedDeltaAt p31 x y) (weightedDeltaAt p41 x y)
    (weightedDeltaAt p47 x y) (weightedDeltaAt p59 x y) (weightedDeltaAt p71 x y)
    (weightedSupportAt p2 x y) (weightedSupportAt p3 x y) (weightedSupportAt p5 x y) (weightedSupportAt p7 x y)
    (weightedSupportAt p11 x y) (weightedSupportAt p13 x y) (weightedSupportAt p17 x y) (weightedSupportAt p19 x y)
    (weightedSupportAt p23 x y) (weightedSupportAt p29 x y) (weightedSupportAt p31 x y) (weightedSupportAt p41 x y)
    (weightedSupportAt p47 x y) (weightedSupportAt p59 x y) (weightedSupportAt p71 x y)
    (weightedLocalBound p2 x y)
    (weightedLocalBound p3 x y)
    (weightedLocalBound p5 x y)
    (weightedLocalBound p7 x y)
    (weightedLocalBound p11 x y)
    (weightedLocalBound p13 x y)
    (weightedLocalBound p17 x y)
    (weightedLocalBound p19 x y)
    (weightedLocalBound p23 x y)
    (weightedLocalBound p29 x y)
    (weightedLocalBound p31 x y)
    (weightedLocalBound p41 x y)
    (weightedLocalBound p47 x y)
    (weightedLocalBound p59 x y)
    (weightedLocalBound p71 x y)

record WeightedPressureStructure : Set₁ where
  field
    localWeight : SSP → Int → Int → Nat
    globalWeight : Int → Int → Nat
    localBound :
      ∀ p x y →
      weightedDeltaAt p x y ≤ weightedSupportAt p x y
    globalBound :
      ∀ x y →
      weightedPressure x y ≤ weightedSupport x y

open WeightedPressureStructure public

weightedPressureStructure : WeightedPressureStructure
weightedPressureStructure = record
  { localWeight = weightedDeltaAt
  ; globalWeight = weightedPressure
  ; localBound = weightedLocalBound
  ; globalBound = weightedPressure≤weightedSupport
  }
