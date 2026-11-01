module DASHI.Arithmetic.MaxPressure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; _⊔_; s≤s)
open import Data.Nat.Properties as NatP using (⊔-lub; +-comm; +-assoc; +-identityʳ; +-mono-≤; ≤-refl; ≤-reflexive; ≤-trans; m≤m+n)
open import Relation.Binary.PropositionalEquality using (sym)

open import MonsterOntos using
  ( p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Statistics.Vec15Descriptive using
  ( PrimeCarrier15
  ; max15
  ; sum15
  ; maxNat
  )

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; delta15
  )
open import DASHI.Arithmetic.GlobalPressure using
  ( totalPressure
  )
open import DASHI.Arithmetic.TrackedSupport using
  ( trackedSupport
  ; totalPressure≤trackedSupport
  )
open import DASHI.Arithmetic.WeightedPressure using
  ( weightedDelta15
  ; weightedPressure
  ; weightedPressure≤weightedSupport
  ; weightedSupport
  )

------------------------------------------------------------------------
-- A generic Nat bound for the two-way max.

maxNat≤sum :
  ∀ a b →
  maxNat a b ≤ a + b
maxNat≤sum zero b = ≤-refl
maxNat≤sum (suc a) zero rewrite +-identityʳ (suc a) = ≤-refl
maxNat≤sum (suc a) (suc b) =
  ≤-trans
    (s≤s (maxNat≤⊔ a b))
    (⊔≤+ (suc a) (suc b))
  where
    maxNat≤⊔ :
      ∀ a b →
      maxNat a b ≤ a ⊔ b
    maxNat≤⊔ zero b = ≤-refl
    maxNat≤⊔ (suc a) zero = ≤-refl
    maxNat≤⊔ (suc a) (suc b) = s≤s (maxNat≤⊔ a b)

    ⊔≤+ :
      ∀ a b →
      a ⊔ b ≤ a + b
    ⊔≤+ a b =
      ⊔-lub
        (m≤m+n a b)
        (≤-trans (m≤m+n b a) (NatP.≤-reflexive (NatP.+-comm b a)))

------------------------------------------------------------------------
-- The tracked 15-lane max is always bounded by the tracked 15-lane sum.

max15≤sum15 :
  ∀ v →
  max15 v ≤ sum15 v
max15≤sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  ≤-trans
    (maxNat≤sum a2 m14)
    ( ≤-trans
        (NatP.+-mono-≤ NatP.≤-refl step14)
        sum15-right-nested )
  where
    m2 : Nat
    m2 = maxNat a59 a71

    m3 : Nat
    m3 = maxNat a47 m2

    m4 : Nat
    m4 = maxNat a41 m3

    m5 : Nat
    m5 = maxNat a31 m4

    m6 : Nat
    m6 = maxNat a29 m5

    m7 : Nat
    m7 = maxNat a23 m6

    m8 : Nat
    m8 = maxNat a19 m7

    m9 : Nat
    m9 = maxNat a17 m8

    m10 : Nat
    m10 = maxNat a13 m9

    m11 : Nat
    m11 = maxNat a11 m10

    m12 : Nat
    m12 = maxNat a7 m11

    m13 : Nat
    m13 = maxNat a5 m12

    m14 : Nat
    m14 = maxNat a3 m13

    s2 : Nat
    s2 = a59 + a71

    s3 : Nat
    s3 = a47 + s2

    s4 : Nat
    s4 = a41 + s3

    s5 : Nat
    s5 = a31 + s4

    s6 : Nat
    s6 = a29 + s5

    s7 : Nat
    s7 = a23 + s6

    s8 : Nat
    s8 = a19 + s7

    s9 : Nat
    s9 = a17 + s8

    s10 : Nat
    s10 = a13 + s9

    s11 : Nat
    s11 = a11 + s10

    s12 : Nat
    s12 = a7 + s11

    s13 : Nat
    s13 = a5 + s12

    s14 : Nat
    s14 = a3 + s13

    step2 :
      m2 ≤ s2
    step2 = maxNat≤sum a59 a71

    step3 :
      m3 ≤ s3
    step3 =
      ≤-trans
        (maxNat≤sum a47 m2)
        ( +-mono-≤ ≤-refl step2 )

    step4 :
      m4 ≤ s4
    step4 =
      ≤-trans
        (maxNat≤sum a41 m3)
        ( +-mono-≤ ≤-refl step3 )

    step5 :
      m5 ≤ s5
    step5 =
      ≤-trans
        (maxNat≤sum a31 m4)
        ( +-mono-≤ ≤-refl step4 )

    step6 :
      m6 ≤ s6
    step6 =
      ≤-trans
        (maxNat≤sum a29 m5)
        ( +-mono-≤ ≤-refl step5 )

    step7 :
      m7 ≤ s7
    step7 =
      ≤-trans
        (maxNat≤sum a23 m6)
        ( +-mono-≤ ≤-refl step6 )

    step8 :
      m8 ≤ s8
    step8 =
      ≤-trans
        (maxNat≤sum a19 m7)
        ( +-mono-≤ ≤-refl step7 )

    step9 :
      m9 ≤ s9
    step9 =
      ≤-trans
        (maxNat≤sum a17 m8)
        ( +-mono-≤ ≤-refl step8 )

    step10 :
      m10 ≤ s10
    step10 =
      ≤-trans
        (maxNat≤sum a13 m9)
        ( +-mono-≤ ≤-refl step9 )

    step11 :
      m11 ≤ s11
    step11 =
      ≤-trans
        (maxNat≤sum a11 m10)
        ( +-mono-≤ ≤-refl step10 )

    step12 :
      m12 ≤ s12
    step12 =
      ≤-trans
        (maxNat≤sum a7 m11)
        ( +-mono-≤ ≤-refl step11 )

    step13 :
      m13 ≤ s13
    step13 =
      ≤-trans
        (maxNat≤sum a5 m12)
        ( +-mono-≤ ≤-refl step12 )

    step14 :
      m14 ≤ s14
    step14 =
      ≤-trans
        (maxNat≤sum a3 m13)
        ( +-mono-≤ ≤-refl step13 )

    sum15-right-nested :
      a2 + s14 ≤
      sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71)
    sum15-right-nested
      rewrite sym (NatP.+-assoc a2 a3 s13)
            | sym (NatP.+-assoc (a2 + a3) a5 s12)
            | sym (NatP.+-assoc ((a2 + a3) + a5) a7 s11)
            | sym (NatP.+-assoc (((a2 + a3) + a5) + a7) a11 s10)
            | sym (NatP.+-assoc ((((a2 + a3) + a5) + a7) + a11) a13 s9)
            | sym (NatP.+-assoc (((((a2 + a3) + a5) + a7) + a11) + a13) a17 s8)
            | sym (NatP.+-assoc ((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) a19 s7)
            | sym (NatP.+-assoc (((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) a23 s6)
            | sym (NatP.+-assoc ((((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) + a23) a29 s5)
            | sym (NatP.+-assoc (((((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) + a23) + a29) a31 s4)
            | sym (NatP.+-assoc ((((((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) + a23) + a29) + a31) a41 s3)
            | sym (NatP.+-assoc (((((((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) + a23) + a29) + a31) + a41) a47 s2)
            | sym (NatP.+-assoc ((((((((((((a2 + a3) + a5) + a7) + a11) + a13) + a17) + a19) + a23) + a29) + a31) + a41) + a47) a59 a71)
      = NatP.≤-refl

------------------------------------------------------------------------
-- Pressure maxima for the current arithmetic carriers.

maxPressure : Int → Int → Nat
maxPressure x y = max15 (delta15 x y)

weightedMaxPressure : Int → Int → Nat
weightedMaxPressure x y = max15 (weightedDelta15 x y)

maxPressure≤totalPressure :
  ∀ x y →
  maxPressure x y ≤ totalPressure x y
maxPressure≤totalPressure x y =
  max15≤sum15 (delta15 x y)

weightedMaxPressure≤weightedPressure :
  ∀ x y →
  weightedMaxPressure x y ≤ weightedPressure x y
weightedMaxPressure≤weightedPressure x y =
  max15≤sum15 (weightedDelta15 x y)

weightedMaxPressure≤weightedSupport :
  ∀ x y →
  weightedMaxPressure x y ≤ weightedSupport x y
weightedMaxPressure≤weightedSupport x y =
  NatP.≤-trans
    (weightedMaxPressure≤weightedPressure x y)
    (weightedPressure≤weightedSupport x y)

maxPressure≤trackedSupport :
  ∀ x y →
  maxPressure x y ≤ trackedSupport x y
maxPressure≤trackedSupport x y =
  NatP.≤-trans
    (maxPressure≤totalPressure x y)
    (totalPressure≤trackedSupport x y)

record MaxPressureStructure : Set₁ where
  field
    maxPressureAt : Int → Int → Nat
    weightedMaxPressureAt : Int → Int → Nat
    maxBound :
      ∀ x y →
      maxPressureAt x y ≤ totalPressure x y
    weightedMaxBound :
      ∀ x y →
      weightedMaxPressureAt x y ≤ weightedPressure x y
    weightedSupportBound :
      ∀ x y →
      weightedMaxPressureAt x y ≤ weightedSupport x y
    supportBound :
      ∀ x y →
      maxPressureAt x y ≤ trackedSupport x y

open MaxPressureStructure public

maxPressureStructure : MaxPressureStructure
maxPressureStructure = record
  { maxPressureAt = maxPressure
  ; weightedMaxPressureAt = weightedMaxPressure
  ; maxBound = maxPressure≤totalPressure
  ; weightedMaxBound = weightedMaxPressure≤weightedPressure
  ; weightedSupportBound = weightedMaxPressure≤weightedSupport
  ; supportBound = maxPressure≤trackedSupport
  }
