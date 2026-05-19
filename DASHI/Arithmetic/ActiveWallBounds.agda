module DASHI.Arithmetic.ActiveWallBounds where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using
  ( *-identityˡ
  ; +-mono-≤
  ; ≤-refl
  ; ≤-trans
  )

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  )
open import DASHI.Arithmetic.GlobalPressure using
  ( totalPressure
  )
open import DASHI.Arithmetic.ActiveWallStructure using
  ( activeWallMaskAt
  )
open import DASHI.Arithmetic.MaxPressure using
  ( maxPressure
  )
open import DASHI.Arithmetic.TrackedSupport using
  ( sum15≤
  )
open import DASHI.Statistics.Vec15Descriptive using
  ( maxNat
  ; countNonZeroNat
  ; sum15
  )

------------------------------------------------------------------------
-- Active-wall scaling bounds.
--
-- The key carrier fact is:
--   each local delta is bounded by the tracked max,
--   and becomes zero when its nonzero-indicator is zero.
--
-- Summing this pointwise bound yields:
--   totalPressure ≤ Σ_p (1_{δ_p>0} * maxPressure)
--
-- This is the strongest honest bound available without adding a separate
-- multiplicative algebra layer for rewriting that scaled sum into
-- `activeWallCount * maxPressure`.

maxNat-left-≤ :
  ∀ a b →
  a ≤ maxNat a b
maxNat-left-≤ zero b = z≤n
maxNat-left-≤ (suc a) zero = ≤-refl
maxNat-left-≤ (suc a) (suc b) = s≤s (maxNat-left-≤ a b)

maxNat-right-≤ :
  ∀ a b →
  b ≤ maxNat a b
maxNat-right-≤ zero b = ≤-refl
maxNat-right-≤ (suc a) zero = z≤n
maxNat-right-≤ (suc a) (suc b) = s≤s (maxNat-right-≤ a b)

delta2≤maxPressure :
  ∀ x y →
  deltaAt p2 x y ≤ maxPressure x y
delta2≤maxPressure x y = maxNat-left-≤ (deltaAt p2 x y) _

tail59 : Int → Int → Nat
tail59 x y = maxNat (deltaAt p59 x y) (deltaAt p71 x y)

tail47 : Int → Int → Nat
tail47 x y = maxNat (deltaAt p47 x y) (tail59 x y)

tail41 : Int → Int → Nat
tail41 x y = maxNat (deltaAt p41 x y) (tail47 x y)

tail31 : Int → Int → Nat
tail31 x y = maxNat (deltaAt p31 x y) (tail41 x y)

tail29 : Int → Int → Nat
tail29 x y = maxNat (deltaAt p29 x y) (tail31 x y)

tail23 : Int → Int → Nat
tail23 x y = maxNat (deltaAt p23 x y) (tail29 x y)

tail19 : Int → Int → Nat
tail19 x y = maxNat (deltaAt p19 x y) (tail23 x y)

tail17 : Int → Int → Nat
tail17 x y = maxNat (deltaAt p17 x y) (tail19 x y)

tail13 : Int → Int → Nat
tail13 x y = maxNat (deltaAt p13 x y) (tail17 x y)

tail11 : Int → Int → Nat
tail11 x y = maxNat (deltaAt p11 x y) (tail13 x y)

tail7 : Int → Int → Nat
tail7 x y = maxNat (deltaAt p7 x y) (tail11 x y)

tail5 : Int → Int → Nat
tail5 x y = maxNat (deltaAt p5 x y) (tail7 x y)

tail3 : Int → Int → Nat
tail3 x y = maxNat (deltaAt p3 x y) (tail5 x y)

tail59≤maxPressure :
  ∀ x y →
  tail59 x y ≤ maxPressure x y
tail59≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p47 x y) (tail59 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p41 x y) (tail47 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p31 x y) (tail41 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p29 x y) (tail31 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p23 x y) (tail29 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
                (≤-trans
                  (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
                  (≤-trans
                    (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
                    (≤-trans
                      (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
                      (≤-trans
                        (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
                        (≤-trans
                          (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                          (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))))))))))))

tail47≤maxPressure :
  ∀ x y →
  tail47 x y ≤ maxPressure x y
tail47≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p41 x y) (tail47 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p31 x y) (tail41 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p29 x y) (tail31 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p23 x y) (tail29 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
                (≤-trans
                  (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
                  (≤-trans
                    (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
                    (≤-trans
                      (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
                      (≤-trans
                        (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                        (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))))))))))))

tail41≤maxPressure :
  ∀ x y →
  tail41 x y ≤ maxPressure x y
tail41≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p31 x y) (tail41 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p29 x y) (tail31 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p23 x y) (tail29 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
                (≤-trans
                  (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
                  (≤-trans
                    (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
                    (≤-trans
                      (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                      (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))))))))))

tail31≤maxPressure :
  ∀ x y →
  tail31 x y ≤ maxPressure x y
tail31≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p29 x y) (tail31 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p23 x y) (tail29 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
                (≤-trans
                  (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
                  (≤-trans
                    (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                    (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))))))))))

tail29≤maxPressure :
  ∀ x y →
  tail29 x y ≤ maxPressure x y
tail29≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p23 x y) (tail29 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
                (≤-trans
                  (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                  (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))))))))

tail23≤maxPressure :
  ∀ x y →
  tail23 x y ≤ maxPressure x y
tail23≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p19 x y) (tail23 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
              (≤-trans
                (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
                (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))))))))

tail19≤maxPressure :
  ∀ x y →
  tail19 x y ≤ maxPressure x y
tail19≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p17 x y) (tail19 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
            (≤-trans
              (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
              (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))))))

tail17≤maxPressure :
  ∀ x y →
  tail17 x y ≤ maxPressure x y
tail17≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p13 x y) (tail17 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
          (≤-trans
            (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
            (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))))))

tail13≤maxPressure :
  ∀ x y →
  tail13 x y ≤ maxPressure x y
tail13≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p11 x y) (tail13 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
        (≤-trans
          (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
          (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))))

tail11≤maxPressure :
  ∀ x y →
  tail11 x y ≤ maxPressure x y
tail11≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p7 x y) (tail11 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
      (≤-trans
        (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
        (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))))

tail7≤maxPressure :
  ∀ x y →
  tail7 x y ≤ maxPressure x y
tail7≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p5 x y) (tail7 x y))
    (≤-trans
      (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
      (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y)))

tail5≤maxPressure :
  ∀ x y →
  tail5 x y ≤ maxPressure x y
tail5≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p3 x y) (tail5 x y))
    (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))

delta3≤maxPressure :
  ∀ x y →
  deltaAt p3 x y ≤ maxPressure x y
delta3≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p3 x y) (tail5 x y))
    (maxNat-right-≤ (deltaAt p2 x y) (tail3 x y))

delta5≤maxPressure :
  ∀ x y →
  deltaAt p5 x y ≤ maxPressure x y
delta5≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p5 x y) (tail7 x y))
    (tail5≤maxPressure x y)

delta7≤maxPressure :
  ∀ x y →
  deltaAt p7 x y ≤ maxPressure x y
delta7≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p7 x y) (tail11 x y))
    (tail7≤maxPressure x y)

delta11≤maxPressure :
  ∀ x y →
  deltaAt p11 x y ≤ maxPressure x y
delta11≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p11 x y) (tail13 x y))
    (tail11≤maxPressure x y)

delta13≤maxPressure :
  ∀ x y →
  deltaAt p13 x y ≤ maxPressure x y
delta13≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p13 x y) (tail17 x y))
    (tail13≤maxPressure x y)

delta17≤maxPressure :
  ∀ x y →
  deltaAt p17 x y ≤ maxPressure x y
delta17≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p17 x y) (tail19 x y))
    (tail17≤maxPressure x y)

delta19≤maxPressure :
  ∀ x y →
  deltaAt p19 x y ≤ maxPressure x y
delta19≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p19 x y) (tail23 x y))
    (tail19≤maxPressure x y)

delta23≤maxPressure :
  ∀ x y →
  deltaAt p23 x y ≤ maxPressure x y
delta23≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p23 x y) (tail29 x y))
    (tail23≤maxPressure x y)

delta29≤maxPressure :
  ∀ x y →
  deltaAt p29 x y ≤ maxPressure x y
delta29≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p29 x y) (tail31 x y))
    (tail29≤maxPressure x y)

delta31≤maxPressure :
  ∀ x y →
  deltaAt p31 x y ≤ maxPressure x y
delta31≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p31 x y) (tail41 x y))
    (tail31≤maxPressure x y)

delta41≤maxPressure :
  ∀ x y →
  deltaAt p41 x y ≤ maxPressure x y
delta41≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p41 x y) (tail47 x y))
    (tail41≤maxPressure x y)

delta47≤maxPressure :
  ∀ x y →
  deltaAt p47 x y ≤ maxPressure x y
delta47≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p47 x y) (tail59 x y))
    (tail47≤maxPressure x y)

delta59≤maxPressure :
  ∀ x y →
  deltaAt p59 x y ≤ maxPressure x y
delta59≤maxPressure x y =
  ≤-trans
    (maxNat-left-≤ (deltaAt p59 x y) (deltaAt p71 x y))
    (tail59≤maxPressure x y)

delta71≤maxPressure :
  ∀ x y →
  deltaAt p71 x y ≤ maxPressure x y
delta71≤maxPressure x y =
  ≤-trans
    (maxNat-right-≤ (deltaAt p59 x y) (deltaAt p71 x y))
    (tail59≤maxPressure x y)

nonZeroScaleUpper :
  ∀ a m →
  a ≤ m →
  a ≤ countNonZeroNat a * m
nonZeroScaleUpper zero m a≤m = z≤n
nonZeroScaleUpper (suc a) m a≤m
  rewrite NatP.*-identityˡ m
  = a≤m

activeWallScaledAt : SSP → Int → Int → Nat
activeWallScaledAt p x y = activeWallMaskAt p x y * maxPressure x y

activeWallScaled15 : Int → Int → Vec15 Nat
activeWallScaled15 x y =
  mkVec15
    (activeWallScaledAt p2 x y) (activeWallScaledAt p3 x y) (activeWallScaledAt p5 x y) (activeWallScaledAt p7 x y)
    (activeWallScaledAt p11 x y) (activeWallScaledAt p13 x y) (activeWallScaledAt p17 x y) (activeWallScaledAt p19 x y)
    (activeWallScaledAt p23 x y) (activeWallScaledAt p29 x y) (activeWallScaledAt p31 x y) (activeWallScaledAt p41 x y)
    (activeWallScaledAt p47 x y) (activeWallScaledAt p59 x y) (activeWallScaledAt p71 x y)

activeWallScaledPressure : Int → Int → Nat
activeWallScaledPressure x y = sum15 (activeWallScaled15 x y)

deltaAt≤activeWallScaledAt :
  ∀ p x y →
  deltaAt p x y ≤ activeWallScaledAt p x y
deltaAt≤activeWallScaledAt p x y with p
... | p2 = nonZeroScaleUpper (deltaAt p2 x y) (maxPressure x y) (delta2≤maxPressure x y)
... | p3 = nonZeroScaleUpper (deltaAt p3 x y) (maxPressure x y) (delta3≤maxPressure x y)
... | p5 = nonZeroScaleUpper (deltaAt p5 x y) (maxPressure x y) (delta5≤maxPressure x y)
... | p7 = nonZeroScaleUpper (deltaAt p7 x y) (maxPressure x y) (delta7≤maxPressure x y)
... | p11 = nonZeroScaleUpper (deltaAt p11 x y) (maxPressure x y) (delta11≤maxPressure x y)
... | p13 = nonZeroScaleUpper (deltaAt p13 x y) (maxPressure x y) (delta13≤maxPressure x y)
... | p17 = nonZeroScaleUpper (deltaAt p17 x y) (maxPressure x y) (delta17≤maxPressure x y)
... | p19 = nonZeroScaleUpper (deltaAt p19 x y) (maxPressure x y) (delta19≤maxPressure x y)
... | p23 = nonZeroScaleUpper (deltaAt p23 x y) (maxPressure x y) (delta23≤maxPressure x y)
... | p29 = nonZeroScaleUpper (deltaAt p29 x y) (maxPressure x y) (delta29≤maxPressure x y)
... | p31 = nonZeroScaleUpper (deltaAt p31 x y) (maxPressure x y) (delta31≤maxPressure x y)
... | p41 = nonZeroScaleUpper (deltaAt p41 x y) (maxPressure x y) (delta41≤maxPressure x y)
... | p47 = nonZeroScaleUpper (deltaAt p47 x y) (maxPressure x y) (delta47≤maxPressure x y)
... | p59 = nonZeroScaleUpper (deltaAt p59 x y) (maxPressure x y) (delta59≤maxPressure x y)
... | p71 = nonZeroScaleUpper (deltaAt p71 x y) (maxPressure x y) (delta71≤maxPressure x y)

totalPressure≤activeWallScaledPressure :
  ∀ x y →
  totalPressure x y ≤ activeWallScaledPressure x y
totalPressure≤activeWallScaledPressure x y =
  sum15≤
    (deltaAt p2 x y) (deltaAt p3 x y) (deltaAt p5 x y) (deltaAt p7 x y)
    (deltaAt p11 x y) (deltaAt p13 x y) (deltaAt p17 x y) (deltaAt p19 x y)
    (deltaAt p23 x y) (deltaAt p29 x y) (deltaAt p31 x y) (deltaAt p41 x y)
    (deltaAt p47 x y) (deltaAt p59 x y) (deltaAt p71 x y)
    (activeWallScaledAt p2 x y) (activeWallScaledAt p3 x y) (activeWallScaledAt p5 x y) (activeWallScaledAt p7 x y)
    (activeWallScaledAt p11 x y) (activeWallScaledAt p13 x y) (activeWallScaledAt p17 x y) (activeWallScaledAt p19 x y)
    (activeWallScaledAt p23 x y) (activeWallScaledAt p29 x y) (activeWallScaledAt p31 x y) (activeWallScaledAt p41 x y)
    (activeWallScaledAt p47 x y) (activeWallScaledAt p59 x y) (activeWallScaledAt p71 x y)
    (deltaAt≤activeWallScaledAt p2 x y)
    (deltaAt≤activeWallScaledAt p3 x y)
    (deltaAt≤activeWallScaledAt p5 x y)
    (deltaAt≤activeWallScaledAt p7 x y)
    (deltaAt≤activeWallScaledAt p11 x y)
    (deltaAt≤activeWallScaledAt p13 x y)
    (deltaAt≤activeWallScaledAt p17 x y)
    (deltaAt≤activeWallScaledAt p19 x y)
    (deltaAt≤activeWallScaledAt p23 x y)
    (deltaAt≤activeWallScaledAt p29 x y)
    (deltaAt≤activeWallScaledAt p31 x y)
    (deltaAt≤activeWallScaledAt p41 x y)
    (deltaAt≤activeWallScaledAt p47 x y)
    (deltaAt≤activeWallScaledAt p59 x y)
    (deltaAt≤activeWallScaledAt p71 x y)

record ActiveWallBoundStructure : Set₁ where
  field
    scaledPressure : Int → Int → Nat
    activeWallBound :
      ∀ x y →
      totalPressure x y ≤ scaledPressure x y

open ActiveWallBoundStructure public

activeWallBoundStructure : ActiveWallBoundStructure
activeWallBoundStructure = record
  { scaledPressure = activeWallScaledPressure
  ; activeWallBound = totalPressure≤activeWallScaledPressure
  }
