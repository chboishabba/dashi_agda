module DASHI.Arithmetic.TrackedSupport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using
  (+-mono-≤; m∸n≤m)

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; alphaAt
  ; betaAt
  ; gammaAt
  ; gamma15
  ; gammaSum
  ; deltaAt
  ; delta15
  ; deltaAt-decomposition
  )
open import DASHI.Arithmetic.GlobalPressure using
  ( totalPressure )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15 )
open import DASHI.Arithmetic.VpDepth using
  ( minNat )

------------------------------------------------------------------------
-- First tracked support proxy.
--
-- The support proxy stays conservative and fully constructive at the
-- current arithmetic layer: a local contribution is bounded by its output
-- valuation depth, and the global support score is the corresponding 15-lane
-- gamma sum.

supportAt : SSP → Int → Int → Nat
supportAt = gammaAt

support15 : Int → Int → Vec15 Nat
support15 = gamma15

trackedSupport : Int → Int → Nat
trackedSupport = gammaSum

------------------------------------------------------------------------
-- Local bound: the local cancellation lift is always bounded by the output
-- valuation depth.

deltaAt≤supportAt :
  ∀ p x y →
  deltaAt p x y ≤ supportAt p x y
deltaAt≤supportAt p x y
  rewrite deltaAt-decomposition p x y
  = m∸n≤m (gammaAt p x y) (minNat (alphaAt p x y) (betaAt p x y))

------------------------------------------------------------------------
-- Componentwise monotonicity over the tracked 15-lane carrier.

sum15≤ :
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
sum15≤ a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71
       b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71
       a2≤b2 a3≤b3 a5≤b5 a7≤b7 a11≤b11 a13≤b13 a17≤b17 a19≤b19
       a23≤b23 a29≤b29 a31≤b31 a41≤b41 a47≤b47 a59≤b59 a71≤b71 =
  step15
  where
    step2 = +-mono-≤ a2≤b2 a3≤b3
    step3 = +-mono-≤ step2 a5≤b5
    step4 = +-mono-≤ step3 a7≤b7
    step5 = +-mono-≤ step4 a11≤b11
    step6 = +-mono-≤ step5 a13≤b13
    step7 = +-mono-≤ step6 a17≤b17
    step8 = +-mono-≤ step7 a19≤b19
    step9 = +-mono-≤ step8 a23≤b23
    step10 = +-mono-≤ step9 a29≤b29
    step11 = +-mono-≤ step10 a31≤b31
    step12 = +-mono-≤ step11 a41≤b41
    step13 = +-mono-≤ step12 a47≤b47
    step14 = +-mono-≤ step13 a59≤b59
    step15 = +-mono-≤ step14 a71≤b71

------------------------------------------------------------------------
-- Global tracked bound.

totalPressure≤trackedSupport :
  ∀ x y →
  totalPressure x y ≤ trackedSupport x y
totalPressure≤trackedSupport x y =
  sum15≤
    (deltaAt p2 x y) (deltaAt p3 x y) (deltaAt p5 x y) (deltaAt p7 x y)
    (deltaAt p11 x y) (deltaAt p13 x y) (deltaAt p17 x y) (deltaAt p19 x y)
    (deltaAt p23 x y) (deltaAt p29 x y) (deltaAt p31 x y) (deltaAt p41 x y)
    (deltaAt p47 x y) (deltaAt p59 x y) (deltaAt p71 x y)
    (supportAt p2 x y) (supportAt p3 x y) (supportAt p5 x y) (supportAt p7 x y)
    (supportAt p11 x y) (supportAt p13 x y) (supportAt p17 x y) (supportAt p19 x y)
    (supportAt p23 x y) (supportAt p29 x y) (supportAt p31 x y) (supportAt p41 x y)
    (supportAt p47 x y) (supportAt p59 x y) (supportAt p71 x y)
    (deltaAt≤supportAt p2 x y)
    (deltaAt≤supportAt p3 x y)
    (deltaAt≤supportAt p5 x y)
    (deltaAt≤supportAt p7 x y)
    (deltaAt≤supportAt p11 x y)
    (deltaAt≤supportAt p13 x y)
    (deltaAt≤supportAt p17 x y)
    (deltaAt≤supportAt p19 x y)
    (deltaAt≤supportAt p23 x y)
    (deltaAt≤supportAt p29 x y)
    (deltaAt≤supportAt p31 x y)
    (deltaAt≤supportAt p41 x y)
    (deltaAt≤supportAt p47 x y)
    (deltaAt≤supportAt p59 x y)
    (deltaAt≤supportAt p71 x y)

record TrackedSupportStructure : Set₁ where
  field
    localSupport : SSP → Int → Int → Nat
    globalSupport : Int → Int → Nat
    localBound :
      ∀ p x y →
      deltaAt p x y ≤ localSupport p x y
    globalBound :
      ∀ x y →
      totalPressure x y ≤ globalSupport x y

open TrackedSupportStructure public

trackedSupportStructure : TrackedSupportStructure
trackedSupportStructure = record
  { localSupport = supportAt
  ; globalSupport = trackedSupport
  ; localBound = deltaAt≤supportAt
  ; globalBound = totalPressure≤trackedSupport
  }
