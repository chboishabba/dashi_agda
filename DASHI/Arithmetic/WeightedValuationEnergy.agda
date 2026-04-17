module DASHI.Arithmetic.WeightedValuationEnergy where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Integer using (ℤ; +_)

open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  ; mapTrackedPrimes15
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (Vec15 to Vec15R)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; vp
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15
  )

------------------------------------------------------------------------
-- Weighted valuation helper surface for future Φ / Q₊ integration.
--
-- This layer is purely arithmetic and constructive. It does not assert any
-- bridge theorem to the quadratic core.

ArithmeticPair : Set
ArithmeticPair = Int × Int

left : ArithmeticPair → Int
left = proj₁

right : ArithmeticPair → Int
right = proj₂

weight : SSP → Nat
weight = toNat

square : Nat → Nat
square n = n * n

valuationAt : SSP → Int → Nat
valuationAt p n = vp (toNat p) n

valuation15 : Int → Vec15 Nat
valuation15 n = mapTrackedPrimes15 (λ p → valuationAt p n)

valuationPair15 : ArithmeticPair → Vec15 Nat × Vec15 Nat
valuationPair15 s = valuation15 (left s) , valuation15 (right s)

weightedValuationAt : SSP → Int → Nat
weightedValuationAt p n = weight p * valuationAt p n

weightedQuadraticAt : SSP → Int → Nat
weightedQuadraticAt p n = weight p * square (valuationAt p n)

weightedValuation15 : Int → Vec15 Nat
weightedValuation15 n = mapTrackedPrimes15 (λ p → weightedValuationAt p n)

weightedQuadratic15 : Int → Vec15 Nat
weightedQuadratic15 n = mapTrackedPrimes15 (λ p → weightedQuadraticAt p n)

weightedValuationEnergy : Int → Nat
weightedValuationEnergy n = sum15 (weightedValuation15 n)

weightedQuadraticEnergy : Int → Nat
weightedQuadraticEnergy n = sum15 (weightedQuadratic15 n)

liftVec15NatToVecℤ : Vec15 Nat → Vec ℤ 15
liftVec15NatToVecℤ v =
  + (Vec15R.e2 v) ∷ + (Vec15R.e3 v) ∷ + (Vec15R.e5 v) ∷ + (Vec15R.e7 v) ∷
  + (Vec15R.e11 v) ∷ + (Vec15R.e13 v) ∷ + (Vec15R.e17 v) ∷ + (Vec15R.e19 v) ∷
  + (Vec15R.e23 v) ∷ + (Vec15R.e29 v) ∷ + (Vec15R.e31 v) ∷ + (Vec15R.e41 v) ∷
  + (Vec15R.e47 v) ∷ + (Vec15R.e59 v) ∷ + (Vec15R.e71 v) ∷ []

valuationVecℤ : Int → Vec ℤ 15
valuationVecℤ n = liftVec15NatToVecℤ (valuation15 n)

weightedValuationVecℤ : Int → Vec ℤ 15
weightedValuationVecℤ n = liftVec15NatToVecℤ (weightedValuation15 n)

weightedQuadraticVecℤ : Int → Vec ℤ 15
weightedQuadraticVecℤ n = liftVec15NatToVecℤ (weightedQuadratic15 n)

record WeightedValuationEnergySurface : Set₁ where
  field
    Carrier : Set
    valuationLane : SSP → Carrier → Nat
    valuationCarrier15 : Carrier → Vec15 Nat
    weightedValuationLane : SSP → Carrier → Nat
    weightedQuadraticLane : SSP → Carrier → Nat
    weightedLinearEnergy : Carrier → Nat
    weightedQuadraticEnergyNat : Carrier → Nat
    valuationCarrierVecℤ : Carrier → Vec ℤ 15
    weightedValuationCarrierVecℤ : Carrier → Vec ℤ 15
    weightedQuadraticCarrierVecℤ : Carrier → Vec ℤ 15

weightedValuationEnergySurface : WeightedValuationEnergySurface
weightedValuationEnergySurface = record
  { Carrier = Int
  ; valuationLane = valuationAt
  ; valuationCarrier15 = valuation15
  ; weightedValuationLane = weightedValuationAt
  ; weightedQuadraticLane = weightedQuadraticAt
  ; weightedLinearEnergy = weightedValuationEnergy
  ; weightedQuadraticEnergyNat = weightedQuadraticEnergy
  ; valuationCarrierVecℤ = valuationVecℤ
  ; weightedValuationCarrierVecℤ = weightedValuationVecℤ
  ; weightedQuadraticCarrierVecℤ = weightedQuadraticVecℤ
  }
