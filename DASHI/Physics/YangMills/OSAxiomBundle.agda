module DASHI.Physics.YangMills.OSAxiomBundle where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Physics.Closure.OSAxiomAvailability using
  ( OSAxiomAvailability
  ; currentOSStatus
  )

-- OSAxiomBundle: OS axiom assembly for the YM mass gap route.
--
-- v0.3 / P33-closed state:
--   OS0 (temperedness):         true  (via currentOSStatus)
--   OS1 (Euclidean covariance): true  (2602.0092 P30, via currentOSStatus)
--   OS2 (reflection positivity): false — CompleteMonotonicityScaffold route open
--   OS3 (permutation symmetry): true  (via currentOSStatus)
--   OS4 (cluster decomposition): false — exponential decay / DLR-LSI route open
--
-- osComplete = false because all five must hold simultaneously.
-- OS2 and OS4 are the two live open obligations.

record OSAxiomBundle : Set₁ where
  field
    availability : OSAxiomAvailability
    -- Closed axioms: verified by refl against currentOSStatus.
    os0Available : OSAxiomAvailability.os0-temperedness availability ≡ true
    os1Available : OSAxiomAvailability.os1-euclidean-covariance availability ≡ true
    os3Available : OSAxiomAvailability.os3-permutation-symmetry availability ≡ true
    -- Open axioms: still false.
    reflectionPositivityWitness : Bool
    clusterPropertyWitness : Bool
    osComplete : Bool
    reflectionPositivityWitnessIsFalse : reflectionPositivityWitness ≡ false
    clusterPropertyWitnessIsFalse : clusterPropertyWitness ≡ false
    osCompleteIsFalse : osComplete ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalOSAxiomBundle : OSAxiomBundle
canonicalOSAxiomBundle = record
  { availability = currentOSStatus
  ; os0Available = refl
  ; os1Available = refl
  ; os3Available = refl
  ; reflectionPositivityWitness = false
  ; clusterPropertyWitness = false
  ; osComplete = false
  ; reflectionPositivityWitnessIsFalse = refl
  ; clusterPropertyWitnessIsFalse = refl
  ; osCompleteIsFalse = refl
  ; noClayPromotion = refl
  }

