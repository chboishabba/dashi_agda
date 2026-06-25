module DASHI.Physics.YangMills.OSAxiomBundle where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Physics.Closure.OSAxiomAvailability using
  ( OSAxiomAvailability
  ; currentOSStatus
  )

record OSAxiomBundle : Set₁ where
  field
    availability : OSAxiomAvailability
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
  ; reflectionPositivityWitness = false
  ; clusterPropertyWitness = false
  ; osComplete = false
  ; reflectionPositivityWitnessIsFalse = refl
  ; clusterPropertyWitnessIsFalse = refl
  ; osCompleteIsFalse = refl
  ; noClayPromotion = refl
  }
