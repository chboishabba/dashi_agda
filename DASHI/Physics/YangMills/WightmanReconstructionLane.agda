module DASHI.Physics.YangMills.WightmanReconstructionLane where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record WightmanReconstructionLane : Set₁ where
  field
    osBundleAvailable : Bool
    hilbertSpaceDefined : Bool
    hamiltonianDefined : Bool
    vacuumIsUnique : Bool
    reconstructionDone : Bool
    osBundleAvailableIsFalse : osBundleAvailable ≡ false
    hilbertSpaceDefinedIsFalse : hilbertSpaceDefined ≡ false
    hamiltonianDefinedIsFalse : hamiltonianDefined ≡ false
    vacuumIsUniqueIsFalse : vacuumIsUnique ≡ false
    reconstructionDoneIsFalse : reconstructionDone ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalWightmanReconstructionLane : WightmanReconstructionLane
canonicalWightmanReconstructionLane = record
  { osBundleAvailable = false
  ; hilbertSpaceDefined = false
  ; hamiltonianDefined = false
  ; vacuumIsUnique = false
  ; reconstructionDone = false
  ; osBundleAvailableIsFalse = refl
  ; hilbertSpaceDefinedIsFalse = refl
  ; hamiltonianDefinedIsFalse = refl
  ; vacuumIsUniqueIsFalse = refl
  ; reconstructionDoneIsFalse = refl
  ; noClayPromotion = refl
  }
