module DASHI.Physics.Closure.YMClayDistanceAfterBalabanReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Closure.YMBalabanImportReceipt as Import

record YMClayDistanceAfterBalabanReceipt : Setω where
  field
    balabanImportReceipt : Import.YMBalabanImportReceipt
    balabanRouteConditional : Import.YMBalabanImportReceipt.inheritanceIsConditional balabanImportReceipt ≡ true
    remainingProblems : String
    ymClayProgrammeReframed : Bool
    ymClayProgrammeReframedProof : ymClayProgrammeReframed ≡ true
    productLatticeUniversalityProved : Bool
    productLatticeUniversalityProvedProof : productLatticeUniversalityProved ≡ false
    vacuumUniquenessProved : Bool
    vacuumUniquenessProvedProof : vacuumUniquenessProved ≡ false
    continuumMassGapProved : Bool
    continuumMassGapProvedProof : continuumMassGapProved ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedProof : clayYangMillsPromoted ≡ false

canonicalYMClayDistanceAfterBalabanReceipt : YMClayDistanceAfterBalabanReceipt
canonicalYMClayDistanceAfterBalabanReceipt =
  record
    { balabanImportReceipt = Import.canonicalYMBalabanImportReceipt
    ; balabanRouteConditional = refl
    ; remainingProblems = "Two remaining problems: product-lattice universality class and vacuum uniqueness/clustering."
    ; ymClayProgrammeReframed = true
    ; ymClayProgrammeReframedProof = refl
    ; productLatticeUniversalityProved = false
    ; productLatticeUniversalityProvedProof = refl
    ; vacuumUniquenessProved = false
    ; vacuumUniquenessProvedProof = refl
    ; continuumMassGapProved = false
    ; continuumMassGapProvedProof = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedProof = refl
    }
