module DASHI.Physics.Closure.YMBalabanImportReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Closure.YMBalabanApproachStatusReceipt as Approach

record YMBalabanImportReceipt : Setω where
  field
    approachReceipt : Approach.YMBalabanApproachStatusReceipt
    approachRequiresClusterExpansion : Approach.YMBalabanApproachStatusReceipt.balabanApproachRequiresClusterExpansion approachReceipt ≡ true
    authorityStatement : String
    balabanTightnessTheoremCitationAuthority : Bool
    balabanTightnessTheoremCitationAuthorityProof : balabanTightnessTheoremCitationAuthority ≡ true
    ymL3InheritedFromBalaban : Bool
    ymL3InheritedFromBalabanProof : ymL3InheritedFromBalaban ≡ true
    inheritanceIsConditional : Bool
    inheritanceIsConditionalProof : inheritanceIsConditional ≡ true
    productLatticeInBalabanClassProved : Bool
    productLatticeInBalabanClassProvedProof : productLatticeInBalabanClassProved ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedProof : clayYangMillsPromoted ≡ false

canonicalYMBalabanImportReceipt : YMBalabanImportReceipt
canonicalYMBalabanImportReceipt =
  record
    { approachReceipt = Approach.canonicalYMBalabanApproachStatusReceipt
    ; approachRequiresClusterExpansion = refl
    ; authorityStatement = "Balaban is a citation-authority route only if the product lattice lies in the 4D Wilson SU(N) universality class."
    ; balabanTightnessTheoremCitationAuthority = true
    ; balabanTightnessTheoremCitationAuthorityProof = refl
    ; ymL3InheritedFromBalaban = true
    ; ymL3InheritedFromBalabanProof = refl
    ; inheritanceIsConditional = true
    ; inheritanceIsConditionalProof = refl
    ; productLatticeInBalabanClassProved = false
    ; productLatticeInBalabanClassProvedProof = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedProof = refl
    }
