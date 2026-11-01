module DASHI.Governance.PermacultureEvolutionTests where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Governance.PermacultureEvolution

------------------------------------------------------------------------
-- Canonical admissions close to profile equality.

holmgrenianAdmissionCloses : holmgrenianProfile ≡ holmgrenianProfile
holmgrenianAdmissionCloses =
  admissionImpliesProfileEquality canonicalHolmgrenianAdmission

mollisonianAdmissionCloses : mollisonianProfile ≡ mollisonianProfile
mollisonianAdmissionCloses =
  admissionImpliesProfileEquality canonicalMollisonianAdmission

newtonianAdmissionCloses : newtonianProfile ≡ newtonianProfile
newtonianAdmissionCloses =
  admissionImpliesProfileEquality canonicalNewtonianAdmission

------------------------------------------------------------------------
-- Promotion witnesses expose their authority payloads.

canonicalDomesticPromotionAuthority :
  PromotionAuthority holmgrenian mollisonian
canonicalDomesticPromotionAuthority =
  promotionAuthority
    (domesticToCommercial commercialProductionAuthority)

canonicalSovereignPromotionAuthority :
  PromotionAuthority mollisonian newtonian
canonicalSovereignPromotionAuthority =
  promotionAuthority
    (commercialToSovereign sovereignSubstrateAuthority)

------------------------------------------------------------------------
-- Diagram observations remain panel-qualified.

mollisonianEvolutionLowerBoundReceipt :
  lowerTenthsHa mollisonianEvolutionScale ≡ 10
mollisonianEvolutionLowerBoundReceipt = refl

mollisonianSplitLowerBoundReceipt :
  lowerTenthsHa mollisonianSplitScale ≡ 1000
mollisonianSplitLowerBoundReceipt = refl

------------------------------------------------------------------------
-- All promotion boundaries remain fail-closed.

scaleOnlyPromotionRemainsBlocked : scaleOnlyPromotionFlag ≡ false
scaleOnlyPromotionRemainsBlocked = scaleOnlyPromotionIsBlocked

historicalPromotionRemainsBlocked :
  historicalCharacterisationPromoted ≡ false
historicalPromotionRemainsBlocked =
  historicalCharacterisationPromotedIsFalse

empiricalPromotionRemainsBlocked :
  empiricalUniversalityPromoted ≡ false
empiricalPromotionRemainsBlocked =
  empiricalUniversalityPromotedIsFalse

moralPromotionRemainsBlocked : moralHierarchyPromoted ≡ false
moralPromotionRemainsBlocked = moralHierarchyPromotedIsFalse

politicalPromotionRemainsBlocked : politicalAuthorityPromoted ≡ false
politicalPromotionRemainsBlocked = politicalAuthorityPromotedIsFalse
