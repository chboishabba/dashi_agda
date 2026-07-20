module DASHI.Culture.DerivedCulturalUseAdmissibility where

open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalProvenanceBoundaryCore as Existing

data Never : Set where

data CulturalMaterialKind : Set where
  namedAuthorMaterial : CulturalMaterialKind
  namedCommunityMaterial : CulturalMaterialKind
  livingPracticeMaterial : CulturalMaterialKind
  formalAnalogyMaterial : CulturalMaterialKind

data CulturalUseKind : Set where
  attributedReferenceUse : CulturalUseKind
  limitedFormalAnalogyUse : CulturalUseKind
  communityAuthorisedUse : CulturalUseKind
  extractiveUse : CulturalUseKind
  universalisingUse : CulturalUseKind
  livingPracticeSubstitutionUse : CulturalUseKind
  permissionClaimUse : CulturalUseKind

record ProvenanceWitness : Set where
  constructor mkProvenanceWitness
  field sourceName sourceContext contribution limits : String
record CommunityAuthorityWitness : Set where
  constructor mkCommunityAuthorityWitness
  field authorityHolder authorityScope authorityReference : String
record ConsentWitness : Set where
  constructor mkConsentWitness
  field consentHolder consentScope consentReference : String

data AdmissibleCulturalUse : CulturalMaterialKind → CulturalUseKind → Set where
  attributedReferenceAdmissible : ProvenanceWitness → AdmissibleCulturalUse namedAuthorMaterial attributedReferenceUse
  formalAnalogyAdmissible : ProvenanceWitness → AdmissibleCulturalUse formalAnalogyMaterial limitedFormalAnalogyUse
  communityUseAdmissible : ProvenanceWitness → CommunityAuthorityWitness → ConsentWitness → AdmissibleCulturalUse namedCommunityMaterial communityAuthorisedUse

extractionBlocked : ∀ {material} → AdmissibleCulturalUse material extractiveUse → Never
extractionBlocked ()
universalisationBlocked : ∀ {material} → AdmissibleCulturalUse material universalisingUse → Never
universalisationBlocked ()
livingPracticeSubstitutionBlocked : ∀ {material} → AdmissibleCulturalUse material livingPracticeSubstitutionUse → Never
livingPracticeSubstitutionBlocked ()
permissionClaimWithoutAuthorityBlocked : ∀ {material} → AdmissibleCulturalUse material permissionClaimUse → Never
permissionClaimWithoutAuthorityBlocked ()

kimmererProvenance : ProvenanceWitness
kimmererProvenance = mkProvenanceWitness
  "Robin Wall Kimmerer"
  "Braiding Sweetgrass; Citizen Potawatomi Nation authorship and context"
  "material inspiration for braided and reciprocal knowledge architecture"
  "DASHI's dialectical braid is a later formal extension and not attributed terminology"

kimmererAnalogyAdmissible : AdmissibleCulturalUse formalAnalogyMaterial limitedFormalAnalogyUse
kimmererAnalogyAdmissible = formalAnalogyAdmissible kimmererProvenance

existingCulturalBoundary : Existing.CulturalProvenanceBoundary
existingCulturalBoundary = Existing.canonicalCulturalProvenanceBoundary
