module DASHI.Culture.DerivedCulturalUseAdmissibility where

open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalProvenanceBoundaryCore as Existing

------------------------------------------------------------------------
-- Cultural use requires provenance, accountable authority, and consent.

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
  field
    sourceName : String
    sourceContext : String
    contribution : String
    limits : String

record CommunityAuthorityWitness : Set where
  constructor mkCommunityAuthorityWitness
  field
    authorityHolder : String
    authorityScope : String
    authorityReference : String

record ConsentWitness : Set where
  constructor mkConsentWitness
  field
    consentHolder : String
    consentScope : String
    consentReference : String

record AccountableCulturalUse : Set where
  constructor mkAccountableCulturalUse
  field
    material : CulturalMaterialKind
    use : CulturalUseKind
    provenance : ProvenanceWitness
    authority : CommunityAuthorityWitness
    consent : ConsentWitness

-- Only attributed reference, limited analogy, and explicitly authorised use
-- are constructible. Extraction, universalisation, substitution, and implied
-- permission have no constructors.
data AdmissibleCulturalUse : CulturalMaterialKind → CulturalUseKind → Set where
  attributedReferenceAdmissible :
    (provenance : ProvenanceWitness) →
    AdmissibleCulturalUse namedAuthorMaterial attributedReferenceUse
  formalAnalogyAdmissible :
    (provenance : ProvenanceWitness) →
    AdmissibleCulturalUse formalAnalogyMaterial limitedFormalAnalogyUse
  communityUseAdmissible :
    (provenance : ProvenanceWitness) →
    (authority : CommunityAuthorityWitness) →
    (consent : ConsentWitness) →
    AdmissibleCulturalUse namedCommunityMaterial communityAuthorisedUse

extractionBlocked :
  ∀ {material} → AdmissibleCulturalUse material extractiveUse → Never
extractionBlocked ()

universalisationBlocked :
  ∀ {material} → AdmissibleCulturalUse material universalisingUse → Never
universalisationBlocked ()

livingPracticeSubstitutionBlocked :
  ∀ {material} →
  AdmissibleCulturalUse material livingPracticeSubstitutionUse → Never
livingPracticeSubstitutionBlocked ()

permissionClaimWithoutAuthorityBlocked :
  ∀ {material} → AdmissibleCulturalUse material permissionClaimUse → Never
permissionClaimWithoutAuthorityBlocked ()

kimmererProvenance : ProvenanceWitness
kimmererProvenance =
  mkProvenanceWitness
    "Robin Wall Kimmerer"
    "Braiding Sweetgrass; Citizen Potawatomi Nation authorship and context"
    "material inspiration for braided and reciprocal knowledge architecture"
    "DASHI's dialectical braid is a later formal extension and not attributed terminology"

kimmererAnalogyAdmissible :
  AdmissibleCulturalUse formalAnalogyMaterial limitedFormalAnalogyUse
kimmererAnalogyAdmissible = formalAnalogyAdmissible kimmererProvenance

existingCulturalBoundary : Existing.CulturalProvenanceBoundary
existingCulturalBoundary = Existing.canonicalCulturalProvenanceBoundary
