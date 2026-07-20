module DASHI.Culture.RelationalTeachingCampaignBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Culture.DerivedCulturalUseAdmissibility as Cultural

------------------------------------------------------------------------
-- User-supplied examples are retained as bounded case-study analogies.

data CaseKind : Set where
  plantTeachingCase advertiserPressureCampaignCase : CaseKind

record CaseStudy : Set where
  constructor caseStudy
  field
    caseKind : CaseKind
    sourceLabel : String
    immediateScale : String
    relationalScale : String
    systemicScale : String
    factualAuthorityClaimed : Bool
    legalAuthorityClaimed : Bool
    communityAuthorityClaimed : Bool

open CaseStudy public

shampooGingerTeachingCase : CaseStudy
shampooGingerTeachingCase =
  caseStudy
    plantTeachingCase
    "user-supplied Kōpī ‘Enua / shampoo-ginger teaching example"
    "immediate sensory encounter with a plant"
    "teaching relation among tamariki, carers, place, language, and practice"
    "candidate multiscale lesson linking local experience to reciprocal ecology"
    false
    false
    false

advertiserPressureCase : CaseStudy
advertiserPressureCase =
  caseStudy
    advertiserPressureCampaignCase
    "user-supplied Vile Kyle / MFW campaign narrative"
    "a disputed public-media event and response"
    "activists, broadcasters, advertisers, audiences, and funding relations"
    "candidate resource-flow intervention aimed at accountability"
    false
    false
    false

record FractalTeachingCompression : Set where
  constructor fractalTeachingCompression
  field
    sourceCase : CaseStudy
    localLesson : String
    higherOrderContext : String
    compressionIsLossless : Bool
    compressionIsLosslessIsFalse : compressionIsLossless ≡ false
    provenanceRetained : Bool
    responsibilityRetained : Bool
    interpretation : String

canonicalPlantTeachingCompression : FractalTeachingCompression
canonicalPlantTeachingCompression =
  fractalTeachingCompression
    shampooGingerTeachingCase
    "bounded, age-appropriate, place-aware lesson"
    "a larger relational ecology and intergenerational knowledge context"
    false refl
    true
    true
    "teaching may compress a broad context into a local lesson while keeping provenance, limitations, and responsibility visible"

record Stage369CampaignReading : Set where
  constructor stage369CampaignReading
  field
    sourceCase : CaseStudy
    stage3Baseline : String
    stage6StructuralTension : String
    stage9Target : String
    targetAlreadyAchieved : Bool
    targetAlreadyAchievedIsFalse : targetAlreadyAchieved ≡ false
    historicalTruthPromoted : Bool
    historicalTruthPromotedIsFalse : historicalTruthPromoted ≡ false
    interpretation : String

canonicalCampaignStageReading : Stage369CampaignReading
canonicalCampaignStageReading =
  stage369CampaignReading
    advertiserPressureCase
    "baseline media and funding arrangement as represented in the supplied narrative"
    "advertiser pressure introduces a material contradiction into that arrangement"
    "accountability and changed funding incentives as the stated target"
    false refl
    false refl
    "a process-stage analogy can track intervention structure without deciding contested historical, legal, or ethical facts"

------------------------------------------------------------------------
-- Cultural provenance gate.

plantAnalogyProvenance : Cultural.ProvenanceWitness
plantAnalogyProvenance =
  Cultural.mkProvenanceWitness
    "user-supplied teaching example"
    "Kōpī ‘Enua / shampoo-ginger example supplied in this design thread"
    "bounded formal analogy for multiscale teaching"
    "no community authority, permission, universal Indigenous account, or living-practice substitution is claimed"

plantFormalAnalogyAdmissible :
  Cultural.AdmissibleCulturalUse
    Cultural.formalAnalogyMaterial
    Cultural.limitedFormalAnalogyUse
plantFormalAnalogyAdmissible = Cultural.formalAnalogyAdmissible plantAnalogyProvenance

------------------------------------------------------------------------
-- Correct Tlurey etymology boundary.

record TlureyEtymologyBoundary : Set where
  constructor tlureyEtymologyBoundary
  field
    canonicalExpansion : String
    socialRole : String
    truePlusLureClaimedAsOrigin : Bool
    truePlusLureClaimedAsOriginIsFalse : truePlusLureClaimedAsOrigin ≡ false
    futureDictionaryMayExtendUsage : Bool

canonicalTlureyEtymologyBoundary : TlureyEtymologyBoundary
canonicalTlureyEtymologyBoundary =
  tlureyEtymologyBoundary
    "truly the world's best brother/friend"
    "kinship and friendship affirmation with reciprocal responsibility"
    false refl
    true

record RelationalCaseBoundary : Set where
  constructor relationalCaseBoundary
  field
    examplesAreUserSupplied : Bool
    examplesAreFormalAnalogies : Bool
    examplesEstablishClinicalTruth : Bool
    examplesEstablishClinicalTruthIsFalse : examplesEstablishClinicalTruth ≡ false
    examplesEstablishCommunityAuthority : Bool
    examplesEstablishCommunityAuthorityIsFalse :
      examplesEstablishCommunityAuthority ≡ false
    examplesEstablishCampaignFacts : Bool
    examplesEstablishCampaignFactsIsFalse : examplesEstablishCampaignFacts ≡ false
    interpretation : String

canonicalRelationalCaseBoundary : RelationalCaseBoundary
canonicalRelationalCaseBoundary =
  relationalCaseBoundary
    true
    true
    false refl
    false refl
    false refl
    "the supplied cultural and campaign examples are retained as provenance-bounded design analogies, not promoted as community-authorised knowledge or adjudicated fact"
