module DASHI.Law.SensibLawWoogarooOffsetLandscapeCounterfactualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- WOOGAROO OFFSET LANDSCAPE COUNTERFACTUAL
--
-- Public-source, attribution-preserving comparison of impact-landscape and
-- proposed-offset-landscape coordinates.  This does not identify any candidate
-- public parcel as the exact 2019/8575 offset parcel unless a primary project
-- source does so.
------------------------------------------------------------------------

data LandscapeObject : Set where
  woogarooImpactLandscape : LandscapeObject
  mtMortRegionalLandscape : LandscapeObject
  mtWalkerWestMtMortSubmissionLead : LandscapeObject
  aroonaStationPublicConservationProperty : LandscapeObject
  littleKipperCreekOtherEPBCOffset : LandscapeObject

data Coordinate : Set where
  urbanDevelopmentPressure : Coordinate
  corridorNetworkPosition : Coordinate
  existingProtection : Coordinate
  vegetationMaturity : Coordinate
  speciesPopulationFunction : Coordinate
  additionalityRiskOfLoss : Coordinate
  ecologicalTimeLag : Coordinate

data EvidenceRelation : Set where
  exactSameObject : EvidenceRelation
  sameRegionalLandscapeOnly : EvidenceRelation
  secondaryProjectLeadOnly : EvidenceRelation
  otherProjectAnalogyOnly : EvidenceRelation
  identityNotProved : EvidenceRelation

record LandscapeEvidence : Set where
  constructor landscape-evidence
  field
    object : LandscapeObject
    coordinate : Coordinate
    proposition : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    relationTo20198575Offset : EvidenceRelation
    mayBePromotedToExactOffsetFact : Bool

open LandscapeEvidence public

woogarooCatchmentPressure : LandscapeEvidence
woogarooCatchmentPressure = landscape-evidence
  woogarooImpactLandscape
  urbanDevelopmentPressure
  "Ipswich City Council describes the Woogaroo Creek sub-catchment as including Springfield and other fast-growing urban residential areas; upper catchment retains significant bushland while development is extensive."
  Provenance.externalSourceClaim
  exactSameObject
  true

woogarooCorridorFunction : LandscapeEvidence
woogarooCorridorFunction = landscape-evidence
  woogarooImpactLandscape
  corridorNetworkPosition
  "Ipswich City Council describes Woogaroo Creek as flowing north from White Rock-Spring Mountain, identifies the sub-catchment as important for securing urban koala populations and as part of the Flinders-Karawatha regional corridor; Ric Nattrass Environmental Park provides connectivity from White Rock-Spring Mountain to the Brisbane River corridor."
  Provenance.externalSourceClaim
  exactSameObject
  true

mtMortExistingConservation : LandscapeEvidence
mtMortExistingConservation = landscape-evidence
  mtMortRegionalLandscape
  existingProtection
  "Ipswich City Council's koala conservation plan describes Mt Mort PRA as highly rural, containing more than 1,900 ha of connected land under voluntary conservation agreements / Land for Wildlife plus a large QTFN conservation property, and says a high proportion of the PRA is managed for conservation."
  Provenance.externalSourceClaim
  sameRegionalLandscapeOnly
  false

mtMortSubmissionOffsetLead : LandscapeEvidence
mtMortSubmissionOffsetLead = landscape-evidence
  mtWalkerWestMtMortSubmissionLead
  additionalityRiskOfLoss
  "A public submission responding to EPBC 2019/8575 identifies a proposed offset property in the Mt Walker West/Mt Mort area and criticises ecological differences and erosion/landscape condition."
  Provenance.secondarySourceInterpretation
  secondaryProjectLeadOnly
  false

aroonaConservationStatus : LandscapeEvidence
aroonaConservationStatus = landscape-evidence
  aroonaStationPublicConservationProperty
  existingProtection
  "Queensland Trust for Nature publicly states that it owns/manages Aroona Station at Mt Mort for koala-supporting conservation; other public material records conservation/offset activity on Aroona Station."
  Provenance.externalSourceClaim
  identityNotProved
  false

littleKipperOtherProject : LandscapeEvidence
littleKipperOtherProject = landscape-evidence
  littleKipperCreekOtherEPBCOffset
  vegetationMaturity
  "A Springfield Rise Additional Offset Management Plan for EPBC 2013/7057 describes a Biarra/Little Kipper Creek offset containing non-remnant, regrowth and remnant vegetation, pastoral grazing disturbance and rehabilitation areas. This is an offset architecture analogy from another EPBC approval, not evidence of the 2019/8575 offset package."
  Provenance.externalSourceClaim
  otherProjectAnalogyOnly
  false

------------------------------------------------------------------------
-- Cross-source inferences: repository-owned, not attributed back to sources.
------------------------------------------------------------------------

record CounterfactualInference : Set where
  constructor counterfactual-inference
  field
    proposition : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    exact20198575OffsetIdentityRequired : Bool
    currentlyProvedForExactOffset : Bool

open CounterfactualInference public

riskOfLossAsymmetryLead : CounterfactualInference
riskOfLossAsymmetryLead = counterfactual-inference
  "If the exact 2019/8575 offset parcel lies within a landscape already under substantial conservation management and low realistic clearing pressure, its avoided-loss additionality may be lower than raw hectares imply when compared with an urban-pressure Woogaroo impact landscape."
  Provenance.crossSourceInference
  true
  false

maturityAsymmetryLead : CounterfactualInference
maturityAsymmetryLead = counterfactual-inference
  "If mature/remnant Woogaroo habitat is replaced by planted, non-remnant or young-regrowth offset habitat, equivalent hectares do not establish equivalent present ecological function without a species-specific quality, time-lag and confidence bridge."
  Provenance.crossSourceInference
  true
  false

protectedNetworkAsymmetryLead : CounterfactualInference
protectedNetworkAsymmetryLead = counterfactual-inference
  "Loss of habitat occupying a live urban corridor between secured conservation nodes may have a different protected-matter function from protection of habitat elsewhere, even where both sites support koalas."
  Provenance.crossSourceInference
  true
  false

------------------------------------------------------------------------
-- Attribution / WrongType boundaries.
------------------------------------------------------------------------

record CounterfactualBoundary : Set where
  constructor counterfactual-boundary
  field
    sameRegionDoesNotProveSameParcel : Bool
    mtMortDoesNotEqualAroona : Bool
    otherEPBCOffsetDoesNotEqual20198575Offset : Bool
    publicSubmissionDoesNotCreateAgencyFinding : Bool
    crossSourceInferenceDoesNotBecomeSourceClaim : Bool
    lowRegionalPressureDoesNotProveExactParcelRiskValue : Bool
    plantedStatusElsewhereDoesNotProveExactOffsetPlanted : Bool
    matureImpactClaimStillNeedsSameParcelEvidence : Bool

counterfactualBoundary : CounterfactualBoundary
counterfactualBoundary = counterfactual-boundary
  true true true true true true true true

record CurrentCounterfactualState : Set where
  constructor current-counterfactual-state
  field
    impactLandscapePressureSourcePaid : Bool
    impactLandscapeCorridorSourcePaid : Bool
    mtMortRegionalConservationSourcePaid : Bool
    exactOffsetParcelIdentityPaid : Bool
    exactOffsetRiskOfLossPaid : Bool
    exactOffsetVegetationAgePaid : Bool
    exactLikeForLikeComparisonPaid : Bool
    offsetInadequacyProved : Bool

currentState : CurrentCounterfactualState
currentState = current-counterfactual-state
  true true true false false false false false
