module DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.ComparativeSettlerColonialSovereigntySourceBidiExact as Sovereignty
import DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact as AUIsrael
import DASHI.Law.OperationalDirectionProvenanceBidiExact as Direction
import DASHI.Law.OperationalCommandAuthorityConstitutionalBidiExact as Command
import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism

------------------------------------------------------------------------
-- Herzog-policing x Country/native-title x Palestine coloniality.
-- This owner does not declare identical colonisation or infer NSW motive from
-- foreign-policy context.  It identifies residual coordinates whose erasure
-- would make sovereignty/self-determination claims invisible to the consumer.
------------------------------------------------------------------------

data ColonialityAuditFeature : Set where
  priorSovereignPeoplehood
  imposedRecognitionRegime
  landOrTerritoryDispossession
  settlementOrDemographicTransformation
  securityRationalisation
  differentialMovementOrAccess
  policingOfPoliticalDissent
  collectiveAttribution
  correctionChannelClosure : ColonialityAuditFeature

record ColonialityFeatureReceipt : Set where
  constructor colonialityFeatureReceipt
  field
    feature : ColonialityAuditFeature
    australiaReceipt : String
    palestineReceipt : String
    australiaEmpiricallyClosed : Bool
    palestineEmpiricallyClosed : Bool
    sameHistoricalMechanismProven : Bool

open ColonialityFeatureReceipt public

openColonialityFeature : ColonialityAuditFeature → ColonialityFeatureReceipt
openColonialityFeature f = colonialityFeatureReceipt
  f
  "requires Australia-specific Mabo/Uluru/Country/policing evidence"
  "requires Palestine-specific ICJ/UN/Palestinian evidence"
  false false false

record CountryPalestineColonialityAudit : Set where
  constructor countryPalestineColonialityAudit
  field
    peoplehood : ColonialityFeatureReceipt
    recognition : ColonialityFeatureReceipt
    dispossession : ColonialityFeatureReceipt
    settlement : ColonialityFeatureReceipt
    security : ColonialityFeatureReceipt
    movement : ColonialityFeatureReceipt
    dissentPolicing : ColonialityFeatureReceipt
    collectiveAttributionReceipt : ColonialityFeatureReceipt
    correctionClosure : ColonialityFeatureReceipt
    structuralHomologyPermitted : Bool
    structuralHomologyPermittedIsTrue : structuralHomologyPermitted ≡ true
    literalHistoricalIdentityPromoted : Bool
    literalHistoricalIdentityPromotedIsFalse : literalHistoricalIdentityPromoted ≡ false
    auditReference : String

open CountryPalestineColonialityAudit public

canonicalCountryPalestineAudit : CountryPalestineColonialityAudit
canonicalCountryPalestineAudit = countryPalestineColonialityAudit
  (openColonialityFeature priorSovereignPeoplehood)
  (openColonialityFeature imposedRecognitionRegime)
  (openColonialityFeature landOrTerritoryDispossession)
  (openColonialityFeature settlementOrDemographicTransformation)
  (openColonialityFeature securityRationalisation)
  (openColonialityFeature differentialMovementOrAccess)
  (openColonialityFeature policingOfPoliticalDissent)
  (openColonialityFeature collectiveAttribution)
  (openColonialityFeature correctionChannelClosure)
  true refl false refl
  "shared coloniality feature audit only; Australian and Palestinian histories/legal doctrines remain separately sourced"

------------------------------------------------------------------------
-- Mabo/Country epistemic-compression bridge.
-- The juridical surface 'recognised native title' is not exhaustive of Country,
-- law, authority, obligation or unceded-sovereignty claims.  This mirrors the
-- open PR #711 dominant-chart boundary without importing an unmerged module.
------------------------------------------------------------------------

data CountryConsumer : Set where
  crownRecognisedPropertyInterest
  countryRelation
  collectiveAuthority
  lawAndObligation
  materialEcologicalContinuity
  sovereigntyAndSelfDetermination : CountryConsumer

record CountryRecognitionBoundary : Set where
  constructor countryRecognitionBoundary
  field
    nativeTitleRecognitionExhaustsCountry : Bool
    nativeTitleRecognitionExhaustsCountryIsFalse : nativeTitleRecognitionExhaustsCountry ≡ false
    crownRecognitionCreatesUnderlyingIndigenousAuthority : Bool
    crownRecognitionCreatesUnderlyingIndigenousAuthorityIsFalse : crownRecognitionCreatesUnderlyingIndigenousAuthority ≡ false
    propertyTitleEqualsSovereignty : Bool
    propertyTitleEqualsSovereigntyIsFalse : propertyTitleEqualsSovereignty ≡ false
    securityAdministrationExtinguishesUnrepresentedCountryClaims : Bool
    securityAdministrationExtinguishesUnrepresentedCountryClaimsIsFalse : securityAdministrationExtinguishesUnrepresentedCountryClaims ≡ false

canonicalCountryRecognitionBoundary : CountryRecognitionBoundary
canonicalCountryRecognitionBoundary =
  countryRecognitionBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Herzog rally audit: a public-order/security observer can be locally useful
-- while erasing protest content, sovereignty claims and the provenance of the
-- protected/targeted political relation.  Missing coordinates must be restored,
-- not inferred from aggregate 'public disorder' labels.
------------------------------------------------------------------------

data HerzogPolicingCoordinate : Set where
  protestPoliticalContent
  palestinianSelfDeterminationContent
  herzogSourceContext
  commandAuthority
  commandContent
  transmission
  civilianDirection
  opportunityToComply
  forcePath
  groupSelection
  exitAccess
  foreignPolicySecurityContext : HerzogPolicingCoordinate

record HerzogPolicingColonialityFibre : Set where
  constructor herzogPolicingColonialityFibre
  field
    coordinateReference : HerzogPolicingCoordinate → String
    foreignPolicyContextKnown : Bool
    directForeignOperationalControlKnown : Bool
    directForeignOperationalControlKnownIsFalse : directForeignOperationalControlKnown ≡ false
    publicOrderLabelExhaustsPoliticalMeaning : Bool
    publicOrderLabelExhaustsPoliticalMeaningIsFalse : publicOrderLabelExhaustsPoliticalMeaning ≡ false
    securityRationaleProvesLawfulExercise : Bool
    securityRationaleProvesLawfulExerciseIsFalse : securityRationaleProvesLawfulExercise ≡ false
    fibreReference : String

open HerzogPolicingColonialityFibre public

canonicalHerzogColonialityFibre : HerzogPolicingColonialityFibre
canonicalHerzogColonialityFibre = herzogPolicingColonialityFibre
  (λ c → "coordinate requires encounter/command/source-specific receipt")
  true false refl false refl false refl
  "foreign-policy and security context retained without promoting a direct-control claim"

------------------------------------------------------------------------
-- Fascism-feature adapters: policing data can test mechanisms without first
-- applying a fascism label.
------------------------------------------------------------------------

data PolicingMechanism : Set where
  groupBasedSelection
  differentialEscalation
  differentialExitAccess
  sourceIdentityAsLiabilityProxy
  aggregateCategoryErasesIndividualLawfulness
  dissentAsConfirmingFault : PolicingMechanism

featureToPolicingMechanism : Fascism.FascismFeature → PolicingMechanism
featureToPolicingMechanism Fascism.collectiveGuiltTransport = groupBasedSelection
featureToPolicingMechanism Fascism.asymmetricRouting = differentialEscalation
featureToPolicingMechanism Fascism.provenanceWeaponisation = sourceIdentityAsLiabilityProxy
featureToPolicingMechanism Fascism.distinctionErasure = aggregateCategoryErasesIndividualLawfulness
featureToPolicingMechanism Fascism.terminalisation = dissentAsConfirmingFault
featureToPolicingMechanism Fascism.coerciveContraction = differentialExitAccess

record FascismPolicingAuditBoundary : Set where
  constructor fascismPolicingAuditBoundary
  field
    mechanismObservationAutomaticallyClosesFascismDiagnosis : Bool
    mechanismObservationAutomaticallyClosesFascismDiagnosisIsFalse : mechanismObservationAutomaticallyClosesFascismDiagnosis ≡ false
    foreignPolicyAlignmentAutomaticallyClosesPoliceMotive : Bool
    foreignPolicyAlignmentAutomaticallyClosesPoliceMotiveIsFalse : foreignPolicyAlignmentAutomaticallyClosesPoliceMotive ≡ false
    colonialityHomologyAutomaticallyClosesIntent : Bool
    colonialityHomologyAutomaticallyClosesIntentIsFalse : colonialityHomologyAutomaticallyClosesIntent ≡ false

canonicalFascismPolicingAuditBoundary : FascismPolicingAuditBoundary
canonicalFascismPolicingAuditBoundary =
  fascismPolicingAuditBoundary false refl false refl false refl

------------------------------------------------------------------------
-- BIDI claims and producer obligations.
------------------------------------------------------------------------

data HerzogCountryClaim : Set where
  publicOrderObserverIsEpistemicallyComplete
  australiaPalestineStructuralColonialityHomology
  australiaReplicatesPalestineExactColonisation
  nswPoliceImportedIsraeliSecurityPractice
  herzogPoliceResponseForeignPolicyMotivated
  countrySovereigntyContentErasedByPropertyOnlyChart : HerzogCountryClaim

data HerzogCountryProducer : Set where
  completePoliticalContentProducer
  pairedColonialityCoordinateProducer
  exactHistoricalMechanismProducer
  operationalTransferReceiptProducer
  motiveAndCoordinationProducer
  countryAuthorityResidualProducer : HerzogCountryProducer

reverseHerzogCountry : HerzogCountryClaim → HerzogCountryProducer
reverseHerzogCountry publicOrderObserverIsEpistemicallyComplete = completePoliticalContentProducer
reverseHerzogCountry australiaPalestineStructuralColonialityHomology = pairedColonialityCoordinateProducer
reverseHerzogCountry australiaReplicatesPalestineExactColonisation = exactHistoricalMechanismProducer
reverseHerzogCountry nswPoliceImportedIsraeliSecurityPractice = operationalTransferReceiptProducer
reverseHerzogCountry herzogPoliceResponseForeignPolicyMotivated = motiveAndCoordinationProducer
reverseHerzogCountry countrySovereigntyContentErasedByPropertyOnlyChart = countryAuthorityResidualProducer

record HerzogCountryBoundary : Set where
  constructor herzogCountryBoundary
  field
    australiaIsraelMilitaryLinkProvesNSWPoliceImport : Bool
    australiaIsraelMilitaryLinkProvesNSWPoliceImportIsFalse : australiaIsraelMilitaryLinkProvesNSWPoliceImport ≡ false
    armedCommunitySecurityAtFixedSitesProvesPoliceIsraeliTactics : Bool
    armedCommunitySecurityAtFixedSitesProvesPoliceIsraeliTacticsIsFalse : armedCommunitySecurityAtFixedSitesProvesPoliceIsraeliTactics ≡ false
    firstNationsNeverCededAssertionEqualsMunicipalCourtHolding : Bool
    firstNationsNeverCededAssertionEqualsMunicipalCourtHoldingIsFalse : firstNationsNeverCededAssertionEqualsMunicipalCourtHolding ≡ false
    palestinianSelfDeterminationHoldingEqualsMaboDoctrine : Bool
    palestinianSelfDeterminationHoldingEqualsMaboDoctrineIsFalse : palestinianSelfDeterminationHoldingEqualsMaboDoctrine ≡ false

canonicalHerzogCountryBoundary : HerzogCountryBoundary
canonicalHerzogCountryBoundary =
  herzogCountryBoundary false refl false refl false refl false refl
