module DASHI.Law.ComparativeSettlerColonialSovereigntySourceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bounded comparative sovereignty layer.
-- Australia/Mabo/Uluru and Palestine/ICJ are not collapsed into one legal
-- doctrine.  The comparison is structural and consumer-specific.
------------------------------------------------------------------------

data SovereigntySourceRole : Set where
  highCourtHolding
  firstNationsConsensusStatement
  icjAdvisoryOpinion
  australianGovernmentRecognitionAct
  governmentPolicyStatement
  secondaryInterpretation
  dashiStructuralHomology : SovereigntySourceRole

data SovereigntyProposition : Set where
  terraNulliusRejected
  nativeTitleMaySurviveCrownSovereignty
  crownAcquiredRadicalNotAutomaticBeneficialTitle
  crownSovereigntyAcquisitionNonJusticiableMunicipally
  firstNationsSovereigntyNeverCededAssertion
  firstNationsSovereigntyCoexistsWithCrownAssertion
  palestinianSelfDeterminationRight
  israelNotEntitledToSovereigntyOverOccupiedPalestinianTerritory
  israeliSettlementsAndAnnexationUnlawful
  australianRecognitionOfSovereignStateOfPalestine
  australianAndPalestinianCasesLegallyIdentical
  settlerColonialStructuralHomology : SovereigntyProposition

record SovereigntySourceReceipt : Set where
  constructor sovereigntySourceReceipt
  field
    proposition : SovereigntyProposition
    role : SovereigntySourceRole
    sourceReference : String
    boundedDescription : String

open SovereigntySourceReceipt public

maboTerraNulliusReceipt : SovereigntySourceReceipt
maboTerraNulliusReceipt = sovereigntySourceReceipt
  terraNulliusRejected highCourtHolding
  "Mabo v Queensland (No 2) (1992) 175 CLR 1"
  "High Court rejected the terra-nullius premise as a basis for denying pre-existing Indigenous land rights"

maboSurvivalReceipt : SovereigntySourceReceipt
maboSurvivalReceipt = sovereigntySourceReceipt
  nativeTitleMaySurviveCrownSovereignty highCourtHolding
  "Mabo v Queensland (No 2) (1992) 175 CLR 1"
  "Native title rights and interests may survive the Crown's acquisition of sovereignty"

maboRadicalTitleReceipt : SovereigntySourceReceipt
maboRadicalTitleReceipt = sovereigntySourceReceipt
  crownAcquiredRadicalNotAutomaticBeneficialTitle highCourtHolding
  "Mabo v Queensland (No 2), Brennan J; later High Court summaries"
  "Crown radical title did not itself confer absolute beneficial ownership of occupied land"

maboSovereigntyJusticiabilityReceipt : SovereigntySourceReceipt
maboSovereigntyJusticiabilityReceipt = sovereigntySourceReceipt
  crownSovereigntyAcquisitionNonJusticiableMunicipally highCourtHolding
  "Brennan J, Mabo (No 2); Brennan J 1995 summary of Mabo"
  "Municipal courts do not adjudicate the validity of the acquisition of sovereignty; its legal effects on native title are justiciable"

uluruNeverCededReceipt : SovereigntySourceReceipt
uluruNeverCededReceipt = sovereigntySourceReceipt
  firstNationsSovereigntyNeverCededAssertion firstNationsConsensusStatement
  "Uluru Statement from the Heart (2017)"
  "First Nations delegates state that their sovereignty has never been ceded or extinguished"

uluruCoexistenceReceipt : SovereigntySourceReceipt
uluruCoexistenceReceipt = sovereigntySourceReceipt
  firstNationsSovereigntyCoexistsWithCrownAssertion firstNationsConsensusStatement
  "Uluru Statement from the Heart (2017)"
  "The Statement describes First Nations sovereignty as co-existing with Crown sovereignty"

icjSelfDeterminationReceipt : SovereigntySourceReceipt
icjSelfDeterminationReceipt = sovereigntySourceReceipt
  palestinianSelfDeterminationRight icjAdvisoryOpinion
  "ICJ Advisory Opinion, Legal Consequences arising from the Policies and Practices of Israel in the OPT, 19 July 2024"
  "ICJ treated Palestinian self-determination as a fundamental legal right and found Israeli policies obstruct it"

icjNoIsraeliSovereigntyReceipt : SovereigntySourceReceipt
icjNoIsraeliSovereigntyReceipt = sovereigntySourceReceipt
  israelNotEntitledToSovereigntyOverOccupiedPalestinianTerritory icjAdvisoryOpinion
  "ICJ Advisory Opinion, 19 July 2024"
  "ICJ held Israel is not entitled to sovereignty over or to exercise sovereign powers in any part of the Occupied Palestinian Territory on account of occupation"

icjSettlementReceipt : SovereigntySourceReceipt
icjSettlementReceipt = sovereigntySourceReceipt
  israeliSettlementsAndAnnexationUnlawful icjAdvisoryOpinion
  "ICJ Advisory Opinion, 19 July 2024"
  "ICJ reaffirmed the illegality of settlements and found annexation/continued presence consequences contrary to international law"

australiaPalestineRecognitionReceipt : SovereigntySourceReceipt
australiaPalestineRecognitionReceipt = sovereigntySourceReceipt
  australianRecognitionOfSovereignStateOfPalestine australianGovernmentRecognitionAct
  "Australian Prime Minister and Foreign Minister joint statement, 21 September 2025"
  "Australia formally recognised the independent and sovereign State of Palestine"

------------------------------------------------------------------------
-- Comparison fibre: shared coordinates may be investigated without declaring
-- historical identity or doctrinal equivalence.
------------------------------------------------------------------------

data ComparisonCoordinate : Set where
  priorPeoplehood
  imposedSovereignOrder
  dispossessionOrTerritorialTaking
  recognitionRegime
  settlementOrDemographicTransformation
  securityAdministration
  differentialMovementControl
  selfDeterminationConstraint
  coerciveEnforcement : ComparisonCoordinate

record ComparativeColonialityFibre : Set where
  constructor comparativeColonialityFibre
  field
    australiaCoordinateReceipt : ComparisonCoordinate → String
    palestineCoordinateReceipt : ComparisonCoordinate → String
    sameHistoricalDoctrine : Bool
    sameHistoricalDoctrineIsFalse : sameHistoricalDoctrine ≡ false
    structuralHomologyOnly : Bool
    structuralHomologyOnlyIsTrue : structuralHomologyOnly ≡ true
    comparisonReference : String

open ComparativeColonialityFibre public

canonicalComparativeFibre : ComparativeColonialityFibre
canonicalComparativeFibre = comparativeColonialityFibre
  (λ c → "Australia coordinate requires Mabo/Uluru/native-title/Country-specific evidence")
  (λ c → "Palestine coordinate requires ICJ/UN/Palestinian-source-specific evidence")
  false refl true refl
  "structural comparison only: shared coloniality coordinates do not merge legal systems or histories"

------------------------------------------------------------------------
-- BIDI routing.
------------------------------------------------------------------------

data SovereigntyComparisonClaim : Set where
  australianNativeTitleSurvival
  firstNationsNeverCededAssertion
  palestinianSelfDeterminationViolation
  israelLacksSovereigntyInOPT
  structuralColonialityComparison
  identicalColonisationClaim : SovereigntyComparisonClaim

data SovereigntyComparisonProducer : Set where
  maboHoldingProducer
  firstNationsStatementProducer
  icjAdvisoryProducer
  pairedCaseSpecificCoordinateProducer
  historicalIdentityProducer : SovereigntyComparisonProducer

reverseSovereigntyComparison : SovereigntyComparisonClaim → SovereigntyComparisonProducer
reverseSovereigntyComparison australianNativeTitleSurvival = maboHoldingProducer
reverseSovereigntyComparison firstNationsNeverCededAssertion = firstNationsStatementProducer
reverseSovereigntyComparison palestinianSelfDeterminationViolation = icjAdvisoryProducer
reverseSovereigntyComparison israelLacksSovereigntyInOPT = icjAdvisoryProducer
reverseSovereigntyComparison structuralColonialityComparison = pairedCaseSpecificCoordinateProducer
reverseSovereigntyComparison identicalColonisationClaim = historicalIdentityProducer

record ComparativeSovereigntyBoundary : Set where
  constructor comparativeSovereigntyBoundary
  field
    uluruAssertionCountsAsHighCourtHolding : Bool
    uluruAssertionCountsAsHighCourtHoldingIsFalse : uluruAssertionCountsAsHighCourtHolding ≡ false
    maboNativeTitleRecognitionEqualsFirstNationsSovereigntyRecognition : Bool
    maboNativeTitleRecognitionEqualsFirstNationsSovereigntyRecognitionIsFalse : maboNativeTitleRecognitionEqualsFirstNationsSovereigntyRecognition ≡ false
    icjOccupationHoldingEqualsAustralianNativeTitleDoctrine : Bool
    icjOccupationHoldingEqualsAustralianNativeTitleDoctrineIsFalse : icjOccupationHoldingEqualsAustralianNativeTitleDoctrine ≡ false
    structuralHomologyImpliesIdenticalColonisation : Bool
    structuralHomologyImpliesIdenticalColonisationIsFalse : structuralHomologyImpliesIdenticalColonisation ≡ false

canonicalComparativeSovereigntyBoundary : ComparativeSovereigntyBoundary
canonicalComparativeSovereigntyBoundary =
  comparativeSovereigntyBoundary false refl false refl false refl false refl
