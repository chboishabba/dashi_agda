module DASHI.Law.ZionistPoliticalCultureSecurityRepertoireExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bounded Zionist political-cultural repertoire.
-- This owner explicitly distinguishes political ideology/culture from Judaism,
-- Jewish identity, Israeli citizenship, and the whole population of Israel.
------------------------------------------------------------------------

data RepertoireSourceRole : Set where
  scholarlyHistory : RepertoireSourceRole
  politicalTheory : RepertoireSourceRole
  officialIsraeliSpeech : RepertoireSourceRole
  unCommissionFinding : RepertoireSourceRole
  icjJudicialObservation : RepertoireSourceRole
  dashiSynthesis : RepertoireSourceRole

data ZionistCurrent : Set where
  politicalZionism : ZionistCurrent
  labourZionism : ZionistCurrent
  revisionistZionism : ZionistCurrent
  religiousZionism : ZionistCurrent
  messianicHardalCurrent : ZionistCurrent
  currentUnspecified : ZionistCurrent

data RepertoireCoordinate : Set where
  securityCentrality : RepertoireCoordinate
  existentialThreat : RepertoireCoordinate
  collectiveInsecurity : RepertoireCoordinate
  selfRelianceByForce : RepertoireCoordinate
  nationalSacrifice : RepertoireCoordinate
  collectiveResponsibility : RepertoireCoordinate
  territorialRedemption : RepertoireCoordinate
  biblicalEnemyRoleBinding : RepertoireCoordinate
  militaryCivilianInterpenetration : RepertoireCoordinate
  settlerColonialTerritoriality : RepertoireCoordinate

record RepertoireReceipt : Set where
  constructor repertoireReceipt
  field
    coordinate : RepertoireCoordinate
    current : ZionistCurrent
    sourceRole : RepertoireSourceRole
    sourceReference : String
    boundedDescription : String

open RepertoireReceipt public

securityCentralityReceipt : RepertoireReceipt
securityCentralityReceipt = repertoireReceipt
  securityCentrality currentUnspecified scholarlyHistory
  "Colin Shindler, A History of Modern Israel; scholarship treating Zionism and security as central determinants of Israeli state history"
  "Security is a recurring organising coordinate in Zionist/Israeli political history; this does not imply every Zionist current assigns it the same meaning or priority."

nationalSecurityVernacularReceipt : RepertoireReceipt
nationalSecurityVernacularReceipt = repertoireReceipt
  militaryCivilianInterpenetration politicalZionism politicalTheory
  "Daniel Levine and related scholarship on Zionist national-security discourse and strategic vernacular"
  "Scholarship identifies a specifically Zionist national-security discourse and institutional vernacular linking state-building, military institutions and collective security."

religiousEnemyRoleReceipt : RepertoireReceipt
religiousEnemyRoleReceipt = repertoireReceipt
  biblicalEnemyRoleBinding religiousZionism scholarlyHistory
  "Scholarship/reporting on religious-Zionist and Hardal currents in Israeli politics and the IDF"
  "Biblical enemy imagery and territorial-redemption language are documented in specific religious-nationalist Zionist currents; they are not attributed to all Zionists."

herzogCollectiveResponsibilityReceipt : RepertoireReceipt
herzogCollectiveResponsibilityReceipt = repertoireReceipt
  collectiveResponsibility currentUnspecified officialIsraeliSpeech
  "Isaac Herzog press conference, 12 October 2023; later cited in UN material"
  "Herzog stated that an entire nation bore responsibility and rejected a clean civilian/authority separation. This is a leader-level activation of collective-responsibility rhetoric, not a population-wide belief survey."

netanyahuAmalekRepertoireReceipt : RepertoireReceipt
netanyahuAmalekRepertoireReceipt = repertoireReceipt
  biblicalEnemyRoleBinding currentUnspecified officialIsraeliSpeech
  "Benjamin Netanyahu wartime Amalek invocation, 28 October and 3 November 2023"
  "Netanyahu activated a biblical enemy-role motif in wartime rhetoric and repeated it to soldiers; current-specific ideological classification remains separately sourced."

------------------------------------------------------------------------
-- Non-identity boundaries.
------------------------------------------------------------------------

record ZionismIdentityBoundary : Set where
  constructor zionismIdentityBoundary
  field
    judaismEqualsZionism : Bool
    judaismEqualsZionismIsFalse : judaismEqualsZionism ≡ false
    jewishIdentityEqualsZionism : Bool
    jewishIdentityEqualsZionismIsFalse : jewishIdentityEqualsZionism ≡ false
    israeliCitizenshipEqualsZionism : Bool
    israeliCitizenshipEqualsZionismIsFalse : israeliCitizenshipEqualsZionism ≡ false
    stateOfIsraelEqualsOneZionistCurrent : Bool
    stateOfIsraelEqualsOneZionistCurrentIsFalse : stateOfIsraelEqualsOneZionistCurrent ≡ false
    allZionistsShareAllRepertoireCoordinates : Bool
    allZionistsShareAllRepertoireCoordinatesIsFalse : allZionistsShareAllRepertoireCoordinates ≡ false

canonicalZionismIdentityBoundary : ZionismIdentityBoundary
canonicalZionismIdentityBoundary =
  zionismIdentityBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data RepertoireClaim : Set where
  coordinateOccursInZionistPoliticalCulture : RepertoireClaim
  coordinateOccursInSpecificCurrent : RepertoireClaim
  coordinateIsUniversallySharedByAllZionists : RepertoireClaim
  judaismAndZionismAreIdentical : RepertoireClaim
  israeliPopulationAndZionismAreIdentical : RepertoireClaim

data RepertoireProducer : Set where
  multiSourceRepertoireProducer : RepertoireProducer
  currentSpecificCorpusProducer : RepertoireProducer
  universalPopulationSurveyProducer : RepertoireProducer
  religionIdeologyIdentityProducer : RepertoireProducer
  statePopulationIdeologyIdentityProducer : RepertoireProducer

reverseRepertoire : RepertoireClaim → RepertoireProducer
reverseRepertoire coordinateOccursInZionistPoliticalCulture = multiSourceRepertoireProducer
reverseRepertoire coordinateOccursInSpecificCurrent = currentSpecificCorpusProducer
reverseRepertoire coordinateIsUniversallySharedByAllZionists = universalPopulationSurveyProducer
reverseRepertoire judaismAndZionismAreIdentical = religionIdeologyIdentityProducer
reverseRepertoire israeliPopulationAndZionismAreIdentical = statePopulationIdeologyIdentityProducer
