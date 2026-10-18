module DASHI.Governance.SuccessorPolityForkFamilyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Governance.ChinaTaiwanHistoricalSuccessionIdentityExact as Taiwan
import DASHI.Environment.KoreanNaturalFarmingExact as KNF

------------------------------------------------------------------------
-- REVOLUTIONARY / PARTITION / SUCCESSOR-POLITY FAMILY
--
-- A shared historical population or political territory may fork into distinct
-- institutions.  The family preserves fork mechanism and later trajectory:
-- civil war, foreign occupation, negotiated partition and ideological bloc
-- division are not one event type.
------------------------------------------------------------------------

koreaStateHistory : Source.AttributedSource
koreaStateHistory = Source.mkNoDOISource
  "United States Department of State, Office of the Historian"
  "The Korean War, 1950-1953"
  "Milestones in the History of U.S. Foreign Relations"
  "historical"
  "https://history.state.gov/milestones/1945-1952/korean-war"
  Source.governmentSource
  "source for post-WWII temporary division at the 38th parallel and emergence of Soviet-backed DPRK and U.S.-backed ROK"
  Source.publicAttribution

vietnamPartitionHistory : Source.AttributedSource
vietnamPartitionHistory = Source.mkNoDOISource
  "United States Department of State"
  "Vietnam background note: North and South Partition"
  "archived background note"
  "2008"
  "https://2009-2017.state.gov/outofdate/bgn/vietnam/109323.htm"
  Source.governmentSource
  "source for 1954 Geneva cease-fire and provisional division near the 17th parallel; later reunification requires separate source"
  Source.publicAttribution

vietnamReunification : Source.AttributedSource
vietnamReunification = Source.mkNoDOISource
  "Government of Vietnam"
  "Constitutional / government historical material"
  "Government of Vietnam"
  "1976 history, current web carrier"
  "https://vietnam.gov.vn/laws"
  Source.governmentSource
  "source for the July 1976 establishment of the Socialist Republic of Vietnam after reunification"
  Source.publicAttribution

germanyReunification : Source.AttributedSource
germanyReunification = Source.mkNoDOISource
  "Federal Government of Germany"
  "German Unity Treaty chronology"
  "Bundesregierung"
  "1990 / current historical carrier"
  "https://www.bundesregierung.de/breg-de/schwerpunkte/deutsche-einheit/einigungsvertrag-353970"
  Source.governmentSource
  "source for the 1990 unification treaty joining the GDR and Federal Republic"
  Source.publicAttribution

irelandPartition : Source.AttributedSource
irelandPartition = Source.mkNoDOISource
  "UK House of Commons Library"
  "100 years since the Government of Ireland Act 1920"
  "House of Commons Library"
  "2020"
  "https://commonslibrary.parliament.uk/research-briefings/cbp-12131/"
  Source.governmentSource
  "source for statutory partition into Northern and Southern Ireland and the later Irish Free State trajectory"
  Source.publicAttribution

data ForkMechanism : Set where
  civilWarRivalGovernmentFork : ForkMechanism
  foreignOccupationColdWarFork : ForkMechanism
  ceasefireProvisionalPartitionFork : ForkMechanism
  negotiatedConstitutionalPartitionFork : ForkMechanism
  ideologicalBlocDivisionFork : ForkMechanism

data ResolutionMode : Set where
  unresolvedDualPolity : ResolutionMode
  reunifiedByMilitaryPoliticalVictory : ResolutionMode
  reunifiedByNegotiatedAccession : ResolutionMode
  partitionPersistsWithAgreementFramework : ResolutionMode

record SuccessorPolityCase : Set where
  constructor successor-polity-case
  field
    label : String
    mechanism : ForkMechanism
    laterResolution : ResolutionMode
    source : Source.AttributedSource
    sharedHistoricalSurface : Bool
    samePresentPolity : Bool
    sharedOriginDeterminesPresentIdentity : Bool
    oneSideAutomaticallyInheritsLegitimacy : Bool

open SuccessorPolityCase public

chinaTaiwanCase : SuccessorPolityCase
chinaTaiwanCase = successor-polity-case
  "PRC / ROC-on-Taiwan"
  civilWarRivalGovernmentFork
  unresolvedDualPolity
  Taiwan.taiwanWhiteTerrorMuseum
  true false false false

koreaCase : SuccessorPolityCase
koreaCase = successor-polity-case
  "DPRK / ROK"
  foreignOccupationColdWarFork
  unresolvedDualPolity
  koreaStateHistory
  true false false false

vietnamCase : SuccessorPolityCase
vietnamCase = successor-polity-case
  "North / South Vietnam, later reunification"
  ceasefireProvisionalPartitionFork
  reunifiedByMilitaryPoliticalVictory
  vietnamPartitionHistory
  true false false false

germanyCase : SuccessorPolityCase
germanyCase = successor-polity-case
  "FRG / GDR, later reunification"
  ideologicalBlocDivisionFork
  reunifiedByNegotiatedAccession
  germanyReunification
  true false false false

irelandCase : SuccessorPolityCase
irelandCase = successor-polity-case
  "Ireland / Northern Ireland partition trajectory"
  negotiatedConstitutionalPartitionFork
  partitionPersistsWithAgreementFramework
  irelandPartition
  true false false false

canonicalCases : List SuccessorPolityCase
canonicalCases = chinaTaiwanCase ∷ koreaCase ∷ vietnamCase ∷ germanyCase ∷ irelandCase ∷ []

knfPracticeBoundary : KNF.KoreanNaturalFarmingBoundary
knfPracticeBoundary = KNF.canonicalKoreanNaturalFarmingBoundary

data SharedCultureMeansSameState : Set where
data SharedLanguageMeansOnePoliticalIdentity : Set where
data SameForkMeansSameResolution : Set where
data KNFPracticeProvesKoreanPoliticalUnity : Set where

sharedCultureDoesNotMeanSameState : SharedCultureMeansSameState → ⊥
sharedCultureDoesNotMeanSameState ()

sharedLanguageDoesNotMeanOnePoliticalIdentity :
  SharedLanguageMeansOnePoliticalIdentity → ⊥
sharedLanguageDoesNotMeanOnePoliticalIdentity ()

sameForkDoesNotMeanSameResolution : SameForkMeansSameResolution → ⊥
sameForkDoesNotMeanSameResolution ()

knfPracticeDoesNotProveKoreanPoliticalUnity :
  KNFPracticeProvesKoreanPoliticalUnity → ⊥
knfPracticeDoesNotProveKoreanPoliticalUnity ()
