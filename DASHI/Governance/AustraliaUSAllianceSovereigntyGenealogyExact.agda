module DASHI.Governance.AustraliaUSAllianceSovereigntyGenealogyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- AUSTRALIA / U.S. ALLIANCE SOVEREIGNTY GENEALOGY
--
-- The sovereignty debate predates AUKUS.  Historical alliance intimacy,
-- Vietnam-era political identification, present basing/interoperability and
-- contemporary AUKUS dependence claims are distinct coordinates.
------------------------------------------------------------------------

holtNAA : Source.AttributedSource
holtNAA = Source.mkNoDOISource
  "National Archives of Australia"
  "Harold Holt: during office"
  "Australia's Prime Ministers"
  "historical"
  "https://www.naa.gov.au/explore-collection/australias-prime-ministers/harold-holt/during-office"
  Source.governmentSource
  "official historical source for Holt's close relationship with Lyndon Johnson and use of 'All the way with LBJ'"
  Source.publicAttribution

aukUSMarlesABC2023 : Source.AttributedSource
aukUSMarlesABC2023 = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "Defence Minister insists AUKUS will enhance Australia's sovereignty, not dependence on US"
  "ABC News"
  "2023-02-09"
  "https://www.abc.net.au/news/2023-02-09/richard-marles-aukus-sovereignty-united-states-dependence/101947732"
  Source.newsSource
  "records the government's claim that AUKUS enhances sovereignty and critics' opposing dependence argument"
  Source.publicAttribution

hastieABC2026 : Source.AttributedSource
hastieABC2026 = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "The Alliance | Has Australia sold its sovereignty to the US?"
  "ABC Radio National"
  "2026-09-03"
  "https://www.abc.net.au/listen/programs/global-roaming/has-australia-sold-its-sovereignty-to-the-us-andrew-hastie-/107041318"
  Source.newsSource
  "records Andrew Hastie's argument that reliance from Pine Gap to AUKUS has diminished sovereignty while he still regards the U.S. alliance as important"
  Source.publicAttribution

data SovereigntyCoordinate : Set where
  allianceIntimacy : SovereigntyCoordinate
  militaryInteroperability : SovereigntyCoordinate
  basingAndOperationalAccess : SovereigntyCoordinate
  industrialDependence : SovereigntyCoordinate
  commandAutonomy : SovereigntyCoordinate
  foreignPolicyFreedom : SovereigntyCoordinate
  intelligenceInfrastructure : SovereigntyCoordinate

record SovereigntyClaim : Set where
  constructor sovereignty-claim
  field
    coordinate : SovereigntyCoordinate
    claimant : String
    reading : String
    source : Source.AttributedSource
    establishedAsFinalFact : Bool

open SovereigntyClaim public

holtAllianceIntimacy : SovereigntyClaim
holtAllianceIntimacy = sovereignty-claim
  allianceIntimacy
  "historical Holt government"
  "Vietnam-era Australia publicly embraced unusually close U.S. alliance identification."
  holtNAA
  true

marlesEnhancesSovereignty : SovereigntyClaim
marlesEnhancesSovereignty = sovereignty-claim
  industrialDependence
  "Richard Marles / Australian government"
  "AUKUS capability cooperation is presented as enhancing strategic options and sovereignty."
  aukUSMarlesABC2023
  false

hastieDiminishesSovereignty : SovereigntyClaim
hastieDiminishesSovereignty = sovereignty-claim
  foreignPolicyFreedom
  "Andrew Hastie"
  "Deep U.S. reliance from Pine Gap to AUKUS is argued to have diminished Australian sovereignty."
  hastieABC2026
  false

data AllianceIntimacyMeansNoSovereignty : Set where
data ForeignDependenceMeansCompleteSovereigntyLoss : Set where
data GovernmentAssertionClosesSovereigntyDebate : Set where

allianceIntimacyDoesNotDefinitionallyEraseSovereignty :
  AllianceIntimacyMeansNoSovereignty → ⊥
allianceIntimacyDoesNotDefinitionallyEraseSovereignty ()

dependenceDoesNotDefinitionallyMeanCompleteSovereigntyLoss :
  ForeignDependenceMeansCompleteSovereigntyLoss → ⊥
dependenceDoesNotDefinitionallyMeanCompleteSovereigntyLoss ()

governmentAssertionDoesNotCloseSovereigntyDebate :
  GovernmentAssertionClosesSovereigntyDebate → ⊥
governmentAssertionDoesNotCloseSovereigntyDebate ()
