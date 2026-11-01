module DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- WOOGAROO NCA s 13 ESSENTIALITY STRESS TEST
--
-- Keeps habitat-function evidence, viable-population nexus and statutory
-- essentiality separate. Carries the strongest supporting and adverse
-- propositions so counsel/ecology can test the actual statutory question.
------------------------------------------------------------------------

data S13Side : Set where
  supportsEssentiality : S13Side
  cutsAgainstEssentiality : S13Side
  unresolvedBridge : S13Side

data S13Status : Set where
  sourcePaid : S13Status
  stronglySupported : S13Status
  open : S13Status

record S13Proposition : Set where
  constructor s13-proposition
  field
    side : S13Side
    status : S13Status
    proposition : String
    sourceRole : String
    relevance : String
    boundary : String

open S13Proposition public

sameParcelHabitatFunction : S13Proposition
sameParcelHabitatFunction = s13-proposition
  supportsEssentiality
  stronglySupported
  "The same Springview project records remnant/native vegetation, recognised Koala food trees, Koala scats, Woogaroo/Opossum Creek connectivity, habitat-connectivity score 2 and a mapped connected habitat landscape greater than 500 ha."
  "Saunders Havill Group / proponent-side ecology"
  "Supports the proposition that the exact project landscape performs real habitat and connectivity functions."
  "Habitat function is necessary evidence but is not identical to statutory essentiality."

fragmentationImportance : S13Proposition
fragmentationImportance = s13-proposition
  supportsEssentiality
  stronglySupported
  "The project ecology anticipates that surrounding development will further fragment habitat and reduce movement opportunities."
  "Saunders Havill Group / proponent-side ecology"
  "Supports a scarcity/connectivity argument: the conservation value of remaining connected habitat can increase as surrounding habitat is lost or fragmented."
  "Projected fragmentation does not by itself identify the relevant viable population or prove essentiality."

significantHabitatLoss : S13Proposition
significantHabitatLoss = s13-proposition
  supportsEssentiality
  stronglySupported
  "The consultant assessed the clearing and functional loss of about 136 ha of habitat score 7 as a significant impact on Koala habitat critical to survival under the federal guideline used at the time."
  "Saunders Havill Group / proponent-side federal ecology assessment"
  "Supports ecological seriousness and irreplaceability concerns relevant to an essentiality assessment."
  "Federal 'critical habitat' terminology and significant-impact reasoning do not equal the Queensland s 13 definition."

recoveryValueZero : S13Proposition
recoveryValueZero = s13-proposition
  cutsAgainstEssentiality
  sourcePaid
  "SHG assigned the site Koala recovery value 0 and argued that roads/urbanisation made the site relatively isolated and not viable to support a Koala population."
  "Saunders Havill Group / proponent-side ecology"
  "This is the strongest identified proposition against an essential-to-viable-population conclusion and must be answered directly."
  "The old federal recovery-value construct is not textually the same as s 13 essentiality and must not be treated as legally dispositive without analysis."

currentKoalaEndangeredStatus : S13Proposition
currentKoalaEndangeredStatus = s13-proposition
  supportsEssentiality
  sourcePaid
  "Koala is currently listed as Endangered in Queensland."
  "Queensland Government conservation-status material"
  "Raises the conservation context and identifies protected wildlife for which viable-population conservation matters."
  "Threatened status alone does not identify a local viable population or make every occupied habitat essential."

viablePopulationIdentity : S13Proposition
viablePopulationIdentity = s13-proposition
  unresolvedBridge
  open
  "The relevant viable protected-wildlife population or community for the s 13 analysis has not yet been precisely identified and source-paid."
  "expert/legal inference"
  "This is the first major bridge from site-level habitat function to statutory essentiality."
  "Do not infer population identity solely from project boundaries, occurrence points or campaign labels."

essentialityBridge : S13Proposition
essentialityBridge = s13-proposition
  unresolvedBridge
  open
  "It remains unproved that loss or severance of this exact habitat would make conservation of the identified viable population/community materially impossible or substantially impaired such that the habitat is 'essential' within s 13."
  "expert/legal inference"
  "This is the statutory core."
  "Connectivity, occupancy, high habitat score and significant impact may support this bridge but none is definitionally equivalent to essentiality."

------------------------------------------------------------------------
-- Stress-test questions: designed for an ecologist/counsel handoff.
------------------------------------------------------------------------

record S13StressTest : Set where
  constructor s13-stress-test
  field
    identifyPopulation : String
    testWithoutSiteCounterfactual : String
    testConnectivityContribution : String
    testAlternativeHabitat : String
    testRecoveryValueZero : String
    testTemporalChangeSince2019 : String
    currentEssentialityEstablished : Bool

currentS13StressTest : S13StressTest
currentS13StressTest = s13-stress-test
  "Define the biologically and legally relevant Koala population/community using evidence independent of the development boundary."
  "Ask what happens to persistence, movement, breeding/dispersal and access to resources if the Springview habitat is removed or functionally severed."
  "Quantify whether Opossum/Woogaroo connectivity is redundant, replaceable or a bottleneck within the surrounding landscape."
  "Identify nearby habitat that could perform the same function now, not merely after future restoration, and test whether barriers/development make it practically substitutable."
  "Reconstruct the factual basis for SHG's recovery-value-0/non-viability conclusion and test it against the same report's >500 ha connectivity finding, later development pressure and current evidence."
  "Update material changes since 2019: surrounding clearing/development, current Koala evidence, corridor condition and any newly protected/degraded areas."
  false

------------------------------------------------------------------------
-- Primary source attribution.
------------------------------------------------------------------------

ncaS13Source : Source.AttributedSource
ncaS13Source = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — section 13"
  "Queensland Legislation — current in-force text"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary statutory source defining critical habitat as habitat essential for conservation of a viable population of protected wildlife or community of native wildlife, including land not presently occupied by the wildlife."
  Source.publicAttribution

koalaStatusSource : Source.AttributedSource
koalaStatusSource = Source.mkNoDOISource
  "Queensland Government"
  "Changes made to wildlife categories on 8 April 2022"
  "Queensland threatened-species conservation-status material"
  "2022"
  "https://www.qld.gov.au/environment/plants-animals/conservation/threatened-species/classes/conservation-status/changes-categories-april-2022"
  Source.governmentSource
  "Official source recording Queensland reclassification of Koala from Vulnerable to Endangered."
  Source.publicAttribution

s13SourceAtlas : Source.AttributedSourceAtlas
s13SourceAtlas = Source.mkSourceAtlas
  "Woogaroo s 13 essentiality stress-test source atlas"
  "DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact"
  (ncaS13Source ∷ koalaStatusSource ∷ [])
  "Project ecology is already attributed in existing Woogaroo owners. These sources do not themselves identify the relevant viable population or prove essentiality."

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data HabitatFunctionEqualsEssentiality : Set where
data FederalCriticalHabitatEqualsNCA13CriticalHabitat : Set where
data EndangeredStatusEqualsEveryHabitatEssential : Set where
data RecoveryValueZeroEqualsNoEssentiality : Set where
data OccupiedHabitatEqualsEssentialHabitat : Set where

habitatFunctionDoesNotEqualEssentiality : HabitatFunctionEqualsEssentiality → ⊥
habitatFunctionDoesNotEqualEssentiality ()

federalLabelDoesNotEqualS13 : FederalCriticalHabitatEqualsNCA13CriticalHabitat → ⊥
federalLabelDoesNotEqualS13 ()

endangeredDoesNotMakeEveryHabitatEssential : EndangeredStatusEqualsEveryHabitatEssential → ⊥
endangeredDoesNotMakeEveryHabitatEssential ()

recoveryValueZeroDoesNotForecloseEssentiality : RecoveryValueZeroEqualsNoEssentiality → ⊥
recoveryValueZeroDoesNotForecloseEssentiality ()

occupancyDoesNotEqualEssentiality : OccupiedHabitatEqualsEssentialHabitat → ⊥
occupancyDoesNotEqualEssentiality ()
