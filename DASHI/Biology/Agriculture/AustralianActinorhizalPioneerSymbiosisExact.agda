module DASHI.Biology.Agriculture.AustralianActinorhizalPioneerSymbiosisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AUSTRALIAN ACTINORHIZAL N-FIXING PIONEER SYMBIOSIS
--
-- Casuarina/Allocasuarina + Frankia supplies an independent biological
-- mechanism for the functional role "N-fixing pioneer".  The role is not
-- identified with legume-rhizobium symbiosis, and source-specific response
-- laws are not transferred between mechanisms.
------------------------------------------------------------------------

flemingEtAl1988DOI : String
flemingEtAl1988DOI = "10.1071/BT9880171"

reddellBowen1985DOI : String
reddellBowen1985DOI = "10.1111/j.1469-8137.1985.tb02763.x"

reddellBowenRobson1985DOI : String
reddellBowenRobson1985DOI = "10.1111/j.1469-8137.1985.tb02850.x"

reddellBowenRobson1985PMID : String
reddellBowenRobson1985PMID = "33874228"

rosbrook1990DOI : String
rosbrook1990DOI = "10.1016/0378-1127(90)90021-3"

flemingWilliamsTurnbull1988 : Attribution.AttributedSource
flemingWilliamsTurnbull1988 = Attribution.mkDOISource
  "A. I. Fleming; E. R. Williams; J. W. Turnbull"
  "Growth and nodulation of provenances of Casuarina cunninghamiana inoculated with a range of Frankia sources"
  "Australian Journal of Botany 36(2):171-181"
  "1988"
  flemingEtAl1988DOI
  "https://doi.org/10.1071/BT9880171"
  Attribution.academicArticleSource
  "Complete glasshouse cross-inoculation across 18 Casuarina cunninghamiana seed provenances and corresponding Frankia/nodule inoculum sources. Seed source, inoculum source and their interaction affected growth; geographically matched combinations were often strongest. This is retained as provenance-by-microsymbiont context evidence, not a universal best-Frankia ranking or field-deployment receipt."
  Attribution.publicAttribution

reddellBowen1985 : Attribution.AttributedSource
reddellBowen1985 = Attribution.mkDOISource
  "Paul Reddell; G. D. Bowen"
  "Frankia source affects growth, nodulation and nitrogen fixation in Casuarina species"
  "New Phytologist 100(1):115-122"
  "1985"
  reddellBowen1985DOI
  "https://doi.org/10.1111/j.1469-8137.1985.tb02763.x"
  Attribution.academicArticleSource
  "Controlled comparison of Casuarina equisetifolia ssp. incana and Casuarina cunninghamiana inoculated with Frankia from five sources. Host species differed in infectivity and growth response, and Frankia sources highly effective on one host could be ineffective on the other. Effectiveness depended on both nodule development and realised N2-fixing ability."
  Attribution.publicAttribution

reddellBowenRobson1985 : Attribution.AttributedSource
reddellBowenRobson1985 = Attribution.mkDOISource
  "Paul Reddell; G. D. Bowen; A. D. Robson"
  "The effects of soil temperature on plant growth, nodulation and nitrogen fixation in Casuarina cunninghamiana Miq."
  "New Phytologist 101(3):441-450"
  "1985"
  reddellBowenRobson1985DOI
  "https://pubmed.ncbi.nlm.nih.gov/33874228/"
  Attribution.academicArticleSource
  "Controlled soil-temperature experiment (15-30 C) on Casuarina cunninghamiana with two Frankia sources. Symbiotic growth was optimal near 25 C; nodulation was delayed at low temperature and nodules formed at 15 C fixed no nitrogen in the reported experiment. Temperature therefore gates realised fixation separately from nodule presence."
  Attribution.publicAttribution

rosbrook1990 : Attribution.AttributedSource
rosbrook1990 = Attribution.mkDOISource
  "P. A. Rosbrook"
  "Effect of inoculum type and placement on nodulation and growth of Casuarina cunninghamiana seedlings"
  "Forest Ecology and Management 36(2-4):135-147"
  "1990"
  rosbrook1990DOI
  "https://doi.org/10.1016/0378-1127(90)90021-3"
  Attribution.academicArticleSource
  "Nursery experiment varying Frankia inoculum type, dose and placement. At low crushed-nodule inoculum levels, placement close to the root system accelerated nodulation and growth response; inoculation method effects changed with inoculum level. Inoculum identity therefore does not erase delivery geometry or dose."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Evidence roles and source-bounded readings.
------------------------------------------------------------------------

data ActinorhizalEvidenceRole : Set where
  hostProvenanceByFrankiaSource : ActinorhizalEvidenceRole
  hostSpeciesByFrankiaSource : ActinorhizalEvidenceRole
  temperatureGatedFixation : ActinorhizalEvidenceRole
  inoculumDeliveryGeometry : ActinorhizalEvidenceRole

record ActinorhizalReceipt : Set where
  constructor actinorhizal-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : ActinorhizalEvidenceRole
    hostReading : String
    symbiontReading : String
    environmentReading : String
    boundedReading : String
open ActinorhizalReceipt public

provenanceFrankiaReceipt : ActinorhizalReceipt
provenanceFrankiaReceipt = actinorhizal-receipt
  flemingWilliamsTurnbull1988
  flemingEtAl1988DOI
  hostProvenanceByFrankiaSource
  "18 Casuarina cunninghamiana seed provenances spanning the species range"
  "multiple Frankia/nodule-inoculum sources"
  "glasshouse cross-inoculation"
  "seed provenance, inoculum source and their interaction remain explicit"

crossSpeciesFrankiaReceipt : ActinorhizalReceipt
crossSpeciesFrankiaReceipt = actinorhizal-receipt
  reddellBowen1985
  reddellBowen1985DOI
  hostSpeciesByFrankiaSource
  "Casuarina equisetifolia ssp. incana and Casuarina cunninghamiana"
  "five Frankia sources"
  "controlled symbiosis experiment"
  "infectivity and N2-fixation effectiveness are host-by-Frankia properties, not Frankia-only labels"

temperatureEnablementReceipt : ActinorhizalReceipt
temperatureEnablementReceipt = actinorhizal-receipt
  reddellBowenRobson1985
  reddellBowenRobson1985DOI
  temperatureGatedFixation
  "Casuarina cunninghamiana seedlings"
  "two Frankia sources"
  "soil temperature 15-30 C"
  "nodule presence and realised N2 fixation separate at low temperature; temperature remains an enablement coordinate"

deliveryGeometryReceipt : ActinorhizalReceipt
deliveryGeometryReceipt = actinorhizal-receipt
  rosbrook1990
  rosbrook1990DOI
  inoculumDeliveryGeometry
  "Casuarina cunninghamiana seedlings"
  "Frankia isolate or crushed-nodule inoculum"
  "nursery dose x placement treatments"
  "inoculum type, dose and root-placement geometry remain separate intervention coordinates"

------------------------------------------------------------------------
-- Functional role != symbiotic mechanism.
------------------------------------------------------------------------

data NFixingPioneerRole : Set where
  nitrogenFixingPioneer : NFixingPioneerRole

data SymbioticMechanism : Set where
  legumeRhizobiumMechanism : SymbioticMechanism
  actinorhizalFrankiaMechanism : SymbioticMechanism

data PioneerSystem : Set where
  australianNativeLegumeSystem : PioneerSystem
  australianCasuarinaSystem : PioneerSystem

pioneerRole : PioneerSystem → NFixingPioneerRole
pioneerRole _ = nitrogenFixingPioneer

pioneerMechanism : PioneerSystem → SymbioticMechanism
pioneerMechanism australianNativeLegumeSystem = legumeRhizobiumMechanism
pioneerMechanism australianCasuarinaSystem = actinorhizalFrankiaMechanism

mechanismNotIdentifiedByRole :
  pioneerMechanism australianNativeLegumeSystem ≡
  pioneerMechanism australianCasuarinaSystem → ⊥
mechanismNotIdentifiedByRole ()

------------------------------------------------------------------------
-- Frankia source/provenance information-loss witness.
------------------------------------------------------------------------

data FrankiaWorld : Set where
  matchedProvenanceFrankia : FrankiaWorld
  mismatchedProvenanceFrankia : FrankiaWorld

data FrankiaTask : Set where
  realisedSymbioticPerformanceTask : FrankiaTask

data FrankiaToken : Set where
  sameFrankiaToken : FrankiaToken

frankiaIdentityOnly : FrankiaWorld → FrankiaToken
frankiaIdentityOnly _ = sameFrankiaToken

realisedSymbioticPerformance : FrankiaTask → FrankiaWorld → Bool
realisedSymbioticPerformance realisedSymbioticPerformanceTask matchedProvenanceFrankia = true
realisedSymbioticPerformance realisedSymbioticPerformanceTask mismatchedProvenanceFrankia = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

frankiaIdentityNotTaskSufficient :
  LES.TaskFactorisation frankiaIdentityOnly realisedSymbioticPerformance → ⊥
frankiaIdentityNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor realisedSymbioticPerformanceTask
      {matchedProvenanceFrankia} {mismatchedProvenanceFrankia} refl)

------------------------------------------------------------------------
-- Existing nitrogenase ladder remains untouched.
------------------------------------------------------------------------

acaciaReactionEnablementStillOpen :
  Chemistry.stageClosed Chemistry.reactionEnablement ≡ false
acaciaReactionEnablementStillOpen = Chemistry.reactionEnablementStillOpen

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record ActinorhizalBoundary : Set where
  constructor actinorhizal-boundary
  field
    sameNFixingPioneerRoleImpliesSameSymbioticMechanism : Bool
    FrankiaIdentityAloneDeterminesPerformance : Bool
    hostProvenanceMayBeDroppedFromFrankiaPerformance : Bool
    hostSpeciesMayBeDroppedFromFrankiaEffectiveness : Bool
    soilTemperatureMayBeDroppedFromSymbioticEnablement : Bool
    nodulePresenceImpliesRealisedNitrogenFixation : Bool
    inoculumDoseAndPlacementMayBeDropped : Bool
    crossInoculationSuccessCreatesFieldDeploymentAuthority : Bool
    actinorhizalEvidenceClosesAcaciaReactionEnablement : Bool
    actinorhizalEvidenceClosesBacterialFixedNFlux : Bool
    sourceExperimentsAreSyntheticDASHIWorlds : Bool
open ActinorhizalBoundary public

canonicalActinorhizalBoundary : ActinorhizalBoundary
canonicalActinorhizalBoundary = actinorhizal-boundary
  false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Fleming, Williams & Turnbull 1988 (DOI 10.1071/BT9880171) owns its Casuarina-cunninghamiana provenance x Frankia-source cross-inoculation propositions. Reddell & Bowen 1985 (DOI 10.1111/j.1469-8137.1985.tb02763.x) owns its Casuarina-species x Frankia-source infectivity/growth/nitrogen-fixation propositions. Reddell, Bowen & Robson 1985 (DOI 10.1111/j.1469-8137.1985.tb02850.x; PMID 33874228) owns its soil-temperature/nodulation/N2-fixation propositions, including nodules with no realised fixation at 15 C in that experiment. Rosbrook 1990 (DOI 10.1016/0378-1127(90)90021-3) owns its inoculum-type/dose/placement nursery propositions. DASHI owns only the functional-role/mechanism separation, synthetic TaskFactorisation collision and no-promotion boundary. Actinorhizal Frankia evidence is not relabelled as legume-rhizobium evidence, does not close the Acacia/Senegalia nitrogenase ladder and does not create field deployment authority."
