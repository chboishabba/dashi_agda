module DASHI.Wikimedia.IbrahimCannabisTerpeneIdentityInteractionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneEntourageMoleculeCrossPollinationExact as Entourage
import DASHI.Wikimedia.IbrahimCannabisTerpeneChemotypeAssayBiosynthesisParetoExact as Composition
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- CANNABIS / TERPENE IDENTITY + INTERACTION PARETO CONTINUATION
--
-- This tranche closes identity metadata that was intentionally left unresolved
-- or stereochemistry-sensitive in the parent owner, then routes the next
-- experiment through concentration-matched, endpoint-indexed interaction
-- receipts.  It does not promote an umbrella entourage claim.
--
-- molecule identity != occurrence in Cannabis != batch composition !=
-- receptor interaction != synergy != clinical efficacy.
------------------------------------------------------------------------

record RegistryIdentityReceipt : Set where
  constructor registry-identity-receipt
  field
    molecule : Entourage.TerpeneMolecule
    canonicalLabel : String
    molecularFormula : String
    wikidataQid : String
    pubChemCID : String
    registryReading : String
    directLink : String
    stereochemistryScope : String
    identityPaid : Bool
    occurrencePaid : Bool
    mechanismPaid : Bool
open RegistryIdentityReceipt public

myrceneIdentity : RegistryIdentityReceipt
myrceneIdentity = registry-identity-receipt
  Entourage.myrcene "myrcene / beta-myrcene" "C10H16" "Q424577" "31253"
  "Wikidata and PubChem agree on the myrcene identity/formula coordinate."
  "https://pubchem.ncbi.nlm.nih.gov/compound/31253"
  "single parent identity used here; exact sample still requires analytical identity"
  true false false

limoneneRacemateIdentity : RegistryIdentityReceipt
limoneneRacemateIdentity = registry-identity-receipt
  Entourage.limonene "(+-)-limonene / dipentene group coordinate" "C10H16" "Q278809" "22311"
  "Q278809 is a group/racemic coordinate and PubChem CID 22311 is the corresponding non-enantiomer-specific identity."
  "https://www.wikidata.org/wiki/Q278809"
  "do not collapse (+)- and (-)-limonene into this coordinate when an assay resolves enantiomers"
  true false false

alphaPineneIdentity : RegistryIdentityReceipt
alphaPineneIdentity = registry-identity-receipt
  Entourage.alphaPinene "alpha-pinene stereoisomer-group coordinate" "C10H16" "Q27104380" "6654"
  "Wikidata Q27104380 and PubChem CID 6654 identify alpha-pinene at the group/racemic level."
  "https://www.wikidata.org/wiki/Q27104380"
  "individual alpha-pinene enantiomers remain distinct when experimentally resolved"
  true false false

betaPineneIdentity : RegistryIdentityReceipt
betaPineneIdentity = registry-identity-receipt
  Entourage.betaPinene "beta-pinene stereoisomer-group coordinate" "C10H16" "Q300928" "14896"
  "This pays the generic beta-pinene CID that was unresolved in the parent tranche: Wikidata Q300928 records PubChem CID 14896."
  "https://www.wikidata.org/wiki/Q300928"
  "individual beta-pinene enantiomers remain distinct when experimentally resolved"
  true false false

linaloolIdentity : RegistryIdentityReceipt
linaloolIdentity = registry-identity-receipt
  Entourage.linalool "linalool stereoisomer-pair coordinate" "C10H18O" "Q410932" "6549"
  "Wikidata Q410932 and PubChem CID 6549 identify linalool without erasing the underlying stereocentre."
  "https://www.wikidata.org/wiki/Q410932"
  "enantiomeric composition remains a separate sample coordinate"
  true false false

betaCaryophylleneIdentity : RegistryIdentityReceipt
betaCaryophylleneIdentity = registry-identity-receipt
  Entourage.betaCaryophyllene "(-)-beta-caryophyllene / caryophyllene common natural coordinate" "C15H24" "Q421614" "5281515"
  "This pays the QID left unresolved in the parent tranche: Wikidata Q421614 and PubChem CID 5281515 identify the common (-)-beta-caryophyllene coordinate."
  "https://www.wikidata.org/wiki/Q421614"
  "the (+)-beta-caryophyllene stereoisomer has a distinct coordinate and must not be silently merged"
  true false false

------------------------------------------------------------------------
-- Snowball / library coordinates.
------------------------------------------------------------------------

cannabisSativaQid : String
cannabisSativaQid = "Q26726"

terpeneQid : String
terpeneQid = "Q212364"

terpeneDewey : String
terpeneDewey = "547.71"

endocannabinoidSystemQid : String
endocannabinoidSystemQid = "Q368952"

historicalIbrahimCannabisFirstLink : String
historicalIbrahimCannabisFirstLink =
  "unresolved: no historical 2014 FLN Cannabis/terpene edge is promoted by current QIDs, Dewey coordinates or source xlinks"

moleculeOEIS : String
moleculeOEIS = "not applicable: molecule/assay/pharmacology coordinates are not integer-sequence claims"

------------------------------------------------------------------------
-- Source-qualified interaction anchors.
------------------------------------------------------------------------

record InteractionSourceReceipt : Set where
  constructor interaction-source-receipt
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
    primaryExperimental : Bool
open InteractionSourceReceipt public

benShabatSource : InteractionSourceReceipt
benShabatSource = interaction-source-receipt
  "Shimon Ben-Shabat; Ester Fride; Tzviel Sheskin; Tsippy Tamiri; Man-Hee Rhee; Zvi Vogel; Tiziana Bisogno; Luciano De Petrocellis; Vincenzo Di Marzo; Raphael Mechoulam"
  "An entourage effect: inactive endogenous fatty acid glycerol esters enhance 2-arachidonoyl-glycerol cannabinoid activity"
  "European Journal of Pharmacology 353(1):23-31" 1998
  "10.1016/S0014-2999(98)00392-6"
  "https://doi.org/10.1016/S0014-2999(98)00392-6"
  "originating endogenous-lipid entourage experiment"
  "Companion endogenous 2-acyl-glycerols enhanced measured 2-AG activity in the reported assays."
  "Does not establish a phytocannabinoid-terpene cannabis entourage effect or clinical benefit."
  true

russoSource : InteractionSourceReceipt
russoSource = interaction-source-receipt
  "Ethan B. Russo"
  "Taming THC: potential cannabis synergy and phytocannabinoid-terpenoid entourage effects"
  "British Journal of Pharmacology 163(7):1344-1364" 2011
  "10.1111/j.1476-5381.2011.01238.x"
  "https://doi.org/10.1111/j.1476-5381.2011.01238.x"
  "cannabis phytocannabinoid-terpenoid hypothesis/review"
  "Assembles pharmacological observations and proposes testable phytocannabinoid-terpenoid interactions."
  "Review-level synthesis does not pay a specific concentration-matched interaction or clinical synergy."
  false

finlaySource : InteractionSourceReceipt
finlaySource = interaction-source-receipt
  "David B. Finlay; Kathleen J. Sircombe; Mhairi Nimick; Callum Jones; Michelle Glass"
  "Terpenoids From Cannabis Do Not Mediate an Entourage Effect by Acting at Cannabinoid Receptors"
  "Frontiers in Pharmacology 11:359" 2020
  "10.3389/fphar.2020.00359"
  "https://doi.org/10.3389/fphar.2020.00359"
  "mechanism-specific CB1/CB2 interaction test"
  "Primary assays tested myrcene, alpha-pinene, beta-pinene, beta-caryophyllene and limonene, individually and in mixtures, against cannabinoid-receptor binding/signalling conditions."
  "Failure to support direct CB1/CB2 mediation under these conditions does not exclude all pharmacokinetic, receptor-independent or systems-level interactions."
  true

andreSource : InteractionSourceReceipt
andreSource = interaction-source-receipt
  "Rebeca Andre; Ana Patricia Gomes; Catarina Pereira-Leite; Antonio Marques-da-Costa; Luis Monteiro Rodrigues; Michael Sassano; Patricia Rijo; Maria do Ceu Costa"
  "The Entourage Effect in Cannabis Medicinal Products: A Comprehensive Review"
  "Pharmaceuticals 17(11):1543" 2024
  "10.3390/ph17111543"
  "https://doi.org/10.3390/ph17111543"
  "systematic evidence appraisal"
  "PRISMA-organised review states that synergistic or additive enhancement of cannabinoid efficacy by terpenes remains unproven and further clinical trials are required."
  "Review-level uncertainty does not prove that every molecule pair has no interaction."
  false

stokesSource : InteractionSourceReceipt
stokesSource = interaction-source-receipt
  "Claire Stokes; Laura Daley; Janet Hardy"
  "Why does medicinal cannabis remain so popular? Is it the 'entourage effect'?"
  "Internal Medicine Journal, online ahead of print" 2026
  "10.1111/imj.70571"
  "https://doi.org/10.1111/imj.70571"
  "current Australian clinical-evidence caution"
  "The 2026 commentary/review characterises the medicinal-cannabis entourage hypothesis as speculative pending well-designed trials."
  "Commentary is not a primary interaction experiment and does not prove universal absence of molecular interactions."
  false

------------------------------------------------------------------------
-- Finlay mechanism-specific discriminator.
------------------------------------------------------------------------

record ConcentrationMatchedInteractionReceipt : Set where
  constructor concentration-matched-interaction-receipt
  field
    source : InteractionSourceReceipt
    firstCompoundReference : String
    secondCompoundReference : String
    firstConcentrationReference : String
    secondConcentrationReference : String
    receptorOrMechanismReference : String
    endpointReference : String
    comparatorReference : String
    replicationReference : String
    exactMolecularIdentityPaid : Bool
    exactConcentrationPaid : Bool
    endpointPaid : Bool
    matchedComparatorPaid : Bool
    mechanismSpecificConclusionPaid : Bool
    generalEntourageConclusionPaid : Bool
    clinicalEfficacyPaid : Bool
open ConcentrationMatchedInteractionReceipt public

finlayTHCTerpeneCB1Discriminator : ConcentrationMatchedInteractionReceipt
finlayTHCTerpeneCB1Discriminator = concentration-matched-interaction-receipt
  finlaySource
  "Delta-9-THC; exact study reagent identity/purity remains source-bound"
  "one of myrcene / alpha-pinene / beta-pinene / beta-caryophyllene / limonene"
  "approximately EC50 THC condition reported as 3.16 nM for the hCB1 cAMP comparison"
  "10 micromolar terpene"
  "human CB1 receptor assay system"
  "forskolin-stimulated cAMP response, with radioligand-binding context"
  "matched THC condition with versus without the terpene"
  "experiments reported in duplicate and repeated at least three times"
  true true true true true false false

finlayTHCTerpeneCB2Discriminator : ConcentrationMatchedInteractionReceipt
finlayTHCTerpeneCB2Discriminator = concentration-matched-interaction-receipt
  finlaySource
  "Delta-9-THC; exact study reagent identity/purity remains source-bound"
  "one of myrcene / alpha-pinene / beta-pinene / beta-caryophyllene / limonene"
  "approximately EC50 THC condition reported as 30 nM for the hCB2 cAMP comparison"
  "10 micromolar terpene"
  "human CB2 receptor assay system"
  "forskolin-stimulated cAMP response, with radioligand-binding context"
  "matched THC condition with versus without the terpene"
  "experiments reported in duplicate and repeated at least three times"
  true true true true true false false

------------------------------------------------------------------------
-- Same-object bridge from a measured Cannabis batch to an interaction test.
------------------------------------------------------------------------

record BatchToInteractionAdmission : Set where
  constructor batch-to-interaction-admission
  field
    batchAssayReference : String
    terpeneMolecule : Entourage.TerpeneMolecule
    batchConcentrationReference : String
    cannabinoidIdentityReference : String
    cannabinoidConcentrationReference : String
    proposedInteractionEndpointReference : String
    experimentalConcentrationMatchReference : String
    exposureOrBioavailabilityReference : String
    sameObjectCompositionPaid : Bool
    concentrationMatchPaid : Bool
    exposureTranslationPaid : Bool
    clinicalTranslationPaid : Bool
open BatchToInteractionAdmission public

currentBatchToInteractionResidual : BatchToInteractionAdmission
currentBatchToInteractionResidual = batch-to-interaction-admission
  "parent Composition owner requires exact batch assay; no arbitrary strain/cultivar label substitutes for it"
  Entourage.myrcene
  "unpaid exact-batch concentration"
  "unpaid exact cannabinoid identity for the same batch"
  "unpaid exact cannabinoid concentration for the same batch"
  "unpaid mechanism/endpoint selected from the measured composition"
  "unpaid: study concentration must be justified against measured composition/exposure"
  "unpaid pharmacokinetic/exposure bridge"
  false false false false

------------------------------------------------------------------------
-- Pareto frontier.
------------------------------------------------------------------------

data InteractionParetoTarget : Set where
  registryIdentityClosure : InteractionParetoTarget
  exactBatchComposition : InteractionParetoTarget
  concentrationMatchedMechanismTest : InteractionParetoTarget
  exposureTranslation : InteractionParetoTarget
  controlledHumanInteraction : InteractionParetoTarget
  umbrellaEntourageClaim : InteractionParetoTarget
  historicalIbrahimReplay : InteractionParetoTarget

record InteractionParetoStep : Set where
  constructor interaction-pareto-step
  field
    priority : Nat
    target : InteractionParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open InteractionParetoStep public

identityStep : InteractionParetoStep
identityStep = interaction-pareto-step
  0 registryIdentityClosure
  "use stereochemistry-aware Wikidata/PubChem coordinates; beta-pinene CID 14896 and beta-caryophyllene Q421614 are now paid"
  "exact molecule navigation/registry identity"
  "none"

batchStep : InteractionParetoStep
batchStep = interaction-pareto-step
  1 exactBatchComposition
  "acquire one same-object Cannabis batch/sample assay with cannabinoid and terpene concentrations, units, calibration and custody"
  "composition actually presented to downstream interaction reasoning"
  "molecule identity alone does not pay occurrence or abundance"

mechanismStep : InteractionParetoStep
mechanismStep = interaction-pareto-step
  2 concentrationMatchedMechanismTest
  "select pair/mixture and endpoint from the measured batch, then test matched concentrations against an explicit additive/null comparator"
  "mechanism-specific interaction or non-interaction result"
  "exact batch composition and assay semantics required first"

exposureStep : InteractionParetoStep
exposureStep = interaction-pareto-step
  3 exposureTranslation
  "justify in-vitro or ex-vivo concentrations against route, absorption, tissue exposure and time course"
  "closes the concentration-to-exposure WrongType gap"
  "mechanism test alone cannot pay human exposure"

humanStep : InteractionParetoStep
humanStep = interaction-pareto-step
  4 controlledHumanInteraction
  "test a preregistered constituent interaction with composition-controlled products and an interaction contrast rather than whole-product anecdotes"
  "human interaction evidence"
  "preclinical interaction and product preference are insufficient"

umbrellaStep : InteractionParetoStep
umbrellaStep = interaction-pareto-step
  9 umbrellaEntourageClaim
  "promote no broad medicinal-cannabis entourage claim without replicated constituent-specific and clinical receipts"
  "nothing at current evidence state"
  "dominated by exact pairwise, exposure and controlled-human payments"

historicalStep : InteractionParetoStep
historicalStep = interaction-pareto-step
  10 historicalIbrahimReplay
  "if a Cannabis/terpene first-link claim matters, replay it through the existing 2014 dump/parser archaeology rather than projecting present QIDs or source xlinks backwards"
  "historical FLN coordinate only"
  "current semantic/dependency graph is not historical Wikipedia state"

------------------------------------------------------------------------
-- Time-indexed evidence state: sources refine mechanism-specific hypotheses
-- without rewriting prior publications.
------------------------------------------------------------------------

data InteractionTime : Set where
  endogenous1998 : InteractionTime
  cb2Specific2008 : InteractionTime
  cannabisHypothesis2011 : InteractionTime
  receptorTest2020 : InteractionTime
  review2024 : InteractionTime
  caution2026 : InteractionTime
  currentDashi : InteractionTime

data InteractionInterpretation : Set where
  endogenousEntourageSourcePaid : InteractionInterpretation
  phytocannabinoidTerpeneHypothesisLive : InteractionInterpretation
  directCB1CB2UmbrellaMechanismLive : InteractionInterpretation
  betaCaryophylleneSpecificCB2MechanismLive : InteractionInterpretation
  stableClinicalEntouragePaid : InteractionInterpretation
  constituentSpecificTestingStillRequired : InteractionInterpretation

data InteractionSummary : Set where
  mechanismSpecificMixedEvidence : InteractionSummary

InteractionCompatible : InteractionTime → InteractionInterpretation → Set
InteractionCompatible endogenous1998 endogenousEntourageSourcePaid = ⊤
InteractionCompatible endogenous1998 phytocannabinoidTerpeneHypothesisLive = ⊥
InteractionCompatible endogenous1998 directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible endogenous1998 betaCaryophylleneSpecificCB2MechanismLive = ⊥
InteractionCompatible endogenous1998 stableClinicalEntouragePaid = ⊥
InteractionCompatible endogenous1998 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible cb2Specific2008 endogenousEntourageSourcePaid = ⊤
InteractionCompatible cb2Specific2008 phytocannabinoidTerpeneHypothesisLive = ⊥
InteractionCompatible cb2Specific2008 directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible cb2Specific2008 betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible cb2Specific2008 stableClinicalEntouragePaid = ⊥
InteractionCompatible cb2Specific2008 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible cannabisHypothesis2011 endogenousEntourageSourcePaid = ⊤
InteractionCompatible cannabisHypothesis2011 phytocannabinoidTerpeneHypothesisLive = ⊤
InteractionCompatible cannabisHypothesis2011 directCB1CB2UmbrellaMechanismLive = ⊤
InteractionCompatible cannabisHypothesis2011 betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible cannabisHypothesis2011 stableClinicalEntouragePaid = ⊥
InteractionCompatible cannabisHypothesis2011 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible receptorTest2020 endogenousEntourageSourcePaid = ⊤
InteractionCompatible receptorTest2020 phytocannabinoidTerpeneHypothesisLive = ⊤
InteractionCompatible receptorTest2020 directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible receptorTest2020 betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible receptorTest2020 stableClinicalEntouragePaid = ⊥
InteractionCompatible receptorTest2020 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible review2024 endogenousEntourageSourcePaid = ⊤
InteractionCompatible review2024 phytocannabinoidTerpeneHypothesisLive = ⊤
InteractionCompatible review2024 directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible review2024 betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible review2024 stableClinicalEntouragePaid = ⊥
InteractionCompatible review2024 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible caution2026 endogenousEntourageSourcePaid = ⊤
InteractionCompatible caution2026 phytocannabinoidTerpeneHypothesisLive = ⊤
InteractionCompatible caution2026 directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible caution2026 betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible caution2026 stableClinicalEntouragePaid = ⊥
InteractionCompatible caution2026 constituentSpecificTestingStillRequired = ⊤
InteractionCompatible currentDashi endogenousEntourageSourcePaid = ⊤
InteractionCompatible currentDashi phytocannabinoidTerpeneHypothesisLive = ⊤
InteractionCompatible currentDashi directCB1CB2UmbrellaMechanismLive = ⊥
InteractionCompatible currentDashi betaCaryophylleneSpecificCB2MechanismLive = ⊤
InteractionCompatible currentDashi stableClinicalEntouragePaid = ⊥
InteractionCompatible currentDashi constituentSpecificTestingStillRequired = ⊤

interactionTemporalSystem : Temporal.TemporalEvidenceSystem
interactionTemporalSystem = record
  { Time = InteractionTime
  ; Interpretation = InteractionInterpretation
  ; Compatible = InteractionCompatible
  ; Summary = InteractionSummary
  ; summarize = λ _ → mechanismSpecificMixedEvidence
  ; timeReference = λ
      { endogenous1998 → "Ben-Shabat et al. 1998 DOI 10.1016/S0014-2999(98)00392-6"
      ; cb2Specific2008 → "Gertsch et al. 2008 DOI 10.1073/pnas.0803601105"
      ; cannabisHypothesis2011 → "Russo 2011 DOI 10.1111/j.1476-5381.2011.01238.x"
      ; receptorTest2020 → "Finlay et al. 2020 DOI 10.3389/fphar.2020.00359"
      ; review2024 → "Andre et al. 2024 DOI 10.3390/ph17111543"
      ; caution2026 → "Stokes, Daley, Hardy 2026 DOI 10.1111/imj.70571"
      ; currentDashi → "current DASHI constituent-specific entourage frontier"
      }
  }

currentConstituentSpecificTestingRequired :
  Temporal.EvidenceFibre interactionTemporalSystem currentDashi
currentConstituentSpecificTestingRequired =
  Temporal.liveInterpretationAt constituentSpecificTestingStillRequired tt

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data RegistryIdentityCreatesOccurrence : Set where
data CannabisOccurrenceCreatesSynergy : Set where
data SameBatchCreatesInteraction : Set where
data ReceptorNegativeTestCreatesUniversalNull : Set where
data BetaCaryophylleneCB2CreatesEntourage : Set where
data ReviewHypothesisCreatesClinicalEfficacy : Set where
data CurrentQidCreatesHistoricalIbrahimEdge : Set where
data InVitroConcentrationCreatesHumanExposure : Set where

registryIdentityDoesNotCreateOccurrence : RegistryIdentityCreatesOccurrence → ⊥
registryIdentityDoesNotCreateOccurrence ()

cannabisOccurrenceDoesNotCreateSynergy : CannabisOccurrenceCreatesSynergy → ⊥
cannabisOccurrenceDoesNotCreateSynergy ()

sameBatchDoesNotCreateInteraction : SameBatchCreatesInteraction → ⊥
sameBatchDoesNotCreateInteraction ()

receptorNegativeDoesNotCreateUniversalNull : ReceptorNegativeTestCreatesUniversalNull → ⊥
receptorNegativeDoesNotCreateUniversalNull ()

betaCaryophylleneCB2DoesNotCreateEntourage : BetaCaryophylleneCB2CreatesEntourage → ⊥
betaCaryophylleneCB2DoesNotCreateEntourage ()

reviewHypothesisDoesNotCreateClinicalEfficacy : ReviewHypothesisCreatesClinicalEfficacy → ⊥
reviewHypothesisDoesNotCreateClinicalEfficacy ()

currentQidDoesNotCreateHistoricalIbrahimEdge : CurrentQidCreatesHistoricalIbrahimEdge → ⊥
currentQidDoesNotCreateHistoricalIbrahimEdge ()

inVitroConcentrationDoesNotCreateHumanExposure : InVitroConcentrationCreatesHumanExposure → ⊥
inVitroConcentrationDoesNotCreateHumanExposure ()

record CannabisTerpeneIdentityInteractionBoundary : Set where
  constructor cannabis-terpene-identity-interaction-boundary
  field
    parentEntourageOwnerReused : Bool
    parentCompositionOwnerReused : Bool
    correctedRegistryCoordinatesRetained : Bool
    stereochemistryRetained : Bool
    primarySourceRolesRetained : Bool
    mechanismSpecificNegativeEvidenceBounded : Bool
    exactBatchBeforeInteraction : Bool
    exposureBeforeClinicalTranslation : Bool
    currentXlinksRemainNonHistorical : Bool
    umbrellaEntourageCurrentlyPromoted : Bool
open CannabisTerpeneIdentityInteractionBoundary public

canonicalCannabisTerpeneIdentityInteractionBoundary :
  CannabisTerpeneIdentityInteractionBoundary
canonicalCannabisTerpeneIdentityInteractionBoundary =
  cannabis-terpene-identity-interaction-boundary
    true true true true true true true true true false
