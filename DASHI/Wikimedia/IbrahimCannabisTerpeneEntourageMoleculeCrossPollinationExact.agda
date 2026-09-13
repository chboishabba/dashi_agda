module DASHI.Wikimedia.IbrahimCannabisTerpeneEntourageMoleculeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.NeurochemicalVocabularyReceipt as Neuro
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Wikimedia.IbrahimOracleCrossDomainFibreCrossPollinationExact as Cross

------------------------------------------------------------------------
-- IBRAHIM / CANNABIS / TERPENE / ENTOURAGE-EFFECT CROSS-POLLINATION
--
-- This is a thin source-and-evidence bridge over existing DASHI candidate and
-- temporal-fibre machinery.  It does not create a new pharmacology ontology.
--
-- Molecule identity != cannabis occurrence != exact batch composition !=
-- receptor interaction != pharmacodynamic synergy != clinical efficacy.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Existing repo donor.
------------------------------------------------------------------------

endocannabinoidCandidateReference : String
endocannabinoidCandidateReference =
  "DASHI.Biology.NeurochemicalVocabularyReceipt.endocannabinoidCandidate"

endocannabinoidCandidateStillNonPromoting : Bool
endocannabinoidCandidateStillNonPromoting = true

------------------------------------------------------------------------
-- Semantic / library coordinates for the snowball graph.
------------------------------------------------------------------------

cannabisSativaQid : String
cannabisSativaQid = "Q26726"

terpeneQid : String
terpeneQid = "Q212364"

terpeneDewey : String
terpeneDewey = "547.71"

endocannabinoidSystemQid : String
endocannabinoidSystemQid = "Q368952"

entourageEffectQid : String
entourageEffectQid =
  "unresolved: no safely inspected dedicated Wikidata item promoted in this tranche"

cannabisSativaDewey : String
cannabisSativaDewey = "unresolved"

endocannabinoidSystemDewey : String
endocannabinoidSystemDewey = "unresolved"

chemistryOEIS : String
chemistryOEIS = "not applicable: these are molecular/pharmacological identities, not integer-sequence claims"

------------------------------------------------------------------------
-- Common terpene molecule coordinates.
------------------------------------------------------------------------

data TerpeneMolecule : Set where
  myrcene
  limonene
  alphaPinene
  betaPinene
  linalool
  betaCaryophyllene : TerpeneMolecule

record MoleculeCoordinate : Set where
  constructor molecule-coordinate
  field
    molecule : TerpeneMolecule
    canonicalLabel : String
    molecularFormula : String
    pubChemCID : String
    wikidataQid : String
    wikidataResolution : String
    structuralClass : String
    sourceLink : String
    qidCreatesMolecularMechanism : Bool
    moleculeIdentityCreatesCannabisOccurrence : Bool
open MoleculeCoordinate public

myrceneCoordinate : MoleculeCoordinate
myrceneCoordinate = molecule-coordinate
  myrcene "myrcene / beta-myrcene" "C10H16" "31253" "Q424577"
  "verified current Wikidata identity; PubChem CID and formula separately inspected"
  "monoterpene"
  "https://pubchem.ncbi.nlm.nih.gov/compound/Myrcene"
  false false

limoneneCoordinate : MoleculeCoordinate
limoneneCoordinate = molecule-coordinate
  limonene "limonene (stereochemistry must remain explicit per sample)" "C10H16"
  "stereoisomer-specific; (+)-limonene CID 440917 and (-)-limonene CID 439250 inspected"
  "Q278809"
  "verified present Wikidata racemic/group coordinate; enantiomer identity must not be erased"
  "monoterpene"
  "https://www.wikidata.org/wiki/Q278809"
  false false

alphaPineneCoordinate : MoleculeCoordinate
alphaPineneCoordinate = molecule-coordinate
  alphaPinene "alpha-pinene (stereochemistry must remain explicit per sample)" "C10H16" "6654"
  "Q27104380"
  "verified present Wikidata alpha-pinene stereoisomer-group coordinate; individual enantiomer QIDs also exist"
  "bicyclic monoterpene"
  "https://pubchem.ncbi.nlm.nih.gov/compound/alpha-pinene"
  false false

betaPineneCoordinate : MoleculeCoordinate
betaPineneCoordinate = molecule-coordinate
  betaPinene "beta-pinene (stereochemistry must remain explicit per sample)" "C10H16"
  "unresolved generic CID in this tranche; (-)-beta-pinene CID 440967 is source-visible"
  "Q300928"
  "verified present Wikidata stereoisomer-group coordinate"
  "bicyclic monoterpene"
  "https://www.wikidata.org/wiki/Q300928"
  false false

linaloolCoordinate : MoleculeCoordinate
linaloolCoordinate = molecule-coordinate
  linalool "linalool (enantiomeric composition may matter)" "C10H18O" "6549" "Q410932"
  "verified current Wikidata stereoisomer-pair coordinate and PubChem formula/CID"
  "monoterpenoid alcohol"
  "https://pubchem.ncbi.nlm.nih.gov/compound/Linalool"
  false false

betaCaryophylleneCoordinate : MoleculeCoordinate
betaCaryophylleneCoordinate = molecule-coordinate
  betaCaryophyllene "beta-caryophyllene; common natural (-)-form must be distinguished from (+)-form"
  "C15H24" "5281515 for (-)-beta-caryophyllene" "unresolved"
  "Wikidata QID deliberately unresolved in this tranche; PubChem identity/formula inspected"
  "sesquiterpene"
  "https://pubchem.ncbi.nlm.nih.gov/compound/beta-Caryophyllene"
  false false

------------------------------------------------------------------------
-- Source roles.  The same word 'entourage' names distinct claim classes.
------------------------------------------------------------------------

data EntourageSourceRole : Set where
  originalEndocannabinoidPotentiation
  cannabisTerpenoidSynergyHypothesisReview
  receptorMechanismNegativeTest
  betaCaryophylleneCB2Mechanism
  systematicEvidenceAppraisal
  currentClinicalCaution : EntourageSourceRole

record EntourageSource : Set where
  constructor entourage-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    role : EntourageSourceRole
    boundedReading : String
    excludedPromotion : String
    primaryExperimentalSource : Bool
open EntourageSource public

benShabat1998 : EntourageSource
benShabat1998 = entourage-source
  "Shimon Ben-Shabat; Ester Fride; Tzviel Sheskin; Tsippy Tamiri; Man-Hee Rhee; Zvi Vogel; Tiziana Bisogno; Luciano De Petrocellis; Vincenzo Di Marzo; Raphael Mechoulam"
  "An entourage effect: inactive endogenous fatty acid glycerol esters enhance 2-arachidonoyl-glycerol cannabinoid activity"
  "European Journal of Pharmacology 353(1):23-31"
  1998 "10.1016/S0014-2999(98)00392-6"
  "https://doi.org/10.1016/S0014-2999(98)00392-6"
  originalEndocannabinoidPotentiation
  "Primary experimental source: companion endogenous 2-acyl-glycerols potentiated measured 2-AG activity in the assays reported."
  "Does not establish phytocannabinoid-terpene synergy, cannabis whole-plant superiority, or clinical efficacy."
  true

russo2011 : EntourageSource
russo2011 = entourage-source
  "Ethan B. Russo"
  "Taming THC: potential cannabis synergy and phytocannabinoid-terpenoid entourage effects"
  "British Journal of Pharmacology 163(7):1344-1364"
  2011 "10.1111/j.1476-5381.2011.01238.x"
  "https://doi.org/10.1111/j.1476-5381.2011.01238.x"
  cannabisTerpenoidSynergyHypothesisReview
  "Review that assembles pharmacological observations and proposes testable phytocannabinoid-terpenoid synergy; it names limonene, myrcene, alpha-pinene, linalool and beta-caryophyllene among cannabis terpenoids of interest."
  "A review/hypothesis does not pay a specific terpene-cannabinoid interaction, exact product composition, clinical synergy or therapeutic superiority."
  false

finlay2020 : EntourageSource
finlay2020 = entourage-source
  "David B. Finlay; Kathleen J. Sircombe; Mhairi Nimick; Callum Jones; Michelle Glass"
  "Terpenoids From Cannabis Do Not Mediate an Entourage Effect by Acting at Cannabinoid Receptors"
  "Frontiers in Pharmacology 11:359"
  2020 "10.3389/fphar.2020.00359"
  "https://doi.org/10.3389/fphar.2020.00359"
  receptorMechanismNegativeTest
  "Primary receptor-binding/signalling experiment: myrcene, alpha-pinene, beta-pinene, beta-caryophyllene and limonene did not support direct CB1/CB2 entourage mediation under the tested conditions, apart from a weak beta-caryophyllene/CB2 interaction."
  "Negative CB1/CB2 results do not prove no entourage effect by any other molecular, pharmacokinetic or systems mechanism."
  true

gertsch2008 : EntourageSource
gertsch2008 = entourage-source
  "Jurg Gertsch; Marco Leonti; Stefan Raduner; Ildiko Racz; Jian-Zhong Chen; Xiang-Qun Xie; Karl-Heinz Altmann; Meliha Karsak; Andreas Zimmer"
  "Beta-caryophyllene is a dietary cannabinoid"
  "Proceedings of the National Academy of Sciences 105(26):9099-9104"
  2008 "10.1073/pnas.0803601105"
  "https://doi.org/10.1073/pnas.0803601105"
  betaCaryophylleneCB2Mechanism
  "Primary mechanistic source reporting beta-caryophyllene as a selective CB2-ligand/agonist context."
  "One molecule-target result does not establish the cannabis entourage hypothesis or clinical synergy with THC/CBD."
  true

andre2024 : EntourageSource
andre2024 = entourage-source
  "Rebeca Andre; Ana Patricia Gomes; Catarina Pereira-Leite; Antonio Marques-da-Costa; Luis Monteiro Rodrigues; Michael Sassano; Patricia Rijo; Maria do Ceu Costa"
  "The Entourage Effect in Cannabis Medicinal Products: A Comprehensive Review"
  "Pharmaceuticals 17(11):1543"
  2024 "10.3390/ph17111543"
  "https://doi.org/10.3390/ph17111543"
  systematicEvidenceAppraisal
  "PRISMA-organised literature review concluding that terpene-cannabinoid synergistic/additive enhancement remains unproven and requires further clinical trials."
  "Review-level appraisal does not prove that every proposed molecular interaction is absent."
  false

stokes2026 : EntourageSource
stokes2026 = entourage-source
  "Claire Stokes et al."
  "Why does medicinal cannabis remain so popular? Is it the 'entourage effect'?"
  "Internal Medicine Journal"
  2026 "10.1111/imj.70571"
  "https://doi.org/10.1111/imj.70571"
  currentClinicalCaution
  "Current Australian commentary/review characterises whole-plant entourage claims as speculative pending well-designed trials."
  "Commentary does not replace primary mechanistic experiments or prove universal absence of interactions."
  false

------------------------------------------------------------------------
-- Same-object composition / assay gate.
------------------------------------------------------------------------

record CannabisTerpeneAssayReceipt : Set where
  constructor cannabis-terpene-assay-receipt
  field
    cannabisObjectReference : String
    taxonOrProductReference : String
    cultivarOrChemovarReference : String
    lotBatchOrSampleReference : String
    harvestProcessingReference : String
    assayMethodReference : String
    molecule : TerpeneMolecule
    stereochemicalIdentityReference : String
    concentrationReference : String
    concentrationUnitReference : String
    detectionLimitReference : String
    calibrationReference : String
    sameObjectSamplePaid : Bool
    molecularIdentityPaid : Bool
    quantitativeCompositionPaid : Bool
open CannabisTerpeneAssayReceipt public

------------------------------------------------------------------------
-- Interaction evidence is endpoint- and mechanism-indexed.
------------------------------------------------------------------------

data EntourageEvidenceLevel : Set where
  terminologyOnly
  moleculeActivityElsewhere
  cannabisCoOccurrence
  pairwisePreclinicalInteraction
  receptorSpecificInteraction
  humanPKPDInteraction
  controlledClinicalSynergy
  replicatedClinicalSynergy : EntourageEvidenceLevel

record InteractionReceipt : Set where
  constructor interaction-receipt
  field
    firstCompoundReference : String
    secondCompoundReference : String
    exactConcentrationsReference : String
    assayOrStudyReference : String
    endpointReference : String
    comparatorReference : String
    interactionModelReference : String
    level : EntourageEvidenceLevel
    additiveAlternativeExcluded : Bool
    pharmacokineticAlternativeExcluded : Bool
    receptorMechanismPaid : Bool
    humanEvidencePaid : Bool
    clinicalSynergyPaid : Bool
open InteractionReceipt public

------------------------------------------------------------------------
-- Evidence fibre over time.
------------------------------------------------------------------------

data EntourageTime : Set where
  endogenous1998
  cannabisHypothesis2011
  cb2Mechanism2008
  receptorTest2020
  systematicReview2024
  current2026 : EntourageTime

data EntourageInterpretation : Set where
  endogenousEntourageObserved
  phytocannabinoidTerpenoidSynergyCandidate
  cb1cb2DirectTerpeneMechanismCandidate
  betaCaryophylleneSpecificCB2Candidate
  stableClinicalEntourageEstablished
  umbrellaHypothesisStillOpen : EntourageInterpretation

data EntourageSummary : Set where
  entourageEvidenceMixedMechanismSpecific : EntourageSummary

EntourageCompatible : EntourageTime → EntourageInterpretation → Set
EntourageCompatible endogenous1998 endogenousEntourageObserved = ⊤
EntourageCompatible endogenous1998 phytocannabinoidTerpenoidSynergyCandidate = ⊥
EntourageCompatible endogenous1998 cb1cb2DirectTerpeneMechanismCandidate = ⊥
EntourageCompatible endogenous1998 betaCaryophylleneSpecificCB2Candidate = ⊥
EntourageCompatible endogenous1998 stableClinicalEntourageEstablished = ⊥
EntourageCompatible endogenous1998 umbrellaHypothesisStillOpen = ⊤

EntourageCompatible cannabisHypothesis2011 endogenousEntourageObserved = ⊤
EntourageCompatible cannabisHypothesis2011 phytocannabinoidTerpenoidSynergyCandidate = ⊤
EntourageCompatible cannabisHypothesis2011 cb1cb2DirectTerpeneMechanismCandidate = ⊤
EntourageCompatible cannabisHypothesis2011 betaCaryophylleneSpecificCB2Candidate = ⊤
EntourageCompatible cannabisHypothesis2011 stableClinicalEntourageEstablished = ⊥
EntourageCompatible cannabisHypothesis2011 umbrellaHypothesisStillOpen = ⊤

EntourageCompatible cb2Mechanism2008 endogenousEntourageObserved = ⊤
EntourageCompatible cb2Mechanism2008 phytocannabinoidTerpenoidSynergyCandidate = ⊥
EntourageCompatible cb2Mechanism2008 cb1cb2DirectTerpeneMechanismCandidate = ⊥
EntourageCompatible cb2Mechanism2008 betaCaryophylleneSpecificCB2Candidate = ⊤
EntourageCompatible cb2Mechanism2008 stableClinicalEntourageEstablished = ⊥
EntourageCompatible cb2Mechanism2008 umbrellaHypothesisStillOpen = ⊤

EntourageCompatible receptorTest2020 endogenousEntourageObserved = ⊤
EntourageCompatible receptorTest2020 phytocannabinoidTerpenoidSynergyCandidate = ⊤
EntourageCompatible receptorTest2020 cb1cb2DirectTerpeneMechanismCandidate = ⊥
EntourageCompatible receptorTest2020 betaCaryophylleneSpecificCB2Candidate = ⊤
EntourageCompatible receptorTest2020 stableClinicalEntourageEstablished = ⊥
EntourageCompatible receptorTest2020 umbrellaHypothesisStillOpen = ⊤

EntourageCompatible systematicReview2024 endogenousEntourageObserved = ⊤
EntourageCompatible systematicReview2024 phytocannabinoidTerpenoidSynergyCandidate = ⊤
EntourageCompatible systematicReview2024 cb1cb2DirectTerpeneMechanismCandidate = ⊥
EntourageCompatible systematicReview2024 betaCaryophylleneSpecificCB2Candidate = ⊤
EntourageCompatible systematicReview2024 stableClinicalEntourageEstablished = ⊥
EntourageCompatible systematicReview2024 umbrellaHypothesisStillOpen = ⊤

EntourageCompatible current2026 endogenousEntourageObserved = ⊤
EntourageCompatible current2026 phytocannabinoidTerpenoidSynergyCandidate = ⊤
EntourageCompatible current2026 cb1cb2DirectTerpeneMechanismCandidate = ⊥
EntourageCompatible current2026 betaCaryophylleneSpecificCB2Candidate = ⊤
EntourageCompatible current2026 stableClinicalEntourageEstablished = ⊥
EntourageCompatible current2026 umbrellaHypothesisStillOpen = ⊤

entourageTemporalSystem : Temporal.TemporalEvidenceSystem
entourageTemporalSystem = record
  { Time = EntourageTime
  ; Interpretation = EntourageInterpretation
  ; Compatible = EntourageCompatible
  ; Summary = EntourageSummary
  ; summarize = λ _ → entourageEvidenceMixedMechanismSpecific
  ; timeReference = λ
      { endogenous1998 → "Ben-Shabat et al. 1998, DOI 10.1016/S0014-2999(98)00392-6"
      ; cannabisHypothesis2011 → "Russo 2011, DOI 10.1111/j.1476-5381.2011.01238.x"
      ; cb2Mechanism2008 → "Gertsch et al. 2008, DOI 10.1073/pnas.0803601105"
      ; receptorTest2020 → "Finlay et al. 2020, DOI 10.3389/fphar.2020.00359"
      ; systematicReview2024 → "Andre et al. 2024, DOI 10.3390/ph17111543"
      ; current2026 → "Stokes et al. 2026, DOI 10.1111/imj.70571; current evidence-appraisal coordinate"
      }
  }

currentUmbrellaHypothesisOpen : Temporal.EvidenceFibre entourageTemporalSystem current2026
currentUmbrellaHypothesisOpen = Temporal.liveInterpretationAt umbrellaHypothesisStillOpen tt

currentClinicalSynergyNotPaid : EntourageCompatible current2026 stableClinicalEntourageEstablished → ⊥
currentClinicalSynergyNotPaid ()

currentDirectCB1CB2TerpeneMechanismNotLive :
  EntourageCompatible current2026 cb1cb2DirectTerpeneMechanismCandidate → ⊥
currentDirectCB1CB2TerpeneMechanismNotLive ()

------------------------------------------------------------------------
-- Ibrahim / Dewey / QID cross-linking.
--
-- These are present semantic/source-driven xlinks.  They are NOT historical
-- first-link edges from the Ibrahim 2014 corpus unless separately replayed.
------------------------------------------------------------------------

data XLinkRole : Set where
  repoCandidateToExternalIdentity
  plantToChemicalClass
  chemicalClassToMolecule
  moleculeToMechanismSource
  mechanismToEvidenceAppraisal : XLinkRole

record IbrahimXLink : Set where
  constructor ibrahim-xlink
  field
    fromLabel : String
    fromQid : String
    toLabel : String
    toQid : String
    role : XLinkRole
    sourceReference : String
    sourceLink : String
    historicalFirstLinkPaid : Bool
    currentWikipediaFirstLinkPaid : Bool
    semanticCrossLinkPaid : Bool
open IbrahimXLink public

endocannabinoidToSystemXLink : IbrahimXLink
endocannabinoidToSystemXLink = ibrahim-xlink
  "repo endocannabinoid candidate" "unresolved candidate-row identity"
  "endocannabinoid system" "Q368952"
  repoCandidateToExternalIdentity
  endocannabinoidCandidateReference
  "https://www.wikidata.org/wiki/Q368952"
  false false true

cannabisToTerpeneXLink : IbrahimXLink
cannabisToTerpeneXLink = ibrahim-xlink
  "Cannabis sativa" "Q26726" "terpene" "Q212364"
  plantToChemicalClass
  "Russo 2011 source-level cannabis-terpenoid relationship; current semantic cross-link only"
  "https://doi.org/10.1111/j.1476-5381.2011.01238.x"
  false false true

terpeneToMyrceneXLink : IbrahimXLink
terpeneToMyrceneXLink = ibrahim-xlink
  "terpene" "Q212364" "myrcene" "Q424577"
  chemicalClassToMolecule
  "PubChem/Wikidata molecule identity plus Russo 2011 cannabis-terpenoid review"
  "https://pubchem.ncbi.nlm.nih.gov/compound/Myrcene"
  false false true

terpeneToLinaloolXLink : IbrahimXLink
terpeneToLinaloolXLink = ibrahim-xlink
  "terpene" "Q212364" "linalool" "Q410932"
  chemicalClassToMolecule
  "PubChem/Wikidata molecule identity plus Russo 2011 cannabis-terpenoid review"
  "https://pubchem.ncbi.nlm.nih.gov/compound/Linalool"
  false false true

betaCaryophylleneToCB2SourceXLink : IbrahimXLink
betaCaryophylleneToCB2SourceXLink = ibrahim-xlink
  "beta-caryophyllene" "unresolved Wikidata QID" "CB2-specific mechanism source" "not a QID edge"
  moleculeToMechanismSource
  "Gertsch et al. 2008"
  "https://doi.org/10.1073/pnas.0803601105"
  false false true

mechanismToReviewXLink : IbrahimXLink
mechanismToReviewXLink = ibrahim-xlink
  "putative cannabis terpene entourage mechanisms" "not one entity"
  "2024 systematic evidence appraisal" "not one QID"
  mechanismToEvidenceAppraisal
  "Andre et al. 2024"
  "https://doi.org/10.3390/ph17111543"
  false false true

------------------------------------------------------------------------
-- Pareto routing.
------------------------------------------------------------------------

data CannabisTerpeneTarget : Set where
  exactMoleculeIdentity
  exactSampleComposition
  mechanismSpecificInteraction
  humanPKPDInteraction
  controlledClinicalSynergy
  historicalIbrahimReplay : CannabisTerpeneTarget

record CannabisTerpeneParetoStep : Set where
  constructor cannabis-terpene-pareto-step
  field
    priority : Nat
    target : CannabisTerpeneTarget
    action : String
    pays : String
    dominatedUntil : String
open CannabisTerpeneParetoStep public

firstParetoStep : CannabisTerpeneParetoStep
firstParetoStep = cannabis-terpene-pareto-step
  0 exactMoleculeIdentity
  "retain stereochemistry-aware molecule identities, formulae and stable external identifiers for the common terpenes"
  "prevents generic aroma/strain labels from substituting for molecule identity"
  "none"

secondParetoStep : CannabisTerpeneParetoStep
secondParetoStep = cannabis-terpene-pareto-step
  1 exactSampleComposition
  "bind one exact cannabis sample/batch to quantitative terpene assay receipts"
  "same-object occurrence and concentration; separates molecule existence from product composition"
  "molecule identity first"

thirdParetoStep : CannabisTerpeneParetoStep
thirdParetoStep = cannabis-terpene-pareto-step
  2 mechanismSpecificInteraction
  "test a named molecule pair, concentration range, endpoint and interaction model rather than invoking umbrella entourage language"
  "one mechanism-specific interaction or negative result"
  "same-object compounds/concentrations and assay identity first"

fourthParetoStep : CannabisTerpeneParetoStep
fourthParetoStep = cannabis-terpene-pareto-step
  4 humanPKPDInteraction
  "pay human pharmacokinetic/pharmacodynamic interaction only with explicit formulation, dose/composition and comparator"
  "human interaction coordinate"
  "preclinical interaction does not pay this"

fifthParetoStep : CannabisTerpeneParetoStep
fifthParetoStep = cannabis-terpene-pareto-step
  8 controlledClinicalSynergy
  "require controlled clinical comparison capable of distinguishing synergy/additivity from component effects"
  "clinical entourage claim"
  "all lower-level mechanistic and product-identity debts remain consumer-indexed"

historicalReplayParetoStep : CannabisTerpeneParetoStep
historicalReplayParetoStep = cannabis-terpene-pareto-step
  3 historicalIbrahimReplay
  "only promote a cannabis/terpene Wikipedia first-link edge after exact 2014 snapshot/parser replay under the existing Ibrahim producer-archeology gates"
  "historical traversal edge"
  "current QID/source cross-links do not pay historical FLN identity"

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data MoleculeIdentityCreatesCannabisPresence : Set where
data CannabisPresenceCreatesBatchComposition : Set where
data CoOccurrenceCreatesSynergy : Set where
data ReviewCreatesMechanism : Set where
data PreclinicalInteractionCreatesClinicalEfficacy : Set where
data BetaCaryophylleneCB2CreatesWholeEntourage : Set where
data QidCreatesPharmacology : Set where
data CurrentXLinkCreatesHistoricalFirstLink : Set where

moleculeIdentityDoesNotCreateCannabisPresence : MoleculeIdentityCreatesCannabisPresence → ⊥
moleculeIdentityDoesNotCreateCannabisPresence ()

cannabisPresenceDoesNotCreateBatchComposition : CannabisPresenceCreatesBatchComposition → ⊥
cannabisPresenceDoesNotCreateBatchComposition ()

coOccurrenceDoesNotCreateSynergy : CoOccurrenceCreatesSynergy → ⊥
coOccurrenceDoesNotCreateSynergy ()

reviewDoesNotCreateMechanism : ReviewCreatesMechanism → ⊥
reviewDoesNotCreateMechanism ()

preclinicalDoesNotCreateClinicalEfficacy : PreclinicalInteractionCreatesClinicalEfficacy → ⊥
preclinicalDoesNotCreateClinicalEfficacy ()

betaCaryophylleneCB2DoesNotCreateWholeEntourage : BetaCaryophylleneCB2CreatesWholeEntourage → ⊥
betaCaryophylleneCB2DoesNotCreateWholeEntourage ()

qidDoesNotCreatePharmacology : QidCreatesPharmacology → ⊥
qidDoesNotCreatePharmacology ()

currentXLinkDoesNotCreateHistoricalFirstLink : CurrentXLinkCreatesHistoricalFirstLink → ⊥
currentXLinkDoesNotCreateHistoricalFirstLink ()

externalIdentityPolicy : Identity.SnowballExternalIdentityPolicy
externalIdentityPolicy = Identity.canonicalExternalIdentityPolicy

crossDomainBoundary : Cross.IbrahimOracleCrossDomainBoundary
crossDomainBoundary = Cross.canonicalIbrahimOracleCrossDomainBoundary

record CannabisTerpeneEntourageBoundary : Set where
  constructor cannabis-terpene-entourage-boundary
  field
    existingEndocannabinoidCandidateReused : Bool
    moleculeStereochemistryRetained : Bool
    pubChemAndQidAreIdentityOnly : Bool
    terpeneDeweyRetainedAsLibraryCoordinate : Bool
    oeisMarkedNotApplicable : Bool
    primaryAndReviewSourceRolesSeparated : Bool
    negativeMechanismEvidenceRetained : Bool
    evidenceRemainsFibreOverTime : Bool
    currentXlinksRemainNonHistorical : Bool
    clinicalEntouragePromoted : Bool
open CannabisTerpeneEntourageBoundary public

canonicalCannabisTerpeneEntourageBoundary : CannabisTerpeneEntourageBoundary
canonicalCannabisTerpeneEntourageBoundary =
  cannabis-terpene-entourage-boundary
    true true true true true true true true true false
