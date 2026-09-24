module DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as ChemistryBoundary

------------------------------------------------------------------------
-- NITROGENASE INSTANCE OF THE GENERIC SITUATED-PROTEIN ARCHITECTURE
--
-- External papers own only the structural / mechanistic observations attached
-- to their citations. DASHI owns the finite two-world query witness below.
-- Cross-organism source reuse transfers no Acacia-specific mechanism.
------------------------------------------------------------------------

record NitrogenaseSourceIdentifiers : Set where
  constructor nitrogenase-source-identifiers
  field
    pmid : String
    pmcid : String
    pdbAccessions : String
open NitrogenaseSourceIdentifiers public

record NitrogenaseStructuralSource : Set where
  constructor nitrogenase-structural-source
  field
    attributedSource : Attribution.AttributedSource
    identifiers : NitrogenaseSourceIdentifiers
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
open NitrogenaseStructuralSource public

seefeldt2009 : NitrogenaseStructuralSource
seefeldt2009 = nitrogenase-structural-source
  (Attribution.mkDOISource
    "Lance C. Seefeldt; Brian M. Hoffman; Dennis R. Dean"
    "Mechanism of Mo-Dependent Nitrogenase"
    "Annual Review of Biochemistry 78:701-722"
    "2009"
    "10.1146/annurev.biochem.78.070907.103812"
    "https://pubmed.ncbi.nlm.nih.gov/19489731/"
    Attribution.academicArticleSource
    "Mechanistic calibration for Mo-dependent nitrogenase chemistry and limiting overall stoichiometry; does not own DASHI's cross-domain promotion firewalls."
    Attribution.publicAttribution)
  (nitrogenase-source-identifiers "19489731" "PMC2814439" "not recorded by this atlas")
  "Mo-dependent nitrogenase mechanism and limiting overall stoichiometric calibration"
  "Supports the chemistry-level reaction model already formalised by NitrogenaseChemistryCrossPollinationExact."
  "Balanced chemistry is not an in-vivo flux, plant assimilation receipt, seasonal N balance, fertilizer substitution or ecosystem outcome."

warmackRees2024 : NitrogenaseStructuralSource
warmackRees2024 = nitrogenase-structural-source
  (Attribution.mkDOISource
    "Rebeccah A. Warmack; Douglas C. Rees"
    "Structural evolution of nitrogenase states under alkaline turnover"
    "Nature Communications 15:10472"
    "2024"
    "10.1038/s41467-024-54713-0"
    "https://www.nature.com/articles/s41467-024-54713-0"
    Attribution.academicArticleSource
    "Cryo-EM turnover-state structural evidence used only to motivate retention of catalytic-context and observer coordinates in the situated-protein witness."
    Attribution.publicAttribution)
  (nitrogenase-source-identifiers "not recorded by this atlas" "PMC11612016" "source structures retained by publication; exact PDB list not promoted here")
  "Nitrogenase structural-state multiplicity under alkaline/acetylene turnover"
  "Supports that one protein identity may occupy distinguishable source-observed structural states under different turnover contexts."
  "Alkaline/acetylene cryo-EM states are not automatically in-vivo legume-nodule states and do not establish a field fixation rate."

narehood2025 : NitrogenaseStructuralSource
narehood2025 = nitrogenase-structural-source
  (Attribution.mkDOISource
    "Sarah M. Narehood; Brian D. Cook; Suppachai Srisantitham; Vanessa H. Eng; Angela A. Shiau; Kelly L. McGuire; R. David Britt; Mark A. Herzik Jr.; F. Akif Tezcan"
    "Structural basis for the conformational protection of nitrogenase from O2"
    "Nature 637:991-997"
    "2025"
    "10.1038/s41586-024-08311-1"
    "https://pubmed.ncbi.nlm.nih.gov/39779844/"
    Attribution.academicArticleSource
    "Structural source for oxygen-stress FeSII-mediated protection in Azotobacter vinelandii; retained as a situated-protein donor only."
    Attribution.publicAttribution)
  (nitrogenase-source-identifiers "39779844" "PMC11812610" "not recorded by this atlas")
  "FeSII-mediated oxygen-stress conformational protection of nitrogenase"
  "Supports a source-bounded protected/inactive structural state under oxygen stress in A. vinelandii."
  "Does not establish that Acacia/Senegalia symbionts use this exact protection mechanism or that a protected complex is actively fixing N2."

payaTormo2025 : NitrogenaseStructuralSource
payaTormo2025 = nitrogenase-structural-source
  (Attribution.mkDOISource
    "Lucia Paya Tormo; Tu-Quynh Nguyen; Cameron Fyfe; Hind Basbous; Katarzyna Dobrzynska; Carlos Echavarri-Erasun; Lydie Martin; Giorgio Caserta; Pierre Legrand; Andrea Thorn; Patricia Amara; Guy Schoehn; Mickael V. Cherrier; Luis M. Rubio; Yvain Nicolet"
    "Dynamics driving the precursor in NifEN scaffold during nitrogenase FeMo-cofactor assembly"
    "Nature Chemical Biology 22:813-821"
    "2025/2026"
    "10.1038/s41589-025-02070-4"
    "https://pubmed.ncbi.nlm.nih.gov/41238839/"
    Attribution.academicArticleSource
    "Structural source for NifEN cofactor-assembly dynamics; retained as a maturation-state donor rather than catalytic-flux evidence."
    Attribution.publicAttribution)
  (nitrogenase-source-identifiers "41238839" "not recorded by this atlas" "9I0F; 9I0G; 9I0H")
  "NifEN precursor docking, transfer, open/closed rearrangements and partial unfolding during FeMo-cofactor maturation"
  "Supports dynamic maturation-state coordinates and exact PDB identities 9I0F/9I0G/9I0H."
  "NifEN maturation state is not itself nitrogenase catalytic flux, plant BNF, plant assimilation or soil-N outcome."

nitrogenaseAttributedAtlas : Attribution.AttributedSourceAtlas
nitrogenaseAttributedAtlas = Attribution.mkSourceAtlas
  "Nitrogenase situated-protein structural source atlas"
  "DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact"
  (attributedSource seefeldt2009 ∷ attributedSource warmackRees2024 ∷ attributedSource narehood2025 ∷ attributedSource payaTormo2025 ∷ [])
  "Mechanistic/structural sources used to retain chemistry, turnover, oxygen-protection and cofactor-maturation coordinates; source identity never promotes organism transfer or downstream BNF authority."

------------------------------------------------------------------------
-- Explicit situated nitrogenase carrier.
--
-- The carrier keeps the coordinates demanded by the generic situated-protein
-- design visible even though the finite inadequacy proof below projects only
-- protein identity and functional state.  Values in the two canonical states
-- are DASHI source-shaped witnesses, not extra experimental observations.
------------------------------------------------------------------------

data NitrogenaseIdentity : Set where
  moNitrogenase : NitrogenaseIdentity

data OxygenContext : Set where
  lowOxygenContext : OxygenContext
  oxygenStressContext : OxygenContext

data InteractionPartnerState : Set where
  noProtectivePartner : InteractionPartnerState
  feSIIAssociated : InteractionPartnerState

data TurnoverContext : Set where
  catalyticTurnoverContext : TurnoverContext
  protectionContext : TurnoverContext

data CofactorMaturationState : Set where
  matureFeMoCofactor : CofactorMaturationState
  nifENPrecursorState : CofactorMaturationState

data ObserverMethod : Set where
  mechanisticReviewObserver : ObserverMethod
  cryoEMObserver : ObserverMethod
  maturationStructureObserver : ObserverMethod

data NitrogenaseFunctionalState : Set where
  catalyticallyAvailable : NitrogenaseFunctionalState
  conformationallyProtected : NitrogenaseFunctionalState

record NitrogenaseSituatedState : Set where
  constructor nitrogenase-situated-state
  field
    nitrogenaseIdentity : NitrogenaseIdentity
    oxygenContext : OxygenContext
    interactionPartner : InteractionPartnerState
    turnoverContext : TurnoverContext
    cofactorMaturation : CofactorMaturationState
    realisedFunctionalState : NitrogenaseFunctionalState
    historyStressReading : String
    observerMethod : ObserverMethod
    sourceProvenanceReading : String
open NitrogenaseSituatedState public

lowOxygenCatalyticState : NitrogenaseSituatedState
lowOxygenCatalyticState = nitrogenase-situated-state
  moNitrogenase
  lowOxygenContext
  noProtectivePartner
  catalyticTurnoverContext
  matureFeMoCofactor
  catalyticallyAvailable
  "DASHI low-oxygen/catalytic context witness; not a new field observation"
  cryoEMObserver
  "Warmack & Rees 2024 DOI 10.1038/s41467-024-54713-0 supplies turnover-state structural motivation; Seefeldt/Hoffman/Dean 2009 DOI 10.1146/annurev.biochem.78.070907.103812 supplies chemistry context."

oxygenStressProtectedState : NitrogenaseSituatedState
oxygenStressProtectedState = nitrogenase-situated-state
  moNitrogenase
  oxygenStressContext
  feSIIAssociated
  protectionContext
  matureFeMoCofactor
  conformationallyProtected
  "DASHI oxygen-stress/protection context witness; not an Acacia mechanism claim"
  cryoEMObserver
  "Narehood et al. 2025 DOI 10.1038/s41586-024-08311-1 PMID 39779844 PMCID PMC11812610 supplies the Azotobacter FeSII protection premise."

nifENMaturationState : NitrogenaseSituatedState
nifENMaturationState = nitrogenase-situated-state
  moNitrogenase
  lowOxygenContext
  noProtectivePartner
  protectionContext
  nifENPrecursorState
  conformationallyProtected
  "DASHI maturation-state carrier inhabitant; not catalytic-flux evidence"
  maturationStructureObserver
  "Paya Tormo et al. DOI 10.1038/s41589-025-02070-4 PMID 41238839 PDB 9I0F/9I0G/9I0H supplies NifEN precursor-state structural evidence."

------------------------------------------------------------------------
-- Finite situated-state witness.
------------------------------------------------------------------------

data NitrogenaseWorld : Set where
  lowOxygenCatalyticWorld : NitrogenaseWorld
  oxygenStressProtectedWorld : NitrogenaseWorld

worldState : NitrogenaseWorld → NitrogenaseSituatedState
worldState lowOxygenCatalyticWorld = lowOxygenCatalyticState
worldState oxygenStressProtectedWorld = oxygenStressProtectedState

proteinIdentity : NitrogenaseWorld → NitrogenaseIdentity
proteinIdentity world = nitrogenaseIdentity (worldState world)

functionalState : NitrogenaseWorld → NitrogenaseFunctionalState
functionalState world = realisedFunctionalState (worldState world)

sameProteinIdentity :
  proteinIdentity lowOxygenCatalyticWorld ≡ proteinIdentity oxygenStressProtectedWorld
sameProteinIdentity = refl

functionalStateSeparates :
  functionalState lowOxygenCatalyticWorld ≡ functionalState oxygenStressProtectedWorld → ⊥
functionalStateSeparates ()

data NitrogenaseQuery : Set where
  functionalStateQuery : NitrogenaseQuery

nitrogenaseAnswer : NitrogenaseQuery → NitrogenaseWorld → NitrogenaseFunctionalState
nitrogenaseAnswer functionalStateQuery world = functionalState world

nitrogenaseSemantics : Query.QuerySemantics NitrogenaseWorld NitrogenaseQuery NitrogenaseFunctionalState
nitrogenaseSemantics = Query.querySemantics nitrogenaseAnswer

proteinIdentityDefect :
  Query.QueryAdequacyDefect proteinIdentity nitrogenaseSemantics functionalStateQuery
proteinIdentityDefect = Query.queryAdequacyDefect
  lowOxygenCatalyticWorld
  oxygenStressProtectedWorld
  sameProteinIdentity
  functionalStateSeparates

nitrogenaseSituatedQueryWitness : Situated.SituatedProteinQueryWitness
nitrogenaseSituatedQueryWitness = Situated.situated-protein-query-witness
  NitrogenaseWorld
  NitrogenaseIdentity
  NitrogenaseQuery
  NitrogenaseFunctionalState
  proteinIdentity
  nitrogenaseSemantics
  functionalStateQuery
  proteinIdentityDefect
  Situated.contextual
  "oxygen/context/partner state separates nitrogenase functional state while the protein-identity projection remains fixed in the finite DASHI witness"
  "Warmack & Rees 2024 DOI 10.1038/s41467-024-54713-0; Narehood et al. 2025 DOI 10.1038/s41586-024-08311-1 PMID 39779844 PMCID PMC11812610; Paya Tormo et al. DOI 10.1038/s41589-025-02070-4 PMID 41238839 PDB 9I0F/9I0G/9I0H. Sources own only their bounded structural observations."
  "DASHI owns the two-world query inadequacy witness and the cross-source structural synthesis; it does not assert that the synthetic worlds are additional experimental observations."

proteinIdentityNotAdequateForFunctionalState :
  Query.AdequateFor proteinIdentity nitrogenaseSemantics functionalStateQuery → ⊥
proteinIdentityNotAdequateForFunctionalState =
  Situated.witnessBlocksCoarseAdequacy nitrogenaseSituatedQueryWitness

------------------------------------------------------------------------
-- Existing chemistry owner remains authoritative.
------------------------------------------------------------------------

balancedEquationStillDoesNotImplyInVivoFlux :
  ChemistryBoundary.NitrogenaseCrossDomainBoundary
balancedEquationStillDoesNotImplyInVivoFlux = ChemistryBoundary.canonicalNitrogenaseCrossDomainBoundary

reactionEnablementStageStillOpen :
  ChemistryBoundary.stageClosed ChemistryBoundary.reactionEnablement ≡ false
reactionEnablementStageStillOpen = ChemistryBoundary.reactionEnablementStillOpen

------------------------------------------------------------------------
-- Promotion / organism-transfer boundary.
------------------------------------------------------------------------

record NitrogenaseSituatedBoundary : Set where
  constructor nitrogenase-situated-boundary
  field
    usesGenericSituatedProteinWitness : Bool
    fullSituatedContextCarrierRetained : Bool
    proteinIdentityAloneAdequate : Bool
    balancedStoichiometryCreatesEffectiveFlux : Bool
    azotobacterProtectionTransfersToAcacia : Bool
    nifENMaturationStateCreatesCatalyticFlux : Bool
    structuralStateCreatesPlantAssimilation : Bool
    sourceIdentifiersCreateBiologicalAuthority : Bool
open NitrogenaseSituatedBoundary public

canonicalNitrogenaseBoundary : NitrogenaseSituatedBoundary
canonicalNitrogenaseBoundary = nitrogenase-situated-boundary
  true true false false false false false false

proteinIdentityAloneIsInadequate :
  proteinIdentityAloneAdequate canonicalNitrogenaseBoundary ≡ false
proteinIdentityAloneIsInadequate = refl

fullSituatedContextIsRetained :
  fullSituatedContextCarrierRetained canonicalNitrogenaseBoundary ≡ true
fullSituatedContextIsRetained = refl

balancedStoichiometryDoesNotCreateEffectiveFlux :
  balancedStoichiometryCreatesEffectiveFlux canonicalNitrogenaseBoundary ≡ false
balancedStoichiometryDoesNotCreateEffectiveFlux = refl

attributionRule : String
attributionRule =
  "Seefeldt/Hoffman/Dean, Warmack/Rees, Narehood et al., and Paya Tormo et al. retain ownership of their cited source propositions and identifiers. ProteinSituatedHyperfabric, QueryAdequacyDefect, organism-transfer firewalls and the finite collision are DASHI formalisation/synthesis. DOI/PMID/PMCID/PDB identifiers are provenance only."
