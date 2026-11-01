module DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Protein.ProteinFunctionProjection as Function
import DASHI.Biology.Protein.AlliumThiolProteinInteractionExact as AlliumProtein

------------------------------------------------------------------------
-- TRPA1 SINGLE-RESIDUE THERMAL-GATING FIBRE
--
-- Feng et al., Science Advances (2026), DOI 10.1126/sciadv.aee3948,
-- report that a single amino-acid change in the TRPA1 pore domain is sufficient
-- to rewire heat sensitivity in their comparative/mutational system.  The
-- finite witness below encodes only the information-loss shape needed by DASHI:
-- retaining the protein name while erasing the residue coordinate loses the
-- experimentally discriminating thermal-response coordinate.
--
-- This is not a theorem that one residue determines all TRPA1 function, all
-- protein function, or vertebrate thermal adaptation in every context.
------------------------------------------------------------------------

data ProteinIdentity : Set where
  trpa1 : ProteinIdentity

data PoreResidueState : Set where
  ancestralLikeResidue : PoreResidueState
  mammalianAspartate : PoreResidueState

data TRPA1RichState : Set where
  ancestralLikeTRPA1 : TRPA1RichState
  mammalianAspartateTRPA1 : TRPA1RichState

data ThermalResponse : Set where
  heatActivated : ThermalResponse
  reducedThermalResponsiveness : ThermalResponse

proteinIdentity : TRPA1RichState → ProteinIdentity
proteinIdentity ancestralLikeTRPA1 = trpa1
proteinIdentity mammalianAspartateTRPA1 = trpa1

poreResidue : TRPA1RichState → PoreResidueState
poreResidue ancestralLikeTRPA1 = ancestralLikeResidue
poreResidue mammalianAspartateTRPA1 = mammalianAspartate

thermalReadout : TRPA1RichState → ThermalResponse
thermalReadout ancestralLikeTRPA1 = heatActivated
thermalReadout mammalianAspartateTRPA1 = reducedThermalResponsiveness

sameProteinIdentity :
  proteinIdentity ancestralLikeTRPA1 ≡ proteinIdentity mammalianAspartateTRPA1
sameProteinIdentity = refl

residueStateSeparates :
  poreResidue ancestralLikeTRPA1 ≡ poreResidue mammalianAspartateTRPA1 → ⊥
residueStateSeparates ()

thermalResponseSeparates :
  thermalReadout ancestralLikeTRPA1
  ≡ thermalReadout mammalianAspartateTRPA1 → ⊥
thermalResponseSeparates ()

record ThermalResponseFactorsThroughProteinIdentity : Set where
  constructor thermalResponseFactorsThroughProteinIdentity
  field
    factor : ProteinIdentity → ThermalResponse
    law : (x : TRPA1RichState) → thermalReadout x ≡ factor (proteinIdentity x)

open ThermalResponseFactorsThroughProteinIdentity public

thermalResponseDoesNotFactorThroughProteinIdentity :
  ThermalResponseFactorsThroughProteinIdentity → ⊥
thermalResponseDoesNotFactorThroughProteinIdentity F =
  thermalResponseSeparates
    (trans
      (law F ancestralLikeTRPA1)
      (sym (law F mammalianAspartateTRPA1)))

------------------------------------------------------------------------
-- Constructive repair: expose protein identity together with the pore-residue
-- coordinate.  For this finite source-shaped carrier, thermal response then has
-- an explicit factorisation through the enriched observation.
------------------------------------------------------------------------

record ResidueAwareObservation : Set where
  constructor residueAwareObservation
  field
    protein : ProteinIdentity
    residue : PoreResidueState

open ResidueAwareObservation public

residueAware : TRPA1RichState → ResidueAwareObservation
residueAware ancestralLikeTRPA1 =
  residueAwareObservation trpa1 ancestralLikeResidue
residueAware mammalianAspartateTRPA1 =
  residueAwareObservation trpa1 mammalianAspartate

thermalFromResidueAware : ResidueAwareObservation → ThermalResponse
thermalFromResidueAware (residueAwareObservation trpa1 ancestralLikeResidue) =
  heatActivated
thermalFromResidueAware (residueAwareObservation trpa1 mammalianAspartate) =
  reducedThermalResponsiveness

thermalResponseFactorsThroughResidueAware :
  (x : TRPA1RichState) →
  thermalReadout x ≡ thermalFromResidueAware (residueAware x)
thermalResponseFactorsThroughResidueAware ancestralLikeTRPA1 = refl
thermalResponseFactorsThroughResidueAware mammalianAspartateTRPA1 = refl

------------------------------------------------------------------------
-- Empirical promotion ladder.
--
-- Each level requires its own receipt so sequence perturbation, channel gating,
-- cell signalling, developmental phenotype, and evolutionary interpretation
-- cannot silently collapse into one another.
------------------------------------------------------------------------

record SingleResidueThermalGateReceipt : Set where
  constructor singleResidueThermalGateReceipt
  field
    proteinReference : String
    poreCoordinateReference : String
    ancestralStateReference : String
    derivedStateReference : String
    assayReference : String
    thermalPhenotypeReference : String
    sourceReference : String
    applicabilityBoundary : String

open SingleResidueThermalGateReceipt public

feng2026ThermalGateReceipt : SingleResidueThermalGateReceipt
feng2026ThermalGateReceipt =
  singleResidueThermalGateReceipt
    "transient receptor potential ankyrin 1 (TRPA1)"
    "pore-domain homologous site reported around residue 896; species-local numbering must be retained"
    "ancestral residue state retained by many oviparous vertebrates"
    "aspartate state selected in the mammalian lineage"
    "cross-species electrophysiology plus site-directed mutation"
    "ancestral-like state: heat activation; mammalian aspartate state: reduced thermal responsiveness"
    "Feng et al. 2026, Science Advances, DOI 10.1126/sciadv.aee3948"
    "source-bounded comparative/mutational result; not a universal one-residue protein-function law"


data MechanismStage : Set where
  heatActivatedTRPA1 : MechanismStage
  calciumInflux : MechanismStage
  nuclearSP1 : MechanismStage
  cadm1Mdga1Activation : MechanismStage
  dorsalRootGanglionDevelopment : MechanismStage

record MechanismEdgeReceipt : Set where
  constructor mechanismEdgeReceipt
  field
    from : MechanismStage
    to : MechanismStage
    evidenceReference : String
    sourceReference : String

open MechanismEdgeReceipt public

trpa1ToCalcium : MechanismEdgeReceipt
trpa1ToCalcium = mechanismEdgeReceipt
  heatActivatedTRPA1 calciumInflux
  "TRPA1-mediated Ca2+ influx reported under the heat-response mechanism"
  "Feng et al. 2026, DOI 10.1126/sciadv.aee3948"

calciumToSP1 : MechanismEdgeReceipt
calciumToSP1 = mechanismEdgeReceipt
  calciumInflux nuclearSP1
  "Ca2+ influx linked to SP1 nuclear translocation"
  "Feng et al. 2026, DOI 10.1126/sciadv.aee3948"

sp1ToCadm1Mdga1 : MechanismEdgeReceipt
sp1ToCadm1Mdga1 = mechanismEdgeReceipt
  nuclearSP1 cadm1Mdga1Activation
  "SP1 linked to activation of CADM1 and MDGA1"
  "Feng et al. 2026, DOI 10.1126/sciadv.aee3948"

cadm1Mdga1ToDevelopment : MechanismEdgeReceipt
cadm1Mdga1ToDevelopment = mechanismEdgeReceipt
  cadm1Mdga1Activation dorsalRootGanglionDevelopment
  "pathway linked to dorsal-root-ganglion axon development / myelination under high-temperature challenge"
  "Feng et al. 2026, DOI 10.1126/sciadv.aee3948"

record EmbryoInterventionReceipt : Set where
  constructor embryoInterventionReceipt
  field
    interventionReference : String
    observedAxonReference : String
    observedMyelinationReference : String
    observedHatchingReference : String
    sourceReference : String
    causalScopeBoundary : String

oviparousEmbryoInterventionReceipt : EmbryoInterventionReceipt
oviparousEmbryoInterventionReceipt = embryoInterventionReceipt
  "blocking heat-activated TRPA1 in oviparous embryos"
  "impaired dorsal-root-ganglion axon growth"
  "disrupted myelination"
  "limb weakness at hatching"
  "Feng et al. 2026, DOI 10.1126/sciadv.aee3948"
  "intervention evidence supports the assayed developmental route; it does not make TRPA1 the sole determinant of embryo survival or thermal fitness"

------------------------------------------------------------------------
-- Source / snowball coordinates.  Missing catalogue identities stay missing.
------------------------------------------------------------------------

record TRPA1SourceCoordinate : Set where
  constructor trpa1SourceCoordinate
  field
    authors : String
    title : String
    publication : String
    publicationDate : String
    doi : String
    directLink : String
    sourceKind : String
    qid : String
    dewey : String
    oeis : String
    formalisationRole : String

fengrEtAl2026 : TRPA1SourceCoordinate
fengrEtAl2026 = trpa1SourceCoordinate
  "Tian-Yu Feng; Wenqi Dong; Dong Zheng; Lei Han; Jiatong Chen; Xuanye Wu; Xiancui Lu; Shilong Yang; Wei-Guo Du"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  "Science Advances 12(36)"
  "2026-09-02 online issue listing; bibliographic services may display 2026-09-04 issue date"
  "10.1126/sciadv.aee3948"
  "https://www.science.org/doi/10.1126/sciadv.aee3948"
  "primary research article"
  "article-level Wikidata QID unresolved in inspected sources"
  "exact article-level Dewey coordinate unresolved"
  "not an integer-sequence object; no same-object OEIS coordinate"
  "source for the bounded residue/gating, embryo-intervention, and Ca2+-SP1-CADM1/MDGA1 propositions; citation imports neither proof nor universal authority"

------------------------------------------------------------------------
-- Existing protein carriers reused rather than replaced.
------------------------------------------------------------------------

proteinFunctionSystemSurface : Set₁
proteinFunctionSystemSurface = Function.ProteinFunctionSystem

proteinPredictionAuthorityBoundarySurface :
  Function.SharedProteinRepresentation → Set₁
proteinPredictionAuthorityBoundarySurface = Function.ProteinPredictionAuthorityBoundary

alliumProteinThiolReceiptSurface : Set
alliumProteinThiolReceiptSurface = AlliumProtein.SThioallylationReceipt

trpa1AlliumCrossPollinationBoundary : String
trpa1AlliumCrossPollinationBoundary =
  "TRPA1 can participate in chemically activated and thermally gated contexts; shared protein identity does not identify allicin/thiol activation with the site-896 thermal-gating mechanism"

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record TRPA1ThermalAdaptationBoundary : Set where
  constructor trpa1ThermalAdaptationBoundary
  field
    siteSpecificMutationCoordinatePaid : Bool
    siteSpecificMutationCoordinatePaidIsTrue :
      siteSpecificMutationCoordinatePaid ≡ true

    ca2Sp1Cadm1Mdga1PathPaid : Bool
    ca2Sp1Cadm1Mdga1PathPaidIsTrue :
      ca2Sp1Cadm1Mdga1PathPaid ≡ true

    proteinIdentityAloneDeterminesThermalResponse : Bool
    proteinIdentityAloneDeterminesThermalResponseIsFalse :
      proteinIdentityAloneDeterminesThermalResponse ≡ false

    singleResidueDeterminesAllProteinFunction : Bool
    singleResidueDeterminesAllProteinFunctionIsFalse :
      singleResidueDeterminesAllProteinFunction ≡ false

    thermalActivationAloneProvesEmbryoSurvival : Bool
    thermalActivationAloneProvesEmbryoSurvivalIsFalse :
      thermalActivationAloneProvesEmbryoSurvival ≡ false

    allicinActivationIsSameMechanismAsThermalGating : Bool
    allicinActivationIsSameMechanismAsThermalGatingIsFalse :
      allicinActivationIsSameMechanismAsThermalGating ≡ false

    paperCreatesUniversalVertebrateAdaptationLaw : Bool
    paperCreatesUniversalVertebrateAdaptationLawIsFalse :
      paperCreatesUniversalVertebrateAdaptationLaw ≡ false

    sourceCitationImportsProofOrAuthority : Bool
    sourceCitationImportsProofOrAuthorityIsFalse :
      sourceCitationImportsProofOrAuthority ≡ false

canonicalTRPA1ThermalAdaptationBoundary : TRPA1ThermalAdaptationBoundary
canonicalTRPA1ThermalAdaptationBoundary =
  trpa1ThermalAdaptationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
