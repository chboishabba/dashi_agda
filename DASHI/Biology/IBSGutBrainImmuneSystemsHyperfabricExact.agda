module DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.QuailEggHistamineGutSnowballExact as Quail
import DASHI.Biology.HistamineCompartmentClearanceExact as Histamine
import DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary as MicrobiomeHost
import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Interoception
import DASHI.Biology.NeurochemicalVocabularyReceipt as Neurochem

------------------------------------------------------------------------
-- IBS / DGBI WHOLE-SYSTEM HYPERFABRIC
--
-- IBS is represented as a coupled recurrent gut-brain-immune system rather
-- than a one-cause chain.  Individual mechanisms can be experimentally real
-- without being necessary, sufficient, universal, or scalar-complete causes.
------------------------------------------------------------------------

black2026Source : Source.AttributedSource
black2026Source = Source.mkDOISource
  "Christopher J Black et al."
  "Pathophysiology of irritable bowel syndrome"
  "The Lancet Gastroenterology & Hepatology" "2026"
  "10.1016/S2468-1253(26)00148-2"
  "https://doi.org/10.1016/S2468-1253(26)00148-2"
  Source.academicArticleSource
  "Current review retaining infection, microbiome, visceral hypersensitivity, permeability, low-grade mucosal inflammation/immune function, motility, serotonin, bile-acid and carbohydrate metabolism, psychological health and central pain processing as interacting IBS mechanisms."
  Source.publicAttribution

dong2024Source : Source.AttributedSource
dong2024Source = Source.mkDOISource
  "Tien S Dong et al."
  "Advances in Brain-Gut-Microbiome Interactions: A Comprehensive Update on Signaling Mechanisms, Disorders, and Therapeutic Implications"
  "Cellular and Molecular Gastroenterology and Hepatology" "2024"
  "10.1016/j.jcmgh.2024.01.024"
  "https://doi.org/10.1016/j.jcmgh.2024.01.024"
  Source.academicArticleSource
  "Review-level support for a bidirectional brain-gut-microbiome system using neuronal, endocrine and immune signalling, with autonomic outputs modulating motility, secretion, permeability and microbial ecology."
  Source.publicAttribution

gabaIBS2025Source : Source.AttributedSource
gabaIBS2025Source = Source.mkDOISource
  "IBS GABA review authors as indexed by Frontiers in Pharmacology"
  "Targeting gamma-aminobutyric acid pathways in irritable bowel syndrome: bridging central nervous system, enteric dysfunction, and the microbiota-gut-brain axis"
  "Frontiers in Pharmacology" "2025"
  "10.3389/fphar.2025.1677037"
  "https://doi.org/10.3389/fphar.2025.1677037"
  Source.academicArticleSource
  "Review-level candidate bridge: GABAergic signalling may participate in visceral pain, motility, barrier integrity, immune response and microbiota-gut-brain signalling. It does not pay a single-GABA-cause model of IBS."
  Source.publicAttribution

data IBSSystemFibre : Set where
  dietExposureFibre : IBSSystemFibre
  microbiomeMetaboliteFibre : IBSSystemFibre
  epithelialBarrierFibre : IBSSystemFibre
  mucosalImmuneMastCellFibre : IBSSystemFibre
  entericMotilitySecretionFibre : IBSSystemFibre
  visceralSensoryNociceptiveFibre : IBSSystemFibre
  autonomicHPAAllostaticFibre : IBSSystemFibre
  centralPainInteroceptiveFibre : IBSSystemFibre
  neurochemicalMetabolicFibre : IBSSystemFibre

data CouplingKind : Set where
  biochemical : CouplingKind
  immune : CouplingKind
  neural : CouplingKind
  endocrine : CouplingKind
  mechanical : CouplingKind
  behaviouralContext : CouplingKind
  transportBarrier : CouplingKind

record IBSSystemEdge : Set where
  constructor ibs-system-edge
  field
    from : IBSSystemFibre
    to : IBSSystemFibre
    coupling : CouplingKind
    evidenceReference : String
    reverseOrFeedbackReference : String
    universalCausalityClaimed : Bool
open IBSSystemEdge public

microbiomeImmuneEdge : IBSSystemEdge
microbiomeImmuneEdge = ibs-system-edge
  microbiomeMetaboliteFibre mucosalImmuneMastCellFibre immune
  "De Palma 2022: microbiota-derived histamine/H4 mechanism; Gao 2026: fecal-LPS/TLR4 mast-cell route"
  "host immune/barrier state can in turn reshape luminal ecology; direction and timescale remain experiment-specific"
  false

immuneSensoryEdge : IBSSystemEdge
immuneSensoryEdge = ibs-system-edge
  mucosalImmuneMastCellFibre visceralSensoryNociceptiveFibre neural
  "Wouters 2016 and later H1 intervention evidence: histamine/H1/TRPV1-associated visceral sensitization"
  "neural activity and autonomic outputs can also modulate immune/mast-cell state"
  false

barrierImmuneEdge : IBSSystemEdge
barrierImmuneEdge = ibs-system-edge
  epithelialBarrierFibre mucosalImmuneMastCellFibre transportBarrier
  "human DGBI permeability literature and Gao mechanistic IBS-D trial"
  "immune mediators and stress/autonomic outputs can alter barrier function"
  false

allostaticGutEdge : IBSSystemEdge
allostaticGutEdge = ibs-system-edge
  autonomicHPAAllostaticFibre entericMotilitySecretionFibre endocrine
  "brain-gut literature: autonomic/HPA outputs participate in motility, secretion and permeability"
  "gut afference, pain and microbial/endocrine signals feed back to allostatic/central state"
  false

gutCentralEdge : IBSSystemEdge
gutCentralEdge = ibs-system-edge
  visceralSensoryNociceptiveFibre centralPainInteroceptiveFibre neural
  "DGBI literature: visceral afference and central pain processing interact in symptom generation"
  "descending/autonomic regulation changes gain, motility, secretion and immune context"
  false

dietMicrobiomeBarrierEdge : IBSSystemEdge
dietMicrobiomeBarrierEdge = ibs-system-edge
  dietExposureFibre microbiomeMetaboliteFibre biochemical
  "diet/FODMAP and microbiome studies alter substrate availability, metabolites and downstream gut physiology"
  "microbial metabolism changes the effective exposure seen by epithelium/host"
  false

neurochemicalSystemEdge : IBSSystemEdge
neurochemicalSystemEdge = ibs-system-edge
  neurochemicalMetabolicFibre visceralSensoryNociceptiveFibre biochemical
  "candidate mediators include histamine, serotonin, GABA and bile-acid/metabolic signalling, each with compartment/receptor-specific evidence requirements"
  "symptoms do not identify which mediator/pathway generated the observed state"
  false

canonicalIBSFeedbackGraph : List IBSSystemEdge
canonicalIBSFeedbackGraph =
  microbiomeImmuneEdge ∷ immuneSensoryEdge ∷ barrierImmuneEdge ∷
  allostaticGutEdge ∷ gutCentralEdge ∷ dietMicrobiomeBarrierEdge ∷
  neurochemicalSystemEdge ∷ []

record ExistingOwnerWeld : Set where
  constructor existing-owner-weld
  field
    histamineCoordinates : Histamine.HistamineBalanceCoordinates
    microbiomeHostBoundary : MicrobiomeHost.MicrobiomeHostAppetiteBoundary
    allostaticBoundary : Allostatic.AllostaticBodyStateBoundary
    interoceptionBoundary : Interoception.EmbodiedOptionConeBoundary
    quailBoundary : Quail.QuailEggHistamineGutBoundary
    gabaCandidateReference : String
    ownerReuseDoesNotCreateEmpiricalCausality : Bool
open ExistingOwnerWeld public

canonicalExistingOwnerWeld : ExistingOwnerWeld
canonicalExistingOwnerWeld = existing-owner-weld
  Histamine.canonicalHistamineBalanceCoordinates
  MicrobiomeHost.canonicalMicrobiomeHostAppetiteBoundary
  Allostatic.canonicalAllostaticBodyStateBoundary
  Interoception.canonicalEmbodiedOptionConeBoundary
  Quail.canonicalQuailEggHistamineGutBoundary
  "DASHI.Biology.NeurochemicalVocabularyReceipt.gabaCandidate"
  true

data InflammationIsCompleteIBSCausePermission : Set where
inflammationDoesNotExhaustIBS : InflammationIsCompleteIBSCausePermission → ⊥
inflammationDoesNotExhaustIBS ()

data HistamineIsCompleteIBSCausePermission : Set where
histamineDoesNotExhaustIBS : HistamineIsCompleteIBSCausePermission → ⊥
histamineDoesNotExhaustIBS ()

data GutOnlyIBSPermission : Set where
gutOnlyModelDoesNotExhaustDGBI : GutOnlyIBSPermission → ⊥
gutOnlyModelDoesNotExhaustDGBI ()

data BrainOnlyIBSPermission : Set where
brainOnlyModelDoesNotExhaustDGBI : BrainOnlyIBSPermission → ⊥
brainOnlyModelDoesNotExhaustDGBI ()

data QuailLocalFibreEqualsWholeSystemTherapyPermission : Set where
quailLocalFibreDoesNotEqualWholeSystemTherapy :
  QuailLocalFibreEqualsWholeSystemTherapyPermission → ⊥
quailLocalFibreDoesNotEqualWholeSystemTherapy ()

record IBSWholeSystemBoundary : Set where
  constructor ibs-whole-system-boundary
  field
    recurrentBidirectionalGraphRetained : Bool
    inflammationMayBeMechanisticallyRelevant : Bool
    inflammationIsUniversalMasterCause : Bool
    histamineMayBeMechanisticallyRelevant : Bool
    histamineIsUniversalMasterCause : Bool
    autonomicHPAStateRetained : Bool
    centralInteroceptivePainStateRetained : Bool
    microbiomeMetaboliteStateRetained : Bool
    barrierStateRetained : Bool
    motilitySecretionStateRetained : Bool
    quailInterventionActsOnLocalCandidateFibre : Bool
    localMechanismDoesNotEqualWholeSystemClosure : Bool

canonicalIBSWholeSystemBoundary : IBSWholeSystemBoundary
canonicalIBSWholeSystemBoundary = ibs-whole-system-boundary
  true true false true false true true true true true true true
