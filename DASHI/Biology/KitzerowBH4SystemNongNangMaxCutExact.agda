module DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas
import DASHI.Biology.UniProtExternalKnowledgeExact as UniProt
import DASHI.Biology.UniProtBH4PanelCertificateExact as Panel
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide
import DASHI.Biology.NitrousOxideMetabolismEvidenceExact as Nang
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as Nongin
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- KITZEROW BH4 SYSTEM / NONG-NANG MAX-CUT
--
-- External protein-record acquisition is closed (16/16 UniProtKB 2026_03),
-- and the live panel reaction acquisition is now also closed at its bounded
-- level: 24 protein->Rhea links yielded 12 finite matrix reactions and three
-- explicit non-finite MTOR protein/R-group reaction residuals.  Reaction
-- payment remains distinct from compartment/flux/causal-transition payment.
------------------------------------------------------------------------

record ProteinPanelMember : Set where
  constructor protein-panel-member
  field
    symbol : String
    accession : String
    sector : String
    primaryTarget : Atlas.RelationTarget
    secondaryTargets : List Atlas.RelationTarget
    exactCertificatePinned : Bool

open ProteinPanelMember public

gch1 : ProteinPanelMember
gch1 = protein-panel-member "GCH1" "P30793" "BH4 synthesis / regulation" Atlas.gch1RedoxRegulation (Atlas.bh4Availability ∷ []) true

gchfr : ProteinPanelMember
gchfr = protein-panel-member "GCHFR" "P30047" "GCH1 feedback regulation" Atlas.gch1RedoxRegulation [] true

pts : ProteinPanelMember
pts = protein-panel-member "PTS" "Q03393" "BH4 synthesis" Atlas.bh4Availability [] true

spr : ProteinPanelMember
spr = protein-panel-member "SPR" "P35270" "BH4 synthesis" Atlas.bh4Availability [] true

pcbd1 : ProteinPanelMember
pcbd1 = protein-panel-member "PCBD1" "P61457" "BH4 recycling" Atlas.bh4Availability [] true

qdpr : ProteinPanelMember
qdpr = protein-panel-member "QDPR" "P09417" "BH4 recycling" Atlas.bh4Availability [] true

nos1 : ProteinPanelMember
nos1 = protein-panel-member "NOS1" "P29475" "neuronal nitric-oxide synthase" Atlas.nosUncoupling (Atlas.noTsc2Mtor ∷ []) true

nos2 : ProteinPanelMember
nos2 = protein-panel-member "NOS2" "P35228" "inducible nitric-oxide synthase" Atlas.nosUncoupling (Atlas.neuroimmuneCascade ∷ []) true

nos3 : ProteinPanelMember
nos3 = protein-panel-member "NOS3" "P29474" "endothelial nitric-oxide synthase" Atlas.nosUncoupling [] true

pah : ProteinPanelMember
pah = protein-panel-member "PAH" "P00439" "aromatic amino-acid hydroxylase" Atlas.aaaHBranch [] true

th : ProteinPanelMember
th = protein-panel-member "TH" "P07101" "catecholamine AAAH" Atlas.aaaHBranch (Atlas.synapticProteinRegulation ∷ []) true

tph1 : ProteinPanelMember
tph1 = protein-panel-member "TPH1" "P17752" "peripheral serotonin AAAH" Atlas.aaaHBranch (Atlas.neuroimmuneCascade ∷ []) true

tph2 : ProteinPanelMember
tph2 = protein-panel-member "TPH2" "Q8IWU9" "neuronal serotonin AAAH" Atlas.aaaHBranch (Atlas.excitatoryInhibitoryCircuitState ∷ []) true

agmo : ProteinPanelMember
agmo = protein-panel-member "AGMO" "Q6ZNB7" "BH4-dependent ether-lipid cleavage" Atlas.cellStressTranslationState [] true

tsc2 : ProteinPanelMember
tsc2 = protein-panel-member "TSC2" "P49815" "NO downstream / TSC2-mTOR" Atlas.noTsc2Mtor [] true

mtor : ProteinPanelMember
mtor = protein-panel-member "MTOR" "P42345" "TSC2-mTOR signaling" Atlas.noTsc2Mtor (Atlas.cellStressTranslationState ∷ []) true

kitzerowBH4ProteinPanel : List ProteinPanelMember
kitzerowBH4ProteinPanel =
  gch1 ∷ gchfr ∷ pts ∷ spr ∷ pcbd1 ∷ qdpr
  ∷ nos1 ∷ nos2 ∷ nos3
  ∷ pah ∷ th ∷ tph1 ∷ tph2
  ∷ agmo ∷ tsc2 ∷ mtor ∷ []

exactProteinPanelBoundary : Panel.UniProtBH4PanelBoundary
exactProteinPanelBoundary = Panel.canonicalUniProtBH4PanelBoundary

executedReactionPanel : Executed.ExecutedPanelReactionReceipt
executedReactionPanel = Executed.canonicalExecutedPanelReactionReceipt

------------------------------------------------------------------------
-- Edge-payment matrix. "Paid" means paid only at the stated coordinate.
------------------------------------------------------------------------

record MechanisticEdgePayment : Set where
  constructor mechanistic-edge-payment
  field
    edgeId : String
    fromReference : String
    toReference : String
    atlasTarget : Atlas.RelationTarget
    identityPaid : Bool
    reactionOrRelationPaid : Bool
    compartmentPaid : Bool
    fluxPaid : Bool
    causalTransitionPaid : Bool
    residualReference : String

open MechanisticEdgePayment public

qdprRegenerationEdge : MechanisticEdgePayment
qdprRegenerationEdge =
  mechanistic-edge-payment
    "EDGE-QDPR-BH4-REGENERATION"
    "P09417/QDPR; exact UniProt 2026_03 certificate"
    "RHEA:17869 and RHEA:17865; live panel reaction acquisition"
    Atlas.bh4Availability
    true true false false false
    "protein/reaction chemistry is paid; measured compartmental BH4/BH2 state, regeneration flux and causal transition remain unpaid"

bh4ToNOSCouplingEdge : MechanisticEdgePayment
bh4ToNOSCouplingEdge =
  mechanistic-edge-payment
    "EDGE-BH4-NOS-COUPLING"
    "shared BH4/BH2/redox system state"
    "NOS1/NOS2/NOS3 RHEA:19897 chemistry -> coupling state and NO/superoxide output"
    Atlas.nosUncoupling
    true true false false false
    "canonical NOS reaction chemistry is paid; same-compartment BH4/BH2, substrate, redox, product measurements and isoform-specific interventional coupling transitions remain required"

nosToTSC2Edge : MechanisticEdgePayment
nosToTSC2Edge =
  mechanistic-edge-payment
    "EDGE-NO-TSC2-MTOR"
    "NO / S-nitrosylation state"
    "TSC2 -> mTOR dysregulation"
    Atlas.noTsc2Mtor
    true true false false false
    "NOS/TSC2/MTOR identities and downstream relation evidence are paid; same-object transport from the proposed upstream BH4/NOS state remains required; MTOR protein/R-group reaction rows remain non-finite residuals"

aaahCompetitionEdge : MechanisticEdgePayment
aaahCompetitionEdge =
  mechanistic-edge-payment
    "EDGE-BH4-AAAH-COMPETITION"
    "shared BH4 system state"
    "PAH RHEA:20273 / TH RHEA:18201 / TPH1+TPH2 RHEA:16709"
    Atlas.aaaHBranch
    true true false false false
    "AAAH identities and finite BH4-dependent reaction chemistry are paid; simultaneous compartmental demand/allocation flux remains unpaid"

agmoCompetitionEdge : MechanisticEdgePayment
agmoCompetitionEdge =
  mechanistic-edge-payment
    "EDGE-BH4-AGMO-COMPETITION"
    "shared BH4 system state"
    "AGMO RHEA:36255 ether-lipid cleavage"
    Atlas.cellStressTranslationState
    true true false false false
    "AGMO identity and finite BH4-dependent reaction chemistry are paid; allocator competition and downstream cell-stress consequences remain separate obligations"

------------------------------------------------------------------------
-- NONG/NANG cross-pollination stays adjacent to, not merged with, NOS.
------------------------------------------------------------------------

nangSpecies : Oxide.NitrogenOxideSpecies
nangSpecies = Oxide.nitrousOxide

nonginChemicalRefinement : Nongin.NongNangGenealogyBoundary
nonginChemicalRefinement = Nongin.canonicalNongNangGenealogyBoundary

nangCobalaminEvidence : Nang.NitrousOxideEvidenceReceipt
nangCobalaminEvidence = Nang.cobalaminOxidationReceipt

------------------------------------------------------------------------
-- System residual frontier.
------------------------------------------------------------------------

data KitzerowBH4SystemResidual : Set where
  acquireRemainingProteinCertificates : KitzerowBH4SystemResidual
  acquireRheaReactionWitnesses : KitzerowBH4SystemResidual
  acquirePDBSIFTSResidueWitnesses : KitzerowBH4SystemResidual
  acquirePrimaryMechanisticExperiments : KitzerowBH4SystemResidual
  payCompartmentSpecificBH4BH2State : KitzerowBH4SystemResidual
  paySimultaneousConsumerDemand : KitzerowBH4SystemResidual
  payTransportAndOxidationFlux : KitzerowBH4SystemResidual
  payNOSCouplingTransitions : KitzerowBH4SystemResidual
  payUpstreamToTSC2SameObjectTransport : KitzerowBH4SystemResidual
  testWholeSystemFluxBalance : KitzerowBH4SystemResidual
  testAlternativeMechanisms : KitzerowBH4SystemResidual

-- Protein and Rhea acquisition plus the first whole-system flux attempt are now
-- historical residual vocabulary, absent from the live frontier. The flux
-- attempt returned underdetermined rather than feasible/infeasible globally.
liveResiduals : List KitzerowBH4SystemResidual
liveResiduals =
  acquirePDBSIFTSResidueWitnesses
  ∷ acquirePrimaryMechanisticExperiments
  ∷ payCompartmentSpecificBH4BH2State
  ∷ paySimultaneousConsumerDemand
  ∷ payTransportAndOxidationFlux
  ∷ payNOSCouplingTransitions
  ∷ payUpstreamToTSC2SameObjectTransport
  ∷ testAlternativeMechanisms
  ∷ []

record KitzerowBH4SystemMaxCutBoundary : Set where
  constructor kitzerow-bh4-system-maxcut-boundary
  field
    exactProteinPanelAcquisitionClosed : Bool
    panelReactionAcquisitionClosed : Bool
    firstWholeSystemFluxAttemptExecuted : Bool
    isolatedNodeSupportConfirmsWholeGraph : Bool
    isolatedNodeSupportConfirmsWholeGraphIsFalse :
      isolatedNodeSupportConfirmsWholeGraph ≡ false
    fullProteinPanelConfirmsAllocatorFlux : Bool
    fullProteinPanelConfirmsAllocatorFluxIsFalse :
      fullProteinPanelConfirmsAllocatorFlux ≡ false
    finiteReactionPanelConfirmsAllocatorFlux : Bool
    finiteReactionPanelConfirmsAllocatorFluxIsFalse :
      finiteReactionPanelConfirmsAllocatorFlux ≡ false
    bh4CofactorDependenceProvesConsumerCompetition : Bool
    bh4CofactorDependenceProvesConsumerCompetitionIsFalse :
      bh4CofactorDependenceProvesConsumerCompetition ≡ false
    nosPresenceProvesUncoupling : Bool
    nosPresenceProvesUncouplingIsFalse : nosPresenceProvesUncoupling ≡ false
    nitrousOxideLaneCreatesKitzerowMechanism : Bool
    nitrousOxideLaneCreatesKitzerowMechanismIsFalse :
      nitrousOxideLaneCreatesKitzerowMechanism ≡ false
    nongNangGenealogyIdentifiesNOWithN2O : Bool
    nongNangGenealogyIdentifiesNOWithN2OIsFalse :
      nongNangGenealogyIdentifiesNOWithN2O ≡ false

canonicalKitzerowBH4SystemMaxCutBoundary : KitzerowBH4SystemMaxCutBoundary
canonicalKitzerowBH4SystemMaxCutBoundary =
  kitzerow-bh4-system-maxcut-boundary
    true true true
    false refl false refl false refl false refl false refl false refl false refl

canonicalKitzerowBH4SystemNongNangMaxCutReceipt : Receipt.GenericReceipt
canonicalKitzerowBH4SystemNongNangMaxCutReceipt =
  Receipt.mkNonPromotingReceipt
    "Kitzerow BH4 system / NONG-NANG max-cut"
    "DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact"
    "exact 16/16 UniProt panel + executed 24-link Rhea panel + 12 finite reactions/3 residuals + shared BH4 state + NOS coupling + Nongin NO/N2O refinement + N2O metabolic lane"
    "closes protein and reaction acquisition and promotes reaction-level payment for QDPR, AAAH, NOS and AGMO while retaining compartment, flux, causal-transition and mechanistic-discrimination residuals"
    "complete identities and finite chemistry do not prove allocator flux, competition, NOS uncoupling, whole-model causality or NO=N2O; N2O metabolic evidence remains a separate lane"
    "python3 scripts/check_kitzerow_bh4_priority_all.py"
