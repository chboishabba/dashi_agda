module DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas
import DASHI.Biology.UniProtExternalKnowledgeExact as UniProt
import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide
import DASHI.Biology.NitrousOxideMetabolismEvidenceExact as Nang
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as Nongin
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- KITZEROW BH4 SYSTEM / NONG-NANG MAX-CUT
--
-- This is the graph-population owner.  Panel entries are acquisition targets,
-- not assertions that every record has already been byte-pinned.  QDPR is the
-- first exact certificate.  Each proposed mechanistic edge carries independent
-- identity/reaction/compartment/flux/causal payment coordinates.
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
gch1 = protein-panel-member "GCH1" "P30793" "BH4 synthesis / regulation" Atlas.gch1RedoxRegulation (Atlas.bh4Availability ∷ []) false

gchfr : ProteinPanelMember
gchfr = protein-panel-member "GCHFR" "P30047" "GCH1 feedback regulation" Atlas.gch1RedoxRegulation [] false

pts : ProteinPanelMember
pts = protein-panel-member "PTS" "Q03393" "BH4 synthesis" Atlas.bh4Availability [] false

spr : ProteinPanelMember
spr = protein-panel-member "SPR" "P35270" "BH4 synthesis" Atlas.bh4Availability [] false

pcbd1 : ProteinPanelMember
pcbd1 = protein-panel-member "PCBD1" "P61457" "BH4 recycling" Atlas.bh4Availability [] false

qdpr : ProteinPanelMember
qdpr = protein-panel-member "QDPR" "P09417" "BH4 recycling" Atlas.bh4Availability [] true

nos1 : ProteinPanelMember
nos1 = protein-panel-member "NOS1" "P29475" "neuronal nitric-oxide synthase" Atlas.nosUncoupling (Atlas.noTsc2Mtor ∷ []) false

nos2 : ProteinPanelMember
nos2 = protein-panel-member "NOS2" "P35228" "inducible nitric-oxide synthase" Atlas.nosUncoupling (Atlas.neuroimmuneCascade ∷ []) false

nos3 : ProteinPanelMember
nos3 = protein-panel-member "NOS3" "P29474" "endothelial nitric-oxide synthase" Atlas.nosUncoupling [] false

pah : ProteinPanelMember
pah = protein-panel-member "PAH" "P00439" "aromatic amino-acid hydroxylase" Atlas.aaaHBranch [] false

th : ProteinPanelMember
th = protein-panel-member "TH" "P07101" "catecholamine AAAH" Atlas.aaaHBranch (Atlas.synapticProteinRegulation ∷ []) false

tph1 : ProteinPanelMember
tph1 = protein-panel-member "TPH1" "P17752" "peripheral serotonin AAAH" Atlas.aaaHBranch (Atlas.neuroimmuneCascade ∷ []) false

tph2 : ProteinPanelMember
tph2 = protein-panel-member "TPH2" "Q8IWU9" "neuronal serotonin AAAH" Atlas.aaaHBranch (Atlas.excitatoryInhibitoryCircuitState ∷ []) false

agmo : ProteinPanelMember
agmo = protein-panel-member "AGMO" "Q6ZNB7" "BH4-dependent ether-lipid cleavage" Atlas.cellStressTranslationState [] false

tsc2 : ProteinPanelMember
tsc2 = protein-panel-member "TSC2" "P49815" "NO downstream / TSC2-mTOR" Atlas.noTsc2Mtor [] false

mtor : ProteinPanelMember
mtor = protein-panel-member "MTOR" "P42345" "TSC2-mTOR signaling" Atlas.noTsc2Mtor (Atlas.cellStressTranslationState ∷ []) false

kitzerowBH4ProteinPanel : List ProteinPanelMember
kitzerowBH4ProteinPanel =
  gch1 ∷ gchfr ∷ pts ∷ spr ∷ pcbd1 ∷ qdpr
  ∷ nos1 ∷ nos2 ∷ nos3
  ∷ pah ∷ th ∷ tph1 ∷ tph2
  ∷ agmo ∷ tsc2 ∷ mtor ∷ []

------------------------------------------------------------------------
-- Edge-payment matrix.  "Paid" here means paid at the stated bounded layer;
-- it never means the whole disease mechanism has been established.
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
    "RHEA:17869 / BH4-regeneration annotation"
    Atlas.bh4Availability
    true true false false false
    "exact protein/reaction annotation is paid; measured compartmental BH4/BH2 state, regeneration flux and disease-level causal transition remain unpaid"

bh4ToNOSCouplingEdge : MechanisticEdgePayment
bh4ToNOSCouplingEdge =
  mechanistic-edge-payment
    "EDGE-BH4-NOS-COUPLING"
    "shared BH4/BH2/redox system state"
    "NOS1/NOS2/NOS3 coupling state and NO/superoxide output"
    Atlas.nosUncoupling
    false false false false false
    "requires isoform-specific identity certificates plus same-compartment BH4/BH2, substrate, redox and product measurements and an interventional coupling-transition witness"

nosToTSC2Edge : MechanisticEdgePayment
nosToTSC2Edge =
  mechanistic-edge-payment
    "EDGE-NO-TSC2-MTOR"
    "NO / S-nitrosylation state"
    "TSC2 -> mTOR dysregulation"
    Atlas.noTsc2Mtor
    false true false false false
    "PR #1159 records strong downstream intervention evidence; same-object transport from the proposed upstream BH4/NOS state into that experiment remains required"

aaahCompetitionEdge : MechanisticEdgePayment
aaahCompetitionEdge =
  mechanistic-edge-payment
    "EDGE-BH4-AAAH-COMPETITION"
    "shared BH4 system state"
    "PAH/TH/TPH1/TPH2 activity"
    Atlas.aaaHBranch
    false false false false false
    "cofactor requirement can be acquired per enzyme, but competition/allocation requires simultaneous compartmental demand and flux payment"

agmoCompetitionEdge : MechanisticEdgePayment
agmoCompetitionEdge =
  mechanistic-edge-payment
    "EDGE-BH4-AGMO-COMPETITION"
    "shared BH4 system state"
    "AGMO ether-lipid cleavage"
    Atlas.cellStressTranslationState
    false false false false false
    "AGMO BH4 dependence can pay an isolated biochemical node; allocator competition and downstream cell-stress consequences remain separate obligations"

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

liveResiduals : List KitzerowBH4SystemResidual
liveResiduals =
  acquireRemainingProteinCertificates
  ∷ acquireRheaReactionWitnesses
  ∷ acquirePDBSIFTSResidueWitnesses
  ∷ acquirePrimaryMechanisticExperiments
  ∷ payCompartmentSpecificBH4BH2State
  ∷ paySimultaneousConsumerDemand
  ∷ payTransportAndOxidationFlux
  ∷ payNOSCouplingTransitions
  ∷ payUpstreamToTSC2SameObjectTransport
  ∷ testWholeSystemFluxBalance
  ∷ testAlternativeMechanisms
  ∷ []

record KitzerowBH4SystemMaxCutBoundary : Set where
  constructor kitzerow-bh4-system-maxcut-boundary
  field
    isolatedNodeSupportConfirmsWholeGraph : Bool
    isolatedNodeSupportConfirmsWholeGraphIsFalse :
      isolatedNodeSupportConfirmsWholeGraph ≡ false
    fullProteinPanelConfirmsAllocatorFlux : Bool
    fullProteinPanelConfirmsAllocatorFluxIsFalse :
      fullProteinPanelConfirmsAllocatorFlux ≡ false
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
    false refl false refl false refl false refl false refl false refl

canonicalKitzerowBH4SystemNongNangMaxCutReceipt : Receipt.GenericReceipt
canonicalKitzerowBH4SystemNongNangMaxCutReceipt =
  Receipt.mkNonPromotingReceipt
    "Kitzerow BH4 system / NONG-NANG max-cut"
    "DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact"
    "16-protein acquisition panel + shared BH4 state + NOS coupling + Nongin NO/N2O refinement + N2O metabolic lane"
    "turns isolated pathway annotations into an explicit edge-payment matrix and live mechanistic residual frontier"
    "node/panel support does not prove allocator flux, competition, NOS uncoupling, whole-model causality or NO=N2O; N2O metabolic evidence remains a separate lane"
    "python3 scripts/acquire_uniprot_bio_certificate.py --kitzerow-bh4-panel && agda -i . DASHI/Biology/KitzerowBH4SystemNongNangMaxCutExact.agda"
