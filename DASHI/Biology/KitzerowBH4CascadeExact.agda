module DASHI.Biology.KitzerowBH4CascadeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate empirical graph for Kitzerow's Autism and the Comorbidities
-- Cascade.  Nodes and edges are represented as claims with explicit status.
-- Nothing in this owner promotes the whole graph to established mechanism.
------------------------------------------------------------------------

data CascadeNode : Set where
  geneticEpigeneticSituational : CascadeNode
  chronicAllostasis : CascadeNode
  gch1RedoxBH4Allocation : CascadeNode
  aaahHydroxylases : CascadeNode
  precursorReallocation : CascadeNode
  eiCSTLCircuitry : CascadeNode
  nosCouplingState : CascadeNode
  redoxSensitiveProteinRegulation : CascadeNode
  mTORPruning : CascadeNode
  systemicComorbidityTraits : CascadeNode
  agmoEtherLipidCatabolism : CascadeNode
  endocannabinoidSignalling : CascadeNode
  socialRegulatoryTraits : CascadeNode
  autismComorbidityClustering : CascadeNode
  allostaticOverloadProgression : CascadeNode

data EdgeStatus : Set where
  kitzerowProposed : EdgeStatus
  priorBiologyInherited : EdgeStatus
  boundedEmpiricalSupport : EdgeStatus
  directInterventionalSupport : EdgeStatus
  qualifiedSupport : EdgeStatus
  conflictingEvidence : EdgeStatus
  underDetermined : EdgeStatus
  unpaid : EdgeStatus

record CascadeEdge : Set where
  constructor cascadeEdge
  field
    edgeLabel : String
    sourceNode : CascadeNode
    targetNode : CascadeNode
    status : EdgeStatus
    claimReading : String

open CascadeEdge public

canonicalEdges : List CascadeEdge
canonicalEdges =
  cascadeEdge
    "context -> chronic allostasis"
    geneticEpigeneticSituational chronicAllostasis
    kitzerowProposed
    "genetic, epigenetic and situational demand is proposed to contribute to sustained stress-response activation"
  ∷ cascadeEdge
    "allostasis -> redox-regulated BH4 allocation"
    chronicAllostasis gch1RedoxBH4Allocation
    unpaid
    "central resource-reallocation edge; currently requires same-object experimental discrimination"
  ∷ cascadeEdge
    "BH4 allocation -> AAAH branch"
    gch1RedoxBH4Allocation aaahHydroxylases
    kitzerowProposed
    "candidate redistribution across BH4-dependent aromatic amino-acid hydroxylases"
  ∷ cascadeEdge
    "AAAH branch -> precursor reallocation"
    aaahHydroxylases precursorReallocation
    kitzerowProposed
    "candidate monoamine / aromatic-amino-acid precursor redistribution"
  ∷ cascadeEdge
    "precursor reallocation -> E/I CSTL circuitry"
    precursorReallocation eiCSTLCircuitry
    underDetermined
    "downstream circuit relation remains context- and mechanism-dependent"
  ∷ cascadeEdge
    "BH4 allocation -> NOS coupling state"
    gch1RedoxBH4Allocation nosCouplingState
    kitzerowProposed
    "candidate BH4-dependent NOS coupling/uncoupling branch"
  ∷ cascadeEdge
    "NOS state -> redox-sensitive protein regulation"
    nosCouplingState redoxSensitiveProteinRegulation
    boundedEmpiricalSupport
    "later work supports nitric-oxide-linked redox-sensitive protein regulation in bounded autism-model contexts"
  ∷ cascadeEdge
    "redox-sensitive regulation -> mTOR/pruning"
    redoxSensitiveProteinRegulation mTORPruning
    directInterventionalSupport
    "NO/TSC2/mTOR experiments support this internal downstream edge in specific model systems"
  ∷ cascadeEdge
    "BH4 allocation -> AGMO branch"
    gch1RedoxBH4Allocation agmoEtherLipidCatabolism
    kitzerowProposed
    "candidate BH4-dependent AGMO/ether-lipid branch"
  ∷ cascadeEdge
    "AGMO branch -> endocannabinoid signalling"
    agmoEtherLipidCatabolism endocannabinoidSignalling
    unpaid
    "specific autism-cascade bridge remains experimentally unpaid"
  ∷ cascadeEdge
    "endocannabinoid signalling -> social-regulatory traits"
    endocannabinoidSignalling socialRegulatoryTraits
    underDetermined
    "association is compatible with multiple causal architectures"
  ∷ cascadeEdge
    "branch outputs -> autism/comorbidity clustering"
    systemicComorbidityTraits autismComorbidityClustering
    underDetermined
    "trait clustering is not by itself identification of a unique upstream mechanism"
  ∷ cascadeEdge
    "persistent clustering -> chronic progressive conditions"
    autismComorbidityClustering allostaticOverloadProgression
    kitzerowProposed
    "prolonged pathway activation / cumulative loss of functional resilience is a proposed terminal trajectory"
  ∷ []

record KitzerowBH4Cascade : Set where
  constructor kitzerowBH4Cascade
  field
    edges : List CascadeEdge
    candidateEmpiricalGraph : Bool
    candidateEmpiricalGraphIsTrue : candidateEmpiricalGraph ≡ true
    wholeModelConfirmed : Bool
    wholeModelConfirmedIsFalse : wholeModelConfirmed ≡ false
    clinicalAuthorityClaimed : Bool
    clinicalAuthorityClaimedIsFalse : clinicalAuthorityClaimed ≡ false

open KitzerowBH4Cascade public

canonicalKitzerowBH4Cascade : KitzerowBH4Cascade
canonicalKitzerowBH4Cascade =
  kitzerowBH4Cascade canonicalEdges true refl false refl false refl
