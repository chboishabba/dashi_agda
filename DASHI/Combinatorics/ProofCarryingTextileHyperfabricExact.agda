module DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ProofCarryingRuleApplicationExact as RuleProof
import DASHI.Reasoning.TypedHyperfabricCore as Hyper

data ProofMotif : Set where
  premiseMotif : ProofMotif
  branchMotif : ProofMotif
  dischargeMotif : ProofMotif
  rewriteMotif : ProofMotif
  lemmaReferenceMotif : ProofMotif
  conclusionMotif : ProofMotif

record MotifAssignment (Rule : Set) : Set where
  constructor motif-assignment
  field
    motifFor : Rule → ProofMotif

open MotifAssignment public

RuleOccurrence :
  {State Rule : Set} →
  (system : RuleProof.RuleApplicationSystem State Rule) → Set
RuleOccurrence {State} system =
  Σ State (λ state → RuleProof.SelectedRuleApplication system state)

sourceState :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → State
sourceState = proj₁

selectedApplication :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (occurrence : RuleOccurrence system) →
  RuleProof.SelectedRuleApplication system (sourceState occurrence)
selectedApplication = proj₂

targetState :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → State
targetState {system = system} occurrence =
  RuleProof.applySelected system (selectedApplication occurrence)

occurrenceRule :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → Rule
occurrenceRule occurrence =
  RuleProof.selectedRule (selectedApplication occurrence)

data RuleIncidence
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule} :
    State → RuleOccurrence system → Set where
  sourceIncidence :
    (state : State)
    (selected : RuleProof.SelectedRuleApplication system state) →
    RuleIncidence state (state , selected)

  targetIncidence :
    (state : State)
    (selected : RuleProof.SelectedRuleApplication system state) →
    RuleIncidence
      (RuleProof.applySelected system selected)
      (state , selected)

ruleVertexStalk :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  State → Set
ruleVertexStalk {State} state = State

ruleEdgeStalk :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → Set
ruleEdgeStalk {State} occurrence = State × State

ruleRestrict :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  {vertex : State} {edge : RuleOccurrence system} →
  RuleIncidence vertex edge →
  ruleVertexStalk {system = system} vertex →
  ruleEdgeStalk {system = system} edge
ruleRestrict (sourceIncidence state selected) localState =
  localState , RuleProof.applySelected _ selected
ruleRestrict (targetIncidence state selected) localState =
  state , localState

ruleEdgeProvenance :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → List String
ruleEdgeProvenance occurrence =
  Dependency.dependencyReceipt
    (RuleProof.applicationProof (selectedApplication occurrence)) ∷ []

ruleEdgeSalience :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  RuleOccurrence system → Nat
ruleEdgeSalience occurrence = 1

proofRuleHyperfabric :
  {State Rule : Set} →
  (system : RuleProof.RuleApplicationSystem State Rule) →
  Hyper.TypedHyperfabric State (RuleOccurrence system)
proofRuleHyperfabric system = record
  { vertexStalk = ruleVertexStalk
  ; edgeStalk = ruleEdgeStalk
  ; incidence = RuleIncidence
  ; restrict = ruleRestrict
  ; edgeProvenance = ruleEdgeProvenance
  ; edgeSalience = ruleEdgeSalience
  ; fabricLabel = "proof-carrying textile rule hyperfabric"
  }

record CertifiedFabricPatch
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule}
    (assignment : MotifAssignment Rule)
    (occurrence : RuleOccurrence system) : Set where
  constructor certified-fabric-patch
  field
    physicalMotif : ProofMotif
    motifMatchesRule : physicalMotif ≡ motifFor assignment (occurrenceRule occurrence)

open CertifiedFabricPatch public

canonicalPatch :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (assignment : MotifAssignment Rule) →
  (occurrence : RuleOccurrence system) →
  CertifiedFabricPatch assignment occurrence
canonicalPatch assignment occurrence =
  certified-fabric-patch
    (motifFor assignment (occurrenceRule occurrence))
    refl

data CertifiedFabricTrace
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule}
    (assignment : MotifAssignment Rule) :
    {state : State} → RuleProof.CertifiedRuleTrace system state → Set₁ where
  fabricDone :
    ∀ {state} →
    CertifiedFabricTrace assignment (RuleProof.done {state = state})

  fabricChoose :
    ∀ {state}
      (selected : RuleProof.SelectedRuleApplication system state)
      {rest : RuleProof.CertifiedRuleTrace system
        (RuleProof.applySelected system selected)} →
    CertifiedFabricPatch assignment (state , selected) →
    CertifiedFabricTrace assignment rest →
    CertifiedFabricTrace assignment (RuleProof.choose selected rest)

compileCertifiedTrace :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (assignment : MotifAssignment Rule) →
  {state : State} →
  (trace : RuleProof.CertifiedRuleTrace system state) →
  CertifiedFabricTrace assignment trace
compileCertifiedTrace assignment RuleProof.done = fabricDone
compileCertifiedTrace assignment (RuleProof.choose selected rest) =
  fabricChoose
    selected
    (canonicalPatch assignment (_ , selected))
    (compileCertifiedTrace assignment rest)

WellFormedProofFabric :
  {State Rule : Set}
  (system : RuleProof.RuleApplicationSystem State Rule) →
  MotifAssignment Rule → State → Set₁
WellFormedProofFabric system assignment state =
  Σ (RuleProof.CertifiedRuleTrace system state)
    (λ trace → CertifiedFabricTrace assignment trace)

certifiedTraceToWellFormedFabric :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (assignment : MotifAssignment Rule) →
  {state : State} →
  (trace : RuleProof.CertifiedRuleTrace system state) →
  WellFormedProofFabric system assignment state
certifiedTraceToWellFormedFabric assignment trace =
  trace , compileCertifiedTrace assignment trace

wellFormedFabricCarriesCertifiedTrace :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : MotifAssignment Rule}
  {state : State} →
  WellFormedProofFabric system assignment state →
  RuleProof.CertifiedRuleTrace system state
wellFormedFabricCarriesCertifiedTrace = proj₁

record MotifMismatch
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule}
    (assignment : MotifAssignment Rule) : Set where
  constructor motif-mismatch
  field
    occurrence : RuleOccurrence system
    suppliedMotif : ProofMotif
    mismatch :
      suppliedMotif ≡ motifFor assignment (occurrenceRule occurrence) → ⊥

open MotifMismatch public

motifMismatchObstruction :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (assignment : MotifAssignment Rule) →
  (bad : MotifMismatch {system = system} assignment) →
  Hyper.HyperfabricObstruction
    (proofRuleHyperfabric system)
    (MotifMismatch {system = system} assignment)
motifMismatchObstruction assignment bad = record
  { Hyper.obstructedEdge = occurrence bad
  ; Hyper.residual = bad
  ; Hyper.obstructionProvenance =
      "physical proof motif disagrees with the rule assigned to this proof-carrying edge" ∷ []
  ; Hyper.obstructionReceipt =
      "proof-fabric local compatibility failure"
  }

data MotifLabelAloneIsProof : Set where
data VisualAdjacencyAloneIsAdmissibleRuleApplication : Set where
data FabricCertificateCreatesSourceTheoremTruth : Set where

motifLabelAloneIsNotProof : MotifLabelAloneIsProof → ⊥
motifLabelAloneIsNotProof ()

visualAdjacencyAloneIsNotAdmissibility :
  VisualAdjacencyAloneIsAdmissibleRuleApplication → ⊥
visualAdjacencyAloneIsNotAdmissibility ()

fabricCertificateDoesNotCreateSourceTruth :
  FabricCertificateCreatesSourceTheoremTruth → ⊥
fabricCertificateDoesNotCreateSourceTruth ()

record ProofCarryingTextileBoundary : Set where
  constructor proof-carrying-textile-boundary
  field
    ruleEdgesCarryTypedAdmissibility : Bool
    laterPatchesIndexedByReachedState : Bool
    proofDependenciesAreHyperfabricIncidence : Bool
    malformedMotifProducesHyperfabricObstruction : Bool
    everyCertifiedTraceCompilesToCertifiedFabric : Bool
    wellFormedFabricCarriesCertifiedTrace : Bool
    motifLabelAloneProvesRule : Bool
    visiblePatternCreatesTheoremTruth : Bool

canonicalProofCarryingTextileBoundary : ProofCarryingTextileBoundary
canonicalProofCarryingTextileBoundary =
  proof-carrying-textile-boundary
    true true true true true true false false
