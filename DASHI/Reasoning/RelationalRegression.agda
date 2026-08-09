module DASHI.Reasoning.RelationalRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared
import DASHI.Reasoning.ConditionalResponseTree as Response
import DASHI.Reasoning.DefensiveReversalRepair as Repair
import DASHI.Reasoning.IntergenerationalNameIntrusion as Slip
import DASHI.Reasoning.RelationalProcessMemoryHyperfabric as Process
import DASHI.Reasoning.RelationalFormalismSourceAtlas as Sources

parent : Core.Participant
parent = Core.participant "parent" Core.parentRole

child : Core.Participant
child = Core.participant "child" Core.childRole

siblingTemplate : Core.Participant
siblingTemplate = Core.participant "historical sibling" Core.siblingRole

boundedHelpNode : Response.PropositionNode
boundedHelpNode = Response.propositionNode
  "bounded-help"
  (Response.urgentContext
    ∷ Response.sufficientCapacity
    ∷ Response.boundedInstance
    ∷ [])
  Response.help
  Response.considerModality
  "current episode"
  "one bounded instance"
  []
  ("final commitment unresolved" ∷ [])
  "root"

boundedHelpDecision : Response.DecisionToken
boundedHelpDecision = Response.decisionToken
  "decision-0"
  (Response.urgentContext ∷ Response.sufficientCapacity ∷ [])
  ("help" ∷ "decline" ∷ "defer" ∷ [])
  "t0"
  "td"
  zero

openConsiderResponse : Response.ActualResponse
openConsiderResponse = Response.actualResponse
  child
  boundedHelpNode
  boundedHelpDecision
  "t0"
  Core.affirmStance
  Core.openZero
  Core.consideringOption
  Core.noPreference
  Core.noObligation
  (Core.capacityState 2 1 "capacity currently sufficient")
  true
  true
  true
  "explicit assent only to considering the bounded node"

correctedFamilyNameSlip : Slip.CorrectedNameIntrusion
correctedFamilyNameSlip = Slip.correctedNameIntrusion
  parent
  child
  siblingTemplate
  (Slip.nameCandidate "child name" Core.childRole 3 2 1)
  (Slip.nameCandidate "sibling name" Core.siblingRole 2 3 1)
  "si-"
  "child name"
  Slip.articulation
  Slip.familyAssociationIntrusion
  true
  true
  true
  false
  "partial competing name followed by immediate correction"

slipIsNotCompositeLabel :
  Slip.deliberateCompositeLabelUsed correctedFamilyNameSlip ≡ false
slipIsNotCompositeLabel = refl

considerNodeIsNotCommitNode :
  Response.modality boundedHelpNode ≡ Response.considerModality
considerNodeIsNotCommitNode = refl

sourceCountRegression :
  Sources.canonicalRelationalSourceCount ≡ 6
sourceCountRegression = refl

processBoundaryRejectsMoreIsAlwaysBetter :
  Process.moreBranchesAlwaysImproveOutcome
    Process.canonicalProcessMemoryAuthorityBoundary
  ≡ false
processBoundaryRejectsMoreIsAlwaysBetter = refl

repairPreservesBothQuestions :
  Repair.preserveBothQuestions Repair.canonicalRepairSequence ≡ true
repairPreservesBothQuestions = refl

sharedStateRequiresAllegationParticulars :
  Shared.allegationsRequireParticulars Shared.canonicalSharedStateInvariants ≡ true
sharedStateRequiresAllegationParticulars = refl
