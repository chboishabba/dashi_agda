module DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.BodyMemoryCompiledInverseBridge as Body
import DASHI.Cognition.PNF.BraidLearningTransport as Braid
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.OperationalIR as IR
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Body-memory channels are typed fibres, not diagnoses.
------------------------------------------------------------------------

data BodyMemoryChannel : Set where
  breathChannel : BodyMemoryChannel
  postureChannel : BodyMemoryChannel
  arousalChannel : BodyMemoryChannel
  affectChannel : BodyMemoryChannel
  sensoryChannel : BodyMemoryChannel
  memoryChannel : BodyMemoryChannel
  relationChannel : BodyMemoryChannel
  agencyChannel : BodyMemoryChannel

record ChannelMemoryState : Set where
  field
    channel : BodyMemoryChannel
    memory : Memory.VersionedMemory
    residual : Residual.ResidualLevel
    channelReceipt : String
    narrativeAccessComplete : Bool
    diagnosisPromoted : Bool

------------------------------------------------------------------------
-- A PNF memory hypervoxel stores semantic and body-memory state at each
-- recursively addressed lifted site.  The lift may be centre-sensitive: a
-- consumer must not silently quotient away provenance, phase or action bias.
------------------------------------------------------------------------

record PNFMemoryHypervoxel (rank depth : Nat) : Set₁ where
  field
    resolvedSemanticState : PNF.ResolvedPNF
    memoryIR : IR.DomainIR
    memoryIRSourceLaw :
      IR.sourcePNF memoryIR ≡ resolvedSemanticState

    channelAt :
      Hyper.LiftedAddress rank depth → BodyMemoryChannel
    memoryAt :
      Hyper.LiftedAddress rank depth → Memory.VersionedMemory
    residualAt :
      Hyper.LiftedAddress rank depth → Residual.ResidualLevel

    liftedMemoryField :
      Hyper.LiftedField rank depth Memory.MemoryFibre

    bodyMemoryInverseRoute : Body.CompiledInverseRoute
    inverseRouteCandidateOnly :
      bodyMemoryInverseRoute ≡ Body.candidateOnlyCompiledInverseRoute

    narrativeSurfaceComplete : Bool
    traumaDiagnosisPromoted : Bool
    clinicalAuthorityPromoted : Bool

------------------------------------------------------------------------
-- Learning is a PNF-preserving fibre transformation, not a replacement of
-- semantic content.  Revaluation, habituation, reinforcement, extinction and
-- phase realignment alter weights/topology while retaining the remembered PNF.
------------------------------------------------------------------------

record PNFHypervoxelLearningStep (rank depth : Nat) : Set₁ where
  field
    source target : PNFMemoryHypervoxel rank depth
    site : Hyper.LiftedAddress rank depth
    learningReceipt : Learning.LearningReceipt
    beforeMatchesSource :
      Learning.before learningReceipt ≡
      Hyper.liftedFieldValue
        (PNFMemoryHypervoxel.liftedMemoryField source)
        site
    afterMatchesTarget :
      Learning.after learningReceipt ≡
      Hyper.liftedFieldValue
        (PNFMemoryHypervoxel.liftedMemoryField target)
        site
    rememberedPNFPreserved :
      Memory.rememberedEvent (Learning.after learningReceipt)
      ≡ Memory.rememberedEvent (Learning.before learningReceipt)
    publicCategoryPreserved : Bool
    oldMemoryVersionRetained : Bool
    learningDoesNotEraseTraumaClaimed : Bool

------------------------------------------------------------------------
-- Memory, expectation, action and observation form a braid.  Transport order
-- may retain a residual; it is not collapsed to one commutative update.
------------------------------------------------------------------------

record PNFMemoryBraidHypervoxel (rank depth : Nat) : Set₁ where
  field
    carrier : PNFMemoryHypervoxel rank depth
    laneAt : Hyper.LiftedAddress rank depth → Braid.PNFLaneState
    braidOrder : Braid.BraidOrderReceipt
    transportOrderMayMatter : Bool
    nonCommutingResidualRetained : Bool
    expectationActionFeedbackPresent : Bool

------------------------------------------------------------------------
-- Stage transitions consume the actual PNF/memory fibre rather than a Nat-only
-- depth summary.  The public stage edge is a projection of a richer hidden
-- transition carrying revision, learning, braid and residual evidence.
------------------------------------------------------------------------

record PNFStageHypervoxelTransition (rank depth : Nat) : Set₁ where
  field
    source target : PNFMemoryHypervoxel rank depth
    sourceStage targetStage : Atlas.StageAtlasZeroToEleven
    guardedEdge : Stage.GuardedStageEdge sourceStage targetStage
    semanticRevision : PNF.PNFRevision
    learningStep : PNFHypervoxelLearningStep rank depth
    braidReceipt : Braid.BraidOrderReceipt
    unresolvedResidualCount : Nat
    memoryConsumed : Bool
    learnedTransportConsumed : Bool
    residualsRetained : Bool
    directStagePromotionFromTraumaClaimed : Bool
    diagnosisFromResidualClaimed : Bool

record TraumaMemoryHypervoxelAuthorityBoundary : Set where
  field
    pnfOwnsSemanticTransformation : Bool
    memoryIsPNFValuedAndVersioned : Bool
    learningPreservesRememberedPNF : Bool
    traumaResidualIsCrossFibreMismatchCandidate : Bool
    bodyChannelsAreHypervoxelFibres : Bool
    braidOrderResidualIsRetained : Bool
    stageConsumesRichMemoryFibre : Bool
    residualAloneProvesTrauma : Bool
    formalCarrierDiagnosesPerson : Bool
    extinctionErasesMemory : Bool
    narrativeAccessRequiredForBodyMemory : Bool

canonicalTraumaMemoryHypervoxelAuthorityBoundary :
  TraumaMemoryHypervoxelAuthorityBoundary
canonicalTraumaMemoryHypervoxelAuthorityBoundary = record
  { pnfOwnsSemanticTransformation = true
  ; memoryIsPNFValuedAndVersioned = true
  ; learningPreservesRememberedPNF = true
  ; traumaResidualIsCrossFibreMismatchCandidate = true
  ; bodyChannelsAreHypervoxelFibres = true
  ; braidOrderResidualIsRetained = true
  ; stageConsumesRichMemoryFibre = true
  ; residualAloneProvesTrauma = false
  ; formalCarrierDiagnosesPerson = false
  ; extinctionErasesMemory = false
  ; narrativeAccessRequiredForBodyMemory = false
  }

traumaMemoryHypervoxelSummary : String
traumaMemoryHypervoxelSummary =
  "PNF supplies the semantic algebra; versioned memory, learning receipts and noncommuting braid transport form fibres over recursive hypervoxel addresses, while body-memory residuals remain candidate cross-fibre mismatches rather than trauma diagnoses."
