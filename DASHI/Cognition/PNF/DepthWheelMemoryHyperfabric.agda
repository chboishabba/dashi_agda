module DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Depth
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Empirical motivation boundary.
--
-- These references motivate keeping retrieval/update, extinction and context
-- sensitivity distinct.  They are not imported as proof authority for the
-- abstract C3 grading, nor does this module infer a diagnosis from them.
--
-- Karim Nader, Glenn E. Schafe, Joseph E. LeDoux,
-- "Fear memories require protein synthesis in the amygdala for reconsolidation
-- after retrieval", Nature 406 (2000), 722-726.
-- DOI: 10.1038/35021052
--
-- Mark E. Bouton,
-- "Context and behavioral processes in extinction", Learning & Memory 11
-- (2004), 485-494.
-- DOI: 10.1101/lm.78804
--
-- Daniela Schiller, Marie-H. Monfils, Candace M. Raio, David C. Johnson,
-- Joseph E. LeDoux, Elizabeth A. Phelps,
-- "Preventing the return of fear in humans using reconsolidation update
-- mechanisms", Nature 463 (2010), 49-53.
-- DOI: 10.1038/nature08637
-- An addendum was published in 2018; the reference remains motivation only.

------------------------------------------------------------------------
-- Memory-preserving updates.

record MemoryPreservingUpdate : Set₁ where
  constructor memoryPreservingUpdate
  field
    apply : Memory.MemoryFibre → Memory.MemoryFibre
    rememberedPNFPreserved :
      (memory : Memory.MemoryFibre) →
      Memory.rememberedEvent (apply memory)
      ≡ Memory.rememberedEvent memory

open MemoryPreservingUpdate public

revaluationUpdate : Nat → MemoryPreservingUpdate
revaluationUpdate value =
  memoryPreservingUpdate
    (λ memory → Memory.revalue memory value)
    (λ memory → Memory.revaluePreservesRememberedEvent memory value)

habituationUpdate : MemoryPreservingUpdate
habituationUpdate =
  memoryPreservingUpdate
    Memory.habituate
    Memory.habituationPreservesRememberedEvent

reinforcementUpdate : MemoryPreservingUpdate
reinforcementUpdate =
  memoryPreservingUpdate
    Memory.reinforce
    (λ memory → refl)

extinctionUpdate : MemoryPreservingUpdate
extinctionUpdate =
  memoryPreservingUpdate
    Memory.extinguishActionDominance
    Memory.extinctionPreservesRememberedEvent

------------------------------------------------------------------------
-- C3-graded memory fibre.

record WheelMemoryFibre : Set where
  constructor wheelMemoryFibre
  field
    memory : Memory.MemoryFibre
    refinementDepth : Nat
    phaseMatchesDepth :
      Memory.phase memory
      ≡ Depth.phaseOrdinal (Wheel.depthWheelPhase refinementDepth)

open WheelMemoryFibre public

wheelPhase : WheelMemoryFibre → Wheel.DepthWheelPhase
wheelPhase fibre = Wheel.depthWheelPhase (refinementDepth fibre)

wheelCoordinate : WheelMemoryFibre → Depth.WheelDepthCoordinate
wheelCoordinate fibre = Depth.wheelDepthCoordinate (refinementDepth fibre)

completedLearningWheels : WheelMemoryFibre → Nat
completedLearningWheels fibre =
  Depth.completedWheels (wheelCoordinate fibre)

publicMemoryProjection : WheelMemoryFibre → PNF.EventPNF
publicMemoryProjection fibre = Memory.rememberedEvent (memory fibre)

alignMemoryAtDepth : Memory.MemoryFibre → Nat → WheelMemoryFibre
alignMemoryAtDepth memory depth =
  wheelMemoryFibre
    (Memory.realignPhase memory
      (Depth.phaseOrdinal (Wheel.depthWheelPhase depth)))
    depth
    refl

alignmentPreservesRememberedPNF :
  (memory : Memory.MemoryFibre) →
  (depth : Nat) →
  publicMemoryProjection (alignMemoryAtDepth memory depth)
  ≡ Memory.rememberedEvent memory
alignmentPreservesRememberedPNF memory depth = refl

alignedDepthZeroPhaseIsZero :
  (memory : Memory.MemoryFibre) →
  Memory.phase (WheelMemoryFibre.memory (alignMemoryAtDepth memory 0)) ≡ 0
alignedDepthZeroPhaseIsZero memory = refl

------------------------------------------------------------------------
-- One elementary graded learning step.

advancePreservingUpdate :
  MemoryPreservingUpdate →
  WheelMemoryFibre →
  WheelMemoryFibre
advancePreservingUpdate update source =
  alignMemoryAtDepth
    (apply update (memory source))
    (suc (refinementDepth source))

advancePreservesRememberedPNF :
  (update : MemoryPreservingUpdate) →
  (source : WheelMemoryFibre) →
  publicMemoryProjection (advancePreservingUpdate update source)
  ≡ publicMemoryProjection source
advancePreservesRememberedPNF update source =
  rememberedPNFPreserved update (memory source)

advanceMovesDepth :
  (update : MemoryPreservingUpdate) →
  (source : WheelMemoryFibre) →
  refinementDepth (advancePreservingUpdate update source)
  ≡ suc (refinementDepth source)
advanceMovesDepth update source = refl

advanceMovesPhase :
  (update : MemoryPreservingUpdate) →
  (source : WheelMemoryFibre) →
  wheelPhase (advancePreservingUpdate update source)
  ≡ Wheel.nextDepthWheelPhase (wheelPhase source)
advanceMovesPhase update source = refl

record WheelLearningTransition : Set₁ where
  constructor wheelLearningTransition
  field
    update : MemoryPreservingUpdate
    source target : WheelMemoryFibre
    targetIsAdvance : target ≡ advancePreservingUpdate update source
    rememberedPNFInvariant :
      publicMemoryProjection target ≡ publicMemoryProjection source
    depthAdvancesByOne :
      refinementDepth target ≡ suc (refinementDepth source)
    phaseAdvancesByOne :
      wheelPhase target ≡ Wheel.nextDepthWheelPhase (wheelPhase source)

open WheelLearningTransition public

mkWheelLearningTransition :
  (update : MemoryPreservingUpdate) →
  (source : WheelMemoryFibre) →
  WheelLearningTransition
mkWheelLearningTransition update source =
  wheelLearningTransition
    update
    source
    (advancePreservingUpdate update source)
    refl
    (advancePreservesRememberedPNF update source)
    refl
    refl

------------------------------------------------------------------------
-- Existing named learning operations embedded into the graded lane.

revaluationWheelTransition :
  Nat → WheelMemoryFibre → WheelLearningTransition
revaluationWheelTransition value =
  mkWheelLearningTransition (revaluationUpdate value)

habituationWheelTransition :
  WheelMemoryFibre → WheelLearningTransition
habituationWheelTransition =
  mkWheelLearningTransition habituationUpdate

reinforcementWheelTransition :
  WheelMemoryFibre → WheelLearningTransition
reinforcementWheelTransition =
  mkWheelLearningTransition reinforcementUpdate

extinctionWheelTransition :
  WheelMemoryFibre → WheelLearningTransition
extinctionWheelTransition =
  mkWheelLearningTransition extinctionUpdate

extinctionWheelActionWeightIsZero :
  (source : WheelMemoryFibre) →
  Memory.actionWeight
    (memory (target (extinctionWheelTransition source)))
  ≡ zero
extinctionWheelActionWeightIsZero source = refl

extinctionWheelPreservesRememberedPNF :
  (source : WheelMemoryFibre) →
  publicMemoryProjection (target (extinctionWheelTransition source))
  ≡ publicMemoryProjection source
extinctionWheelPreservesRememberedPNF source =
  rememberedPNFInvariant (extinctionWheelTransition source)

------------------------------------------------------------------------
-- Same public PNF does not imply same full memory state.

oneNotZero : suc zero ≡ zero → ⊥
oneNotZero ()

depthZeroAdvanceChangesFullMemory :
  (update : MemoryPreservingUpdate) →
  (raw : Memory.MemoryFibre) →
  memory (advancePreservingUpdate update (alignMemoryAtDepth raw 0))
  ≡ memory (alignMemoryAtDepth raw 0) →
  ⊥
depthZeroAdvanceChangesFullMemory update raw equality =
  oneNotZero (cong Memory.phase equality)

depthZeroAdvancePreservesPublicPNF :
  (update : MemoryPreservingUpdate) →
  (raw : Memory.MemoryFibre) →
  publicMemoryProjection
    (advancePreservingUpdate update (alignMemoryAtDepth raw 0))
  ≡ publicMemoryProjection (alignMemoryAtDepth raw 0)
depthZeroAdvancePreservesPublicPNF update raw =
  advancePreservesRememberedPNF update (alignMemoryAtDepth raw 0)

------------------------------------------------------------------------
-- One complete learning wheel.

record ThreePhaseLearningProgram : Set₁ where
  constructor threePhaseLearningProgram
  field
    phase0Update phase1Update phase2Update : MemoryPreservingUpdate

open ThreePhaseLearningProgram public

runOneLearningWheel :
  ThreePhaseLearningProgram →
  WheelMemoryFibre →
  WheelMemoryFibre
runOneLearningWheel program source =
  advancePreservingUpdate (phase2Update program)
    (advancePreservingUpdate (phase1Update program)
      (advancePreservingUpdate (phase0Update program) source))

oneLearningWheelAdvancesDepthByThree :
  (program : ThreePhaseLearningProgram) →
  (source : WheelMemoryFibre) →
  refinementDepth (runOneLearningWheel program source)
  ≡ suc (suc (suc (refinementDepth source)))
oneLearningWheelAdvancesDepthByThree program source = refl

oneLearningWheelReturnsToSamePhase :
  (program : ThreePhaseLearningProgram) →
  (source : WheelMemoryFibre) →
  wheelPhase (runOneLearningWheel program source)
  ≡ wheelPhase source
oneLearningWheelReturnsToSamePhase program source =
  Wheel.depthWheelPhaseAfterThree (refinementDepth source)

oneLearningWheelPreservesRememberedPNF :
  (program : ThreePhaseLearningProgram) →
  (source : WheelMemoryFibre) →
  publicMemoryProjection (runOneLearningWheel program source)
  ≡ publicMemoryProjection source
oneLearningWheelPreservesRememberedPNF program source =
  trans
    (advancePreservesRememberedPNF
      (phase2Update program)
      (advancePreservingUpdate (phase1Update program)
        (advancePreservingUpdate (phase0Update program) source)))
    (trans
      (advancePreservesRememberedPNF
        (phase1Update program)
        (advancePreservingUpdate (phase0Update program) source))
      (advancePreservesRememberedPNF (phase0Update program) source))

canonicalRevalueHabituateReinforceWheel : Nat → ThreePhaseLearningProgram
canonicalRevalueHabituateReinforceWheel value =
  threePhaseLearningProgram
    (revaluationUpdate value)
    habituationUpdate
    reinforcementUpdate

------------------------------------------------------------------------
-- Existing LearningReceipt and FibreLearningUpdate remain live dependencies.

record ExistingLearningWheelBridge : Set₁ where
  constructor existingLearningWheelBridge
  field
    wheelTransition : WheelLearningTransition
    learningReceipt : Learning.LearningReceipt
    fibreUpdate : FibreLearning.FibreLearningUpdate
    receiptBeforeMatchesWheelSource :
      Learning.before learningReceipt ≡ memory (source wheelTransition)
    receiptAfterMatchesFibreAfter :
      Learning.after learningReceipt ≡ FibreLearning.after fibreUpdate
    fibreRememberedPNFPreserved :
      Memory.rememberedEvent (FibreLearning.after fibreUpdate)
      ≡ Memory.rememberedEvent (FibreLearning.before fibreUpdate)

------------------------------------------------------------------------
-- Hyperfabric cross-fibre phase geometry.

phaseDistance :
  Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Nat
phaseDistance Wheel.phase-0 Wheel.phase-0 = 0
phaseDistance Wheel.phase-1 Wheel.phase-1 = 0
phaseDistance Wheel.phase-2 Wheel.phase-2 = 0
phaseDistance _ _ = 1

phaseDistanceSelf :
  (phase : Wheel.DepthWheelPhase) → phaseDistance phase phase ≡ 0
phaseDistanceSelf Wheel.phase-0 = refl
phaseDistanceSelf Wheel.phase-1 = refl
phaseDistanceSelf Wheel.phase-2 = refl

phaseDistanceSymmetric :
  (left right : Wheel.DepthWheelPhase) →
  phaseDistance left right ≡ phaseDistance right left
phaseDistanceSymmetric Wheel.phase-0 Wheel.phase-0 = refl
phaseDistanceSymmetric Wheel.phase-0 Wheel.phase-1 = refl
phaseDistanceSymmetric Wheel.phase-0 Wheel.phase-2 = refl
phaseDistanceSymmetric Wheel.phase-1 Wheel.phase-0 = refl
phaseDistanceSymmetric Wheel.phase-1 Wheel.phase-1 = refl
phaseDistanceSymmetric Wheel.phase-1 Wheel.phase-2 = refl
phaseDistanceSymmetric Wheel.phase-2 Wheel.phase-0 = refl
phaseDistanceSymmetric Wheel.phase-2 Wheel.phase-1 = refl
phaseDistanceSymmetric Wheel.phase-2 Wheel.phase-2 = refl

record ChannelWheelState : Set where
  constructor channelWheelState
  field
    channel : Trauma.BodyMemoryChannel
    state : WheelMemoryFibre

open ChannelWheelState public

record ChannelPhaseCoupling : Set where
  constructor channelPhaseCoupling
  field
    left right : ChannelWheelState
    couplingWeight : Nat

open ChannelPhaseCoupling public

couplingFrustration : ChannelPhaseCoupling → Nat
couplingFrustration coupling =
  couplingWeight coupling *
  phaseDistance
    (wheelPhase (state (left coupling)))
    (wheelPhase (state (right coupling)))

fabricPhaseFrustration : List ChannelPhaseCoupling → Nat
fabricPhaseFrustration [] = 0
fabricPhaseFrustration (coupling ∷ rest) =
  couplingFrustration coupling + fabricPhaseFrustration rest

------------------------------------------------------------------------
-- Link back to an actual site of the existing trauma-memory hypervoxel.

record DepthWheelHypervoxelSite (rank depth : Nat) : Set₁ where
  constructor depthWheelHypervoxelSite
  field
    carrier : Trauma.PNFMemoryHypervoxel rank depth
    site : Hyper.LiftedAddress rank depth
    learningDepth : Nat
    learningDepthWithinSpatialDepth : learningDepth ≤ depth
    sourceVersionedMemory : Memory.VersionedMemory
    sourceVersionedMemoryMatchesSite :
      sourceVersionedMemory ≡ Trauma.PNFMemoryHypervoxel.memoryAt carrier site
    gradedMemory : WheelMemoryFibre
    gradedMemoryIsAlignedCurrent :
      gradedMemory
      ≡ alignMemoryAtDepth (Memory.current sourceVersionedMemory) learningDepth

open DepthWheelHypervoxelSite public

hypervoxelSiteAlignmentPreservesPNF :
  ∀ {rank depth}
    (siteBridge : DepthWheelHypervoxelSite rank depth) →
  publicMemoryProjection (gradedMemory siteBridge)
  ≡ Memory.rememberedEvent (Memory.current (sourceVersionedMemory siteBridge))
hypervoxelSiteAlignmentPreservesPNF siteBridge
  rewrite gradedMemoryIsAlignedCurrent siteBridge = refl

hypervoxelSiteAlignmentPreservesSitePNF :
  ∀ {rank depth}
    (siteBridge : DepthWheelHypervoxelSite rank depth) →
  publicMemoryProjection (gradedMemory siteBridge)
  ≡ Memory.rememberedEvent
      (Memory.current
        (Trauma.PNFMemoryHypervoxel.memoryAt
          (carrier siteBridge)
          (site siteBridge)))
hypervoxelSiteAlignmentPreservesSitePNF siteBridge
  rewrite gradedMemoryIsAlignedCurrent siteBridge
        | sourceVersionedMemoryMatchesSite siteBridge = refl

------------------------------------------------------------------------
-- Authority boundary.

record DepthWheelMemoryHyperfabricBoundary : Set where
  constructor depthWheelMemoryHyperfabricBoundary
  field
    memoryPhaseIsExplicitlyC3GradedHere : Bool
    rememberedPNFPreservedAcrossWheelUpdates : Bool
    samePublicPNFCanHideDifferentWheelPhase : Bool
    extinctionErasesRememberedPNF : Bool
    extinctionErasesRememberedPNFIsFalse :
      extinctionErasesRememberedPNF ≡ false
    crossFibrePhaseMismatchIsCandidateGeometry : Bool
    phaseFrustrationDiagnosesTrauma : Bool
    phaseFrustrationDiagnosesTraumaIsFalse :
      phaseFrustrationDiagnosesTrauma ≡ false
    learningDepthEqualsSpatialHypervoxelDepthUniversally : Bool
    learningDepthEqualsSpatialHypervoxelDepthUniversallyIsFalse :
      learningDepthEqualsSpatialHypervoxelDepthUniversally ≡ false
    empiricalReconsolidationPaperProvesC3Wheel : Bool
    empiricalReconsolidationPaperProvesC3WheelIsFalse :
      empiricalReconsolidationPaperProvesC3Wheel ≡ false

canonicalDepthWheelMemoryHyperfabricBoundary :
  DepthWheelMemoryHyperfabricBoundary
canonicalDepthWheelMemoryHyperfabricBoundary =
  depthWheelMemoryHyperfabricBoundary
    true true true false refl true false refl false refl false refl
