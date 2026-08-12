module DASHI.Cognition.PNF.DepthWheelMemoryHyperfabricRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as WheelMemory
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.PNFIRLearningRegression as Existing
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

alignedRoot : WheelMemory.WheelMemoryFibre
alignedRoot = WheelMemory.alignMemoryAtDepth Existing.memory 0

rootPhaseIsZero :
  WheelMemory.wheelPhase alignedRoot ≡ Wheel.phase-0
rootPhaseIsZero = refl

reinforcedStep : WheelMemory.WheelLearningTransition
reinforcedStep = WheelMemory.reinforcementWheelTransition alignedRoot

reinforcedStepPhaseIsOne :
  WheelMemory.wheelPhase (WheelMemory.target reinforcedStep) ≡ Wheel.phase-1
reinforcedStepPhaseIsOne = refl

reinforcedStepPreservesEvent :
  WheelMemory.publicMemoryProjection (WheelMemory.target reinforcedStep)
  ≡ Existing.event
reinforcedStepPreservesEvent = refl

reinforcedStepChangesFullMemory :
  WheelMemory.memory (WheelMemory.target reinforcedStep)
  ≡ WheelMemory.memory alignedRoot →
  Data.Empty.⊥
reinforcedStepChangesFullMemory =
  WheelMemory.depthZeroAdvanceChangesFullMemory
    WheelMemory.reinforcementUpdate
    Existing.memory

extinctionStep : WheelMemory.WheelLearningTransition
extinctionStep = WheelMemory.extinctionWheelTransition alignedRoot

extinctionActionProjectionIsZero :
  Memory.actionWeight (WheelMemory.memory (WheelMemory.target extinctionStep)) ≡ 0
extinctionActionProjectionIsZero = refl

extinctionStillRemembersEvent :
  WheelMemory.publicMemoryProjection (WheelMemory.target extinctionStep)
  ≡ Existing.event
extinctionStillRemembersEvent = refl

canonicalProgram : WheelMemory.ThreePhaseLearningProgram
canonicalProgram = WheelMemory.canonicalRevalueHabituateReinforceWheel 7

afterOneWheel : WheelMemory.WheelMemoryFibre
afterOneWheel = WheelMemory.runOneLearningWheel canonicalProgram alignedRoot

afterOneWheelDepthIsThree :
  WheelMemory.refinementDepth afterOneWheel ≡ 3
afterOneWheelDepthIsThree = refl

afterOneWheelPhaseReturnsToZero :
  WheelMemory.wheelPhase afterOneWheel ≡ Wheel.phase-0
afterOneWheelPhaseReturnsToZero = refl

afterOneWheelCountIsOne :
  WheelMemory.completedLearningWheels afterOneWheel ≡ 1
afterOneWheelCountIsOne = refl

afterOneWheelStillRemembersEvent :
  WheelMemory.publicMemoryProjection afterOneWheel ≡ Existing.event
afterOneWheelStillRemembersEvent = refl

semanticChannelAtRoot : WheelMemory.ChannelWheelState
semanticChannelAtRoot =
  WheelMemory.channelWheelState Trauma.memoryChannel alignedRoot

arousalChannelAfterOneStep : WheelMemory.ChannelWheelState
arousalChannelAfterOneStep =
  WheelMemory.channelWheelState
    Trauma.arousalChannel
    (WheelMemory.target reinforcedStep)

canonicalPhaseMismatch : WheelMemory.ChannelPhaseCoupling
canonicalPhaseMismatch =
  WheelMemory.channelPhaseCoupling
    semanticChannelAtRoot
    arousalChannelAfterOneStep
    5

canonicalPhaseMismatchCostIsFive :
  WheelMemory.couplingFrustration canonicalPhaseMismatch ≡ 5
canonicalPhaseMismatchCostIsFive = refl
