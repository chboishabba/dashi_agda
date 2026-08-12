module DASHI.Cognition.PNF.PhasedRelationalLatticeExact where

------------------------------------------------------------------------
-- PHASED RELATIONAL LATTICE
--
-- A lattice cell is a constrained interpretation, not an independently
-- mutable truth trit.  Its semantic phase is derived from the exact signed
-- type-pressure envelope; its process phase is the independent C3 depth-wheel
-- grade; and relational horizon is a third coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (_∷_)

import DASHI.Cognition.PNF.EvidenceDepthWheelOrthogonality as Orth
import DASHI.Cognition.PNF.TypePressure as Pressure
import DASHI.Core.RelationalHorizon369 as Horizon
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference

semanticPhaseOf :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  Pressure.TypePressureEnvelope
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType →
  Selection.InteractionDirection
semanticPhaseOf envelope =
  Interference.interactionDirection
    (Pressure.envelopeClassification envelope)

record PhasedLatticeCell
    {Subject CandidateType Evidence : Set}
    (subject : Subject)
    (candidateType : CandidateType) : Set where
  constructor phasedLatticeCell
  field
    resolutionDepth : Nat
    relationalHorizon : Horizon.HorizonLevel
    processPhase : Wheel.DepthWheelPhase
    pressureEnvelope :
      Pressure.TypePressureEnvelope
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType
    semanticPhase : Selection.InteractionDirection
    semanticPhaseDerived :
      semanticPhase ≡ semanticPhaseOf pressureEnvelope

open PhasedLatticeCell public

advanceProcessPhase :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  PhasedLatticeCell
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType →
  PhasedLatticeCell subject candidateType
advanceProcessPhase cell =
  phasedLatticeCell
    (resolutionDepth cell)
    (relationalHorizon cell)
    (Wheel.nextDepthWheelPhase (processPhase cell))
    (pressureEnvelope cell)
    (semanticPhase cell)
    (semanticPhaseDerived cell)

expandRelationalHorizon :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  PhasedLatticeCell
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType →
  PhasedLatticeCell subject candidateType
expandRelationalHorizon cell =
  phasedLatticeCell
    (resolutionDepth cell)
    (Orth.nextRelationalHorizon (relationalHorizon cell))
    (processPhase cell)
    (pressureEnvelope cell)
    (semanticPhase cell)
    (semanticPhaseDerived cell)

horizonExpansionCommutesWithProcessAdvance :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType}
    (cell :
      PhasedLatticeCell
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType) →
  advanceProcessPhase (expandRelationalHorizon cell)
  ≡ expandRelationalHorizon (advanceProcessPhase cell)
horizonExpansionCommutesWithProcessAdvance cell = refl

processAdvancePreservesSemanticPhase :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType}
    (cell :
      PhasedLatticeCell
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType) →
  semanticPhase (advanceProcessPhase cell) ≡ semanticPhase cell
processAdvancePreservesSemanticPhase cell = refl

prependEvidence :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  Pressure.TypePressureContribution
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType →
  Pressure.TypePressureEnvelope subject candidateType →
  Pressure.TypePressureEnvelope subject candidateType
prependEvidence contribution envelope =
  Pressure.typePressureEnvelope
    (contribution ∷ Pressure.contributions envelope)
