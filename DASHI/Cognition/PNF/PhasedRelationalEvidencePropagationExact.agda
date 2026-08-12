module DASHI.Cognition.PNF.PhasedRelationalEvidencePropagationExact where

------------------------------------------------------------------------
-- PHASED RELATIONAL EVIDENCE PROPAGATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (+_)

import DASHI.Cognition.PNF.PhasedRelationalLatticeExact as Lattice
import DASHI.Cognition.PNF.TypePressure as Pressure
import DASHI.Core.RelationalHorizon369 as Horizon
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

data Node : Set where
  eventNode : Node

data CandidateType : Set where
  editionLike : CandidateType

data Evidence : Set where
  secondHopRoleEvidence : Evidence

emptyPressure :
  Pressure.TypePressureEnvelope
    {Subject = Node}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    eventNode editionLike
emptyPressure = Pressure.typePressureEnvelope []

secondHopPositivePressure :
  Pressure.TypePressureContribution
    {Subject = Node}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    eventNode editionLike
secondHopPositivePressure =
  Pressure.typePressureContribution
    secondHopRoleEvidence
    (+ (suc zero))
    "second-hop predicate-role support"
    "finite phased-lattice regression"

expandedPressure :
  Pressure.TypePressureEnvelope
    {Subject = Node}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    eventNode editionLike
expandedPressure =
  Lattice.prependEvidence secondHopPositivePressure emptyPressure

localCell :
  Lattice.PhasedLatticeCell
    {Subject = Node}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    eventNode editionLike
localCell =
  Lattice.phasedLatticeCell
    0
    Horizon.H3
    Wheel.phase-0
    emptyPressure
    Selection.independent
    refl

expandedCell :
  Lattice.PhasedLatticeCell
    {Subject = Node}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    eventNode editionLike
expandedCell =
  Lattice.phasedLatticeCell
    0
    Horizon.H6
    Wheel.phase-0
    expandedPressure
    Selection.reinforcing
    refl

localSemanticPhaseIsNeutral :
  Lattice.semanticPhase localCell ≡ Selection.independent
localSemanticPhaseIsNeutral = refl

expandedSemanticPhaseIsPositive :
  Lattice.semanticPhase expandedCell ≡ Selection.reinforcing
expandedSemanticPhaseIsPositive = refl

processPhaseUnchangedAcrossEvidenceExpansion :
  Lattice.processPhase localCell ≡ Lattice.processPhase expandedCell
processPhaseUnchangedAcrossEvidenceExpansion = refl

resolutionUnchangedAcrossEvidenceExpansion :
  Lattice.resolutionDepth localCell ≡ Lattice.resolutionDepth expandedCell
resolutionUnchangedAcrossEvidenceExpansion = refl

data SemanticPhaseEquality : Set where

semanticPhaseActuallyChanges :
  Lattice.semanticPhase localCell ≡ Lattice.semanticPhase expandedCell →
  SemanticPhaseEquality
semanticPhaseActuallyChanges ()
