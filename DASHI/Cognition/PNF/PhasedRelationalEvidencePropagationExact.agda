module DASHI.Cognition.PNF.PhasedRelationalEvidencePropagationExact where

------------------------------------------------------------------------
-- PHASED RELATIONAL EVIDENCE PROPAGATION
--
-- Concrete finite witness for the Wikidata/phased-lattice claim: a node can
-- retain the same identity and process phase while its semantic/evidence phase
-- changes solely because a wider relational horizon contributes new typed
-- evidence.  The fine signed pressure remains the retained carrier; the
-- semantic phase is its coarse observation.
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

------------------------------------------------------------------------
-- Small typed carrier.
------------------------------------------------------------------------

data Node : Set where
  eventNode : Node

data CandidateType : Set where
  editionLike : CandidateType

data Evidence : Set where
  secondHopRoleEvidence : Evidence

emptyPressure : Pressure.TypePressureEnvelope eventNode editionLike
emptyPressure = Pressure.typePressureEnvelope []

secondHopPositivePressure :
  Pressure.TypePressureContribution eventNode editionLike
secondHopPositivePressure =
  Pressure.typePressureContribution
    secondHopRoleEvidence
    (+ (suc zero))
    "second-hop predicate-role support"
    "finite phased-lattice regression"

expandedPressure : Pressure.TypePressureEnvelope eventNode editionLike
expandedPressure =
  Lattice.prependEvidence secondHopPositivePressure emptyPressure

localCell : Lattice.PhasedLatticeCell eventNode editionLike
localCell =
  Lattice.phasedLatticeCell
    0
    Horizon.H3
    Wheel.phase-0
    emptyPressure
    Selection.independent
    refl

expandedCell : Lattice.PhasedLatticeCell eventNode editionLike
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

------------------------------------------------------------------------
-- The evidence phase changes because the retained pressure envelope changed,
-- not because process phase or node identity changed.
------------------------------------------------------------------------

data SemanticPhaseEquality : Set where

semanticPhaseActuallyChanges :
  Lattice.semanticPhase localCell ≡ Lattice.semanticPhase expandedCell →
  SemanticPhaseEquality
semanticPhaseActuallyChanges ()
