module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression

-- Use the existing source-to-proof governance theorem.
-- The TOE import graph does not turn a finite proof into source meaning.
-- This imports the original theorem owner. It does not copy the proof.
import DASHI.Governance.FormalisationGovernanceCapstoneExact as Governance

-- The existing theorem closes the exact semantic-promotion guard.
toeKernelProofDoesNotEstablishSourceSemantics :
  Governance.Closure.semanticallyExhaustive
    Governance.Closure.criticalCapstoneStatus ≡ false
toeKernelProofDoesNotEstablishSourceSemantics =
  Governance.kernelClosureIsNotSemanticExhaustiveness
