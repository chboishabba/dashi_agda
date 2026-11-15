module DASHI.Mathematics.Complexity.Karp21MichaelLevinObserverCutQuotientBoundaryExact where

------------------------------------------------------------------------
-- MICHAEL LEVIN / OBSERVER-RELATIVE POLYCOMPUTATION:
-- an exact finite non-recoverability boundary for Karp C2 quotient.
--
-- The actual signed Karp cut objective is invariant under global bit
-- complement. Yet the first vertex's label is NOT invariant. Hence
-- quotienting by signed cut score preserves *that* decision observable
-- but loses the literal policy/bit-label observation.
--
-- This uses the already source-written real signed graph and its real
-- first two-bit cut certificate, not a status-flag record.
--
-- Biology source owners (read-only):
--  ObserverRelativePolycomputation, SubstrateConstrainedComputation,
--  CompetentGoalExecution, ProblemSpaceAgency.
-- Neither the biological physical substrate nor consciousness can be
-- inferred from the two-valued Karp certificate.
--
-- Original Karp 1972; original Michael Levin research attribution
-- stays separate from this DASHI finite witness and the C2 symmetry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Biology.Levin.ObserverRelativePolycomputation as LevinObserver
import DASHI.Biology.Levin.SubstrateConstrainedComputation as LevinSubstrate
import DASHI.Biology.Levin.ProblemSpaceAgency as LevinSpace
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Karp

originalWitness : Vec.Vec Bool 2
originalWitness = Karp.fixedUnitLabels

differentPolicyWitness : Vec.Vec Bool 2
differentPolicyWitness = Lap.flipLabels originalWitness

originalVsFlippedCutScoreExactlyEqual :
  Cut.cutValue Karp.fixedUnitGraph differentPolicyWitness
    ≡ Cut.cutValue Karp.fixedUnitGraph originalWitness
originalVsFlippedCutScoreExactlyEqual =
  Lap.signedMaxCutGlobalFlipInvariant
    (Cut.edges Karp.fixedUnitGraph) originalWitness

-- This actual observation is not the cut objective. It is the first
-- vertex's raw state coordinate, and is destroyed by C2 quotient.
rawFirstVertexObservation :
  Vec.Vec Bool 2 → Bool
rawFirstVertexObservation labels =
  Vec.lookup labels Fin.zero

flippedWitnessChangesRawObservation :
  rawFirstVertexObservation originalWitness
    ≡ rawFirstVertexObservation differentPolicyWitness →
  ⊥
flippedWitnessChangesRawObservation ()

sameDecisionObservableDoesNotRecoverLiteralPolicy :
  (Cut.cutValue Karp.fixedUnitGraph differentPolicyWitness
     ≡ Cut.cutValue Karp.fixedUnitGraph originalWitness)
  ×
  (rawFirstVertexObservation originalWitness
    ≡ rawFirstVertexObservation differentPolicyWitness → ⊥)
sameDecisionObservableDoesNotRecoverLiteralPolicy =
  originalVsFlippedCutScoreExactlyEqual ,
  flippedWitnessChangesRawObservation
