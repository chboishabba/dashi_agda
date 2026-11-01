module DASHI.Physics.Closure.NSPeriodicNearTriadPartitionCorrectness where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicConcreteNearTriadSums as Near
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The literal triad fold is exactly the disjoint LH + HL + HH partition.
------------------------------------------------------------------------

nearTriadPartitionCorrect :
  ∀ {i} {A : AbsorptionArithmetic} {Tag : Set i} →
  (F : Near.ConcreteNearTriadFamily A Tag) →
  Near.nearTotal F ≡
  _+_ A
    (_+_ A (Near.nearLowHigh F) (Near.nearHighLow F))
    (Near.nearHighHigh F)
nearTriadPartitionCorrect = Near.concreteNearTriadDecomposition

nearTriadPartitionCorrectnessLevel : ProofLevel
nearTriadPartitionCorrectnessLevel = machineChecked
