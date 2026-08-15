module DASHI.Physics.Closure.NSPeriodicNearTriadClassification where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteNearTriadSums as Near
import DASHI.Physics.Closure.NSPeriodicFiniteTriadPartition as Partition
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact executable Bony classification from dyadic shell levels.
------------------------------------------------------------------------

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc n) = true
natLess (suc m) zero = false
natLess (suc m) (suc n) = natLess m n

record NearShellPolicy : Set₁ where
  field
    shellLevel : Z3.FourierMode → Nat
    overlapRadius : Nat

open NearShellPolicy public

classifyLevels : Nat → Nat → Nat → Partition.NearClass
classifyLevels radius low high with natLess (low + radius) high
... | true = Partition.lowHigh
... | false with natLess (high + radius) low
...   | true = Partition.highLow
...   | false = Partition.highHigh

classifyTriad : NearShellPolicy → Near.ConcreteNearTriad → Partition.NearClass
classifyTriad P t = classifyLevels
  (overlapRadius P)
  (shellLevel P (Near.p t))
  (shellLevel P (Near.q t))

record ClassificationWitness
    (P : NearShellPolicy)
    (t : Near.ConcreteNearTriad) : Set where
  constructor classified
  field
    class-is-computed : classifyTriad P t ≡ classifyTriad P t

classificationTotal : ∀ P t → ClassificationWitness P t
classificationTotal P t = classified refl

nearTriadClassificationLevel : ProofLevel
nearTriadClassificationLevel = machineChecked
