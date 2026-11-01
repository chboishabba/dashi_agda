module DASHI.Physics.Closure.NSPeriodicConcreteNearTriadSums where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicFiniteTriadPartition as Partition
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal resonant triads and the three exact near folds.
------------------------------------------------------------------------

record ConcreteNearTriad : Set where
  constructor triad
  field
    p q k : Z3.FourierMode
    resonance : Z3.addMode p q ≡ k

open ConcreteNearTriad public

record ConcreteNearTriadFamily
    {i : Level}
    (A : AbsorptionArithmetic)
    (Tag : Set i) : Set (lsuc i) where
  field
    triads : List Tag
    classify : Tag → Partition.NearClass
    contribution : Tag → Scalar A

open ConcreteNearTriadFamily public

classifiedFamily :
  ∀ {i} {A : AbsorptionArithmetic} {Tag : Set i} →
  ConcreteNearTriadFamily A Tag → Partition.ClassifiedNearFamily A Tag
classifiedFamily F = record
  { classify = classify F
  ; contribution = contribution F
  }

nearTotal nearLowHigh nearHighLow nearHighHigh :
  ∀ {i} {A : AbsorptionArithmetic} {Tag : Set i} →
  ConcreteNearTriadFamily A Tag → Scalar A
nearTotal F = Partition.nearTotal (classifiedFamily F) (triads F)
nearLowHigh F = Partition.nearLowHigh (classifiedFamily F) (triads F)
nearHighLow F = Partition.nearHighLow (classifiedFamily F) (triads F)
nearHighHigh F = Partition.nearHighHigh (classifiedFamily F) (triads F)

concreteNearTriadDecomposition :
  ∀ {i} {A : AbsorptionArithmetic} {Tag : Set i} →
  (F : ConcreteNearTriadFamily A Tag) →
  nearTotal F ≡
  _+_ A (_+_ A (nearLowHigh F) (nearHighLow F)) (nearHighHigh F)
concreteNearTriadDecomposition F =
  Partition.finiteNearTriadDecomposition (classifiedFamily F) (triads F)

concreteNearTriadSumsLevel : ProofLevel
concreteNearTriadSumsLevel = machineChecked
