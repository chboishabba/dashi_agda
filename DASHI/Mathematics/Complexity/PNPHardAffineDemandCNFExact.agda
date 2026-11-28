module DASHI.Mathematics.Complexity.PNPHardAffineDemandCNFExact where

-- The original hard constraints and aggregate share one native gate program.
-- Consume the original optimized CNF and finite canonical extension owners.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Vec.Base using (Vec)
open import Data.List.Base using (List)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import DASHI.Mathematics.Complexity.PNPHardAffineGateExact as H
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T
import DASHI.Mathematics.Complexity.PNPAggregateThresholdArithmeticExact as A
import DASHI.Mathematics.Complexity.PNPAggregateGateCountExact as G
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as B
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact as O
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact as Opt
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as F

module Demand {n : Nat} (h : H.Flat n) (fs : List (H.Flat n)) (rs : T.Rows n) (k : Nat) where
  circuit = H.compileDemand h fs rs (G.clamp rs k)
  g = C.gateCount circuit

  Bits : Set
  Bits = CNF.Bits (n + g)

  formula = Opt.optCircuitCNF circuit

  accepted : ∀ x → C.evaluateCircuit circuit x ≡ true →
    (H.hardValue h fs x ≡ true) × (A.potential rs x ≤ k)
  accepted x yes =
    O.cnfAndTrueLeft both ,
    G.clampSound rs k x
      (A.leSound _ _ (trans (sym (A.acceptExact rs (G.clamp rs k) x))
        (CNF.andTrueGivesRight _ _ both)))
    where both = trans (sym (H.demandExact h fs rs (G.clamp rs k) x)) yes

  accept : ∀ x → H.hardValue h fs x ≡ true → A.potential rs x ≤ k →
    C.evaluateCircuit circuit x ≡ true
  accept x hd cap =
    trans (H.demandExact h fs rs (G.clamp rs k) x)
      (O.cnfAndBothTrue hd
        (trans (A.acceptExact rs (G.clamp rs k) x)
          (A.leComplete (G.clampComplete rs k x cap))))

  canonical : Vec Bool n → Bits
  canonical = F.canonicalOriginalProgramBits (C.program circuit)

  decode : (bits : Bits) → CNF.evaluateCNF formula bits ≡ true →
    (H.hardValue h fs (F.inputVectorFromGlobal bits) ≡ true) ×
    (A.potential rs (F.inputVectorFromGlobal bits) ≤ k)
  decode bits yes = accepted (F.inputVectorFromGlobal bits)
    (F.originalPlacedCNFImpliesAcceptedInput circuit bits
      (trans (sym (Opt.optCircuitEqualsOriginal circuit bits)) yes))

  encode : ∀ x → H.hardValue h fs x ≡ true → A.potential rs x ≤ k →
    CNF.evaluateCNF formula (canonical x) ≡ true
  encode x hd cap = trans (Opt.optCircuitEqualsOriginal circuit (canonical x))
    (F.canonicalGlobalPlacedCNFCompleteness circuit x (accept x hd cap))

  originalRoundTrip : ∀ x → F.inputVectorFromGlobal (canonical x) ≡ x
  originalRoundTrip = F.canonicalOriginalProgramInputRoundTrip (C.program circuit)

  uniqueExtension : ∀ (l r : Bits) →
    CNF.evaluateCNF formula l ≡ true → CNF.evaluateCNF formula r ≡ true →
    F.inputVectorFromGlobal l ≡ F.inputVectorFromGlobal r → l ≡ r
  uniqueExtension l r ly ry same =
    F.originalPlacedCNFModelsUniqueForInputs circuit l r
      (trans (sym (Opt.optCircuitEqualsOriginal circuit l)) ly)
      (trans (sym (Opt.optCircuitEqualsOriginal circuit r)) ry) same
