module DASHI.Mathematics.Complexity.PNPAggregateHardCNFWeldExact where

-- Keep the original hard CNF on the original input coordinates. Only the
-- aggregate DAG gates receive fresh indices. Reuse all source CNF semantics.
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
open import Data.Vec.Base using (Vec)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T
import DASHI.Mathematics.Complexity.PNPAggregateThresholdArithmeticExact as A
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Place
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as VecOwner
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact as Original
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact as Opt
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as F

pullbackOriginal : ∀ {n g} (bits : CNF.Bits (n + g)) →
  Rename.pullbackBits Place.finLeft bits ≡ F.finiteVecToBits (F.inputVectorFromGlobal bits)
pullbackOriginal {n} {g} bits =
  trans (sym (F.bitsVecRoundTrip prefix))
    (cong F.finiteVecToBits
      (VecOwner.vecExtensionality
        (F.bitsToFiniteVec prefix) (F.inputVectorFromGlobal {n} {g} bits)
        (λ i → trans (sym (F.lookupCNFToVec prefix i))
          (trans (Rename.pullbackLookup Place.finLeft bits i)
            (sym (F.inputVectorLookupExact bits i))))))
  where
    prefix : CNF.Bits n
    prefix = Rename.pullbackBits Place.finLeft bits

hardValue : ∀ {n} → CNF.CNF n → Vec Bool n → Bool
hardValue hard x = CNF.evaluateCNF hard (F.finiteVecToBits x)

hardPlacedExact : ∀ {n g} (hard : CNF.CNF n) (bits : CNF.Bits (n + g)) →
  CNF.evaluateCNF (Rename.renameCNF Place.finLeft hard) bits ≡
  hardValue hard (F.inputVectorFromGlobal bits)
hardPlacedExact hard bits =
  trans (Rename.renamedCNFEvaluation Place.finLeft hard bits)
    (cong (CNF.evaluateCNF hard) (pullbackOriginal bits))

aggregateGateExact : ∀ {n} (rs : T.Rows n) k (x : Vec Bool n) →
  C.evaluateCircuit (T.aggregateCircuit rs k) x ≡ A.leB (A.potential rs x) k
aggregateGateExact rs k x = trans (T.aggregateCircuitExact rs k x) (A.acceptExact rs k x)

DemandCNF : ∀ {n} (rs : T.Rows n) (k : Nat) → CNF.CNF n →
  CNF.CNF (n + C.gateCount (T.aggregateCircuit rs k))
DemandCNF rs k hard = Placed.append
  (Rename.renameCNF Place.finLeft hard)
  (Opt.optCircuitCNF (T.aggregateCircuit rs k))

aggregatePart : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (bits : CNF.Bits (n + C.gateCount (T.aggregateCircuit rs k))) →
  CNF.evaluateCNF (DemandCNF rs k hard) bits ≡ true →
  CNF.evaluateCNF (Original.circuitPlacedCNF (T.aggregateCircuit rs k)) bits ≡ true
aggregatePart rs k hard bits yes =
  trans (sym (Opt.optCircuitEqualsOriginal (T.aggregateCircuit rs k) bits))
    (CNF.andTrueGivesRight _ _
      (trans (Placed.evaluateCNFAppend
        (Rename.renameCNF Place.finLeft hard)
        (Opt.optCircuitCNF (T.aggregateCircuit rs k)) bits) yes))

decodeDemand : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (bits : CNF.Bits (n + C.gateCount (T.aggregateCircuit rs k))) →
  CNF.evaluateCNF (DemandCNF rs k hard) bits ≡ true →
  (hardValue hard (F.inputVectorFromGlobal bits) ≡ true) ×
  (A.potential rs (F.inputVectorFromGlobal bits) ≤ k)
decodeDemand rs k hard bits yes =
  trans (sym (hardPlacedExact hard bits))
    (Original.cnfAndTrueLeft
      (trans (Placed.evaluateCNFAppend
        (Rename.renameCNF Place.finLeft hard)
        (Opt.optCircuitCNF (T.aggregateCircuit rs k)) bits) yes)) ,
  A.leSound _ k
    (trans (sym (aggregateGateExact rs k (F.inputVectorFromGlobal bits)))
      (F.originalPlacedCNFImpliesAcceptedInput (T.aggregateCircuit rs k) bits
        (aggregatePart rs k hard bits yes)))

canonicalBits : ∀ {n} (rs : T.Rows n) k → Vec Bool n →
  CNF.Bits (n + C.gateCount (T.aggregateCircuit rs k))
canonicalBits rs k x = F.canonicalOriginalProgramBits
  (C.program (T.aggregateCircuit rs k)) x

encodeDemand : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (x : Vec Bool n) → hardValue hard x ≡ true → A.potential rs x ≤ k →
  CNF.evaluateCNF (DemandCNF rs k hard) (canonicalBits rs k x) ≡ true
encodeDemand rs k hard x yes bound =
  trans (Placed.evaluateCNFAppend
    (Rename.renameCNF Place.finLeft hard)
    (Opt.optCircuitCNF (T.aggregateCircuit rs k)) bits)
    (Original.cnfAndBothTrue hardYes gateYes)
  where
    bits = canonicalBits rs k x
    hardYes = trans (hardPlacedExact hard bits)
      (trans (cong (hardValue hard)
        (F.canonicalOriginalProgramInputRoundTrip (C.program (T.aggregateCircuit rs k)) x)) yes)
    gateYes = trans (Opt.optCircuitEqualsOriginal (T.aggregateCircuit rs k) bits)
      (F.canonicalGlobalPlacedCNFCompleteness (T.aggregateCircuit rs k) x
        (trans (aggregateGateExact rs k x) (A.leComplete bound)))

originalRoundTrip : ∀ {n} (rs : T.Rows n) k (x : Vec Bool n) →
  F.inputVectorFromGlobal (canonicalBits rs k x) ≡ x
originalRoundTrip rs k x = F.canonicalOriginalProgramInputRoundTrip
  (C.program (T.aggregateCircuit rs k)) x

uniqueExtension : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (left right : CNF.Bits (n + C.gateCount (T.aggregateCircuit rs k))) →
  CNF.evaluateCNF (DemandCNF rs k hard) left ≡ true →
  CNF.evaluateCNF (DemandCNF rs k hard) right ≡ true →
  F.inputVectorFromGlobal left ≡ F.inputVectorFromGlobal right →
  left ≡ right
uniqueExtension rs k hard left right l r same =
  F.originalPlacedCNFModelsUniqueForInputs (T.aggregateCircuit rs k) left right
    (aggregatePart rs k hard left l) (aggregatePart rs k hard right r) same

-- This closes the finite hard-CNF/aggregate-demand semantic attachment.
-- Translation of arbitrary affine forbidden-flat inputs to the native
-- hard CNF, bounded gate construction cost, and kernel acceptance are
-- still separate. No global SAT producer is asserted.
