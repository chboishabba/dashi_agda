module DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact where

------------------------------------------------------------------------
-- E20 final finite target-object refinement:
-- Construct a REAL Cut.WeightedCutGraph n (positive W), not a target
-- marker, and prove exact existential yes-iff with the original signed
-- list PARTITION for EVERY n and each source.
--
-- A positive ZERO-sum source maps to the fixed two-vertex/unit-edge
-- positive-threshold graph. Other source instances use the new unique
-- upper-triangular Fin-indexed complete graph with 4*c_i*c_j weights.
--
-- Still not a certified Word-level polynomial many-one map: source/
-- target codecs and actual machine clock must be supplied independently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Base using (z≤n)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Data.Integer.Base as Int
import Data.Integer.Properties as IntP
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact as Indexed

fixedUnitGraph : Cut.WeightedCutGraph 2
fixedUnitGraph = Cut.graph
  (Cut.edge Fin.zero (Fin.suc Fin.zero) (λ ()) (+ 1) ∷ [])
  (+ 1)
  (Int.+≤+ z≤n , (λ ()))

fixedUnitLabels : Vec.Vec Bool 2
fixedUnitLabels = true Vec.∷ false Vec.∷ Vec.[]

fixedUnitGraphAccepts :
  Cut.WeightedMaxCutYES fixedUnitGraph
fixedUnitGraphAccepts =
  fixedUnitLabels ,
  IntP.≤ᵇ⇒≤ tt

sourceIndexedWeightedGraph :
  (parts : List ℤ) →
  Threshold.NonZero (Source.sourceTotal parts) →
  Cut.WeightedCutGraph (length parts)
sourceIndexedWeightedGraph parts nonzero =
  Cut.graph
    (Gen.completeScaledPairEdges (Indexed.vectorOfList parts))
    (Source.sourceTotal parts * Source.sourceTotal parts)
    (Threshold.nonzeroTotalSquareIsPositiveThreshold
      (Source.sourceTotal parts) nonzero)

choiceFromLabels :
  (parts : List ℤ) →
  Vec.Vec Bool (length parts) →
  Source.Selection parts
choiceFromLabels [] Vec.[] = tt
choiceFromLabels (x ∷ xs) (bit Vec.∷ bits) =
  bit , choiceFromLabels xs bits

choiceLabelsRoundTrip :
  (parts : List ℤ) (bits : Vec.Vec Bool (length parts)) →
  Indexed.labelsOfSelection
    parts (choiceFromLabels parts bits) ≡ bits
choiceLabelsRoundTrip [] Vec.[] = refl
choiceLabelsRoundTrip (x ∷ xs) (bit Vec.∷ bits) =
  cong (λ remainder → bit Vec.∷ remainder)
    (choiceLabelsRoundTrip xs bits)

sourceIndexedGraphAcceptsIff :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  PR.Iff
    (Indexed.IndexedScaledCutYES parts)
    (Cut.WeightedMaxCutYES (sourceIndexedWeightedGraph parts nonzero))
sourceIndexedGraphAcceptsIff parts nonzero =
  PR.iff
    (λ { (choice , accepted) →
      Indexed.labelsOfSelection parts choice , accepted })
    (λ { (bits , accepted) →
      choiceFromLabels parts bits ,
      subst
        (λ labels →
          Int._≤_ (Source.sourceTotal parts * Source.sourceTotal parts)
          (Cut.edgeListCutValue
            (Gen.completeScaledPairEdges (Indexed.vectorOfList parts))
            labels))
        (sym (choiceLabelsRoundTrip parts bits))
        accepted })

-- Full existential target dispatch; no hidden existential witness
-- influences the mapped finite graph or the zero-sum guard.
ActualPositiveTargetAccepts :
  Source.PositiveCutTarget → Set
ActualPositiveTargetAccepts Source.unitEdgeYesPositive =
  Cut.WeightedMaxCutYES fixedUnitGraph
ActualPositiveTargetAccepts
  (Source.scaledCompletePositive parts nonzero) =
  Cut.WeightedMaxCutYES (sourceIndexedWeightedGraph parts nonzero)

sourcePartitionActualPositiveGraphIff :
  (parts : List ℤ) →
  PR.Iff
    (Source.PartitionYES parts)
    (ActualPositiveTargetAccepts
      (Source.totalPartitionToPositiveCut parts))
sourcePartitionActualPositiveGraphIff parts
  with Int._≟_ (Source.sourceTotal parts) (+ 0)
... | yes eq =
  PR.iff
    (λ _ → fixedUnitGraphAccepts)
    (λ _ → Source.zeroTotalPartitionYES parts eq)
... | no nonzero =
  PR.iffTransitive
    (Indexed.karpPartitionActualIndexedGraphYESIff parts)
    (sourceIndexedGraphAcceptsIff parts nonzero)
