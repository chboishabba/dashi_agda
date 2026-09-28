module DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact where

------------------------------------------------------------------------
-- CANONICAL FINITE TRUTH-TABLE REPAIR GENERATOR
--
-- The full residual Boolean function at remaining arity r is stored literally
-- as a Vec Bool (2^r).
--
-- Shannon restriction updates it locally:
--
--   childRepair(a) = the a-prefixed half of parentRepair.
--
-- Thus a perfectly local deterministic repairStep exists. The price is
-- explicit: repair width is exactly 2^r bits.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineConstructionSharingExact as Sharing
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RepairStepFactorizationExact as Factor

------------------------------------------------------------------------
-- Local Vec tabulation/extensionality.
------------------------------------------------------------------------

tabulateVec :
  ∀ {A : Set} {n : Nat} →
  (Fin.Fin n → A) →
  Vec.Vec A n
tabulateVec {n = zero} f =
  Vec.[]
tabulateVec {n = suc n} f =
  f Fin.zero Vec.∷
  tabulateVec (λ i → f (Fin.suc i))

lookupTabulateVec :
  ∀ {A : Set} {n : Nat}
    (f : Fin.Fin n → A)
    (i : Fin.Fin n) →
  Vec.lookup (tabulateVec f) i ≡ f i
lookupTabulateVec {n = suc n} f Fin.zero =
  refl
lookupTabulateVec {n = suc n} f (Fin.suc i) =
  lookupTabulateVec
    (λ j → f (Fin.suc j))
    i

vecExtensionality :
  ∀ {A : Set} {n : Nat}
    (left right : Vec.Vec A n) →
  ((index : Fin.Fin n) →
    Vec.lookup left index
    ≡
    Vec.lookup right index) →
  left ≡ right
vecExtensionality Vec.[] Vec.[] pointwise =
  refl
vecExtensionality
    (left Vec.∷ lefts)
    (right Vec.∷ rights)
    pointwise
    rewrite pointwise Fin.zero
      |
      vecExtensionality
        lefts
        rights
        (λ index →
          pointwise (Fin.suc index)) =
  refl

------------------------------------------------------------------------
-- Canonical finite residual truth table.
------------------------------------------------------------------------

bitsAssignment :
  ∀ {remaining : Nat} →
  Vec.Vec Bool remaining →
  SAT.Assignment remaining
bitsAssignment bits =
  Vec.lookup bits

truthTableRepair :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  Vec.Vec Bool
    (Bits.bitCardinality remaining)
truthTableRepair node =
  tabulateVec
    (λ index →
      Sharing.layerResidualSemantic
        node
        (bitsAssignment
          (Bits.finToBits index)))

------------------------------------------------------------------------
-- Head-bit index embedding.
------------------------------------------------------------------------

prefixedIndex :
  ∀ {remaining : Nat} →
  Bool →
  Fin.Fin (Bits.bitCardinality remaining) →
  Fin.Fin (Bits.bitCardinality (suc remaining))
prefixedIndex action index =
  Bits.bitsToFin
    (action Vec.∷ Bits.finToBits index)

restrictTruthTable :
  ∀ {remaining : Nat} →
  Bool →
  Vec.Vec Bool
    (Bits.bitCardinality (suc remaining)) →
  Vec.Vec Bool
    (Bits.bitCardinality remaining)
restrictTruthTable action parent =
  tabulateVec
    (λ index →
      Vec.lookup parent
        (prefixedIndex action index))

------------------------------------------------------------------------
-- Actual Shannon child truth table is the selected half of the parent table.
------------------------------------------------------------------------

truthTableRepairStepExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (parent :
      Width.LayerNode
        {root = root}
        (suc remaining)) →
  truthTableRepair
      (Shannon.layerChild action parent)
  ≡
  restrictTruthTable
      action
      (truthTableRepair parent)
truthTableRepairStepExact
    {remaining = remaining}
    action
    parent
    with Width.node parent | Width.arityExact parent
... | Family.restriction-node .(suc remaining) current derivation | refl =
  vecExtensionality
    (truthTableRepair
      (Shannon.layerChild action parent))
    (restrictTruthTable
      action
      (truthTableRepair parent))
    pointwise
  where
    tailBits :
      Fin.Fin (Bits.bitCardinality remaining) →
      Vec.Vec Bool remaining
    tailBits index =
      Bits.finToBits index

    prefixedBits :
      Fin.Fin (Bits.bitCardinality remaining) →
      Vec.Vec Bool (suc remaining)
    prefixedBits index =
      action Vec.∷ tailBits index

    extendAgreement :
      (index :
        Fin.Fin (Bits.bitCardinality remaining)) →
      (variable : Fin.Fin (suc remaining)) →
      SAT.extendAssignment
          action
          (bitsAssignment (tailBits index))
          variable
      ≡
      bitsAssignment
          (Bits.finToBits
            (prefixedIndex action index))
          variable
    extendAgreement index variable
        rewrite
          Bits.finToBitsAfterBitsToFin
            (prefixedBits index)
        with variable
    ... | Fin.zero =
      refl
    ... | Fin.suc lower =
      refl

    childToParentEvaluation :
      (index :
        Fin.Fin (Bits.bitCardinality remaining)) →
      Sharing.layerResidualSemantic
          (Shannon.layerChild action parent)
          (bitsAssignment (tailBits index))
      ≡
      Sharing.layerResidualSemantic
          parent
          (bitsAssignment
            (Bits.finToBits
              (prefixedIndex action index)))
    childToParentEvaluation index =
      trans
        (SAT.restrictionEvaluation
          action
          current
          (bitsAssignment (tailBits index)))
        (SAT.evaluateExtensional
          current
          (extendAgreement index))

    pointwise :
      (index :
        Fin.Fin
          (Bits.bitCardinality remaining)) →
      Vec.lookup
        (truthTableRepair
          (Shannon.layerChild action parent))
        index
      ≡
      Vec.lookup
        (restrictTruthTable
          action
          (truthTableRepair parent))
        index
    pointwise index =
      trans
        (lookupTabulateVec _ index)
        (trans
          (childToParentEvaluation index)
          (trans
            (sym
              (lookupTabulateVec
                (λ parentIndex →
                  Sharing.layerResidualSemantic
                    parent
                    (bitsAssignment
                      (Bits.finToBits parentIndex)))
                (prefixedIndex action index)))
            (sym
              (lookupTabulateVec
                (λ childIndex →
                  Vec.lookup
                    (truthTableRepair parent)
                    (prefixedIndex action childIndex))
                index))))

------------------------------------------------------------------------
-- Projection and exact factorization.
------------------------------------------------------------------------

truthTableRepairProjection :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Factor.GradedQ1RepairProjection root
truthTableRepairProjection root =
  record
    { Factor.Coarse =
        λ remaining → ⊤
    ; Factor.Repair =
        λ remaining →
          Vec.Vec Bool
            (Bits.bitCardinality remaining)
    ; Factor.coarse =
        λ remaining node → tt
    ; Factor.repair =
        λ remaining node →
          truthTableRepair node
    }

truthTableRepairFactors :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Factor.RepairStepFactorization
    (truthTableRepairProjection root)
truthTableRepairFactors root =
  record
    { Factor.repairStep =
        λ remaining action coarse parent →
          restrictTruthTable action parent
    ; Factor.repairStepExact =
        λ remaining action parent →
          truthTableRepairStepExact action parent
    }

------------------------------------------------------------------------
-- FRONTIER
--
-- Positive mechanism PAID:
--
--   a deterministic local Shannon repair recurrence exists for the complete
--   residual truth table.
--
-- Explicit price:
--
--   Repair(r) = Vec Bool (2^r).
--
-- Therefore B1 has moved again. The question is not whether local recurrence
-- exists at all; it does. The question is whether there is a smaller repair
-- projection that still factors through the same local Shannon update.
--
-- The repair-step factorization owner now gives the direct test:
-- either construct its repairStep, or exhibit a same-input/different-child
-- collision.
------------------------------------------------------------------------
