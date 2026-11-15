module DASHI.Moonshine.Monster3BAtlasLagrangianFieldSelectionBoundaryExact where

------------------------------------------------------------------------
-- MONSTER 3B NORMALIZER / GF(729) FIELD-SELECTION BOUNDARY
--
-- The ATLAS direct 12-dimensional GF(3) module for 2.Suz:2 is absolutely
-- irreducible.  Consequently the FULL normalizer action cannot simultaneously
-- preserve a nonzero proper six-dimensional submodule identified with the
-- repository translation half X6.
--
-- This corrects an earlier overly broad roadmap phrase suggesting that the
-- whole source action might descend to one global `X6 -> X6` operator.
--
-- The admissible field-selection experiment is narrower and stronger:
--
--   imported symplectic 12-action
--       -> basis weld to X6 + X6*
--       -> selected element / subgroup stabilising the chosen X6 Lagrangian
--       -> induced 6x6 GF(3) operator
--       -> characteristic/minimal polynomial
--       -> irreducible degree-6 receipt, if one exists
--       -> F3[T] ~= GF(729) candidate.
--
-- `scripts/analyze_monster3b_symplectic_field_candidates.py` implements this
-- exact finite search after the certified ATLAS matrices are acquired.  It also
-- derives the central Heisenberg correction from the symmetric difference of
-- the old and transported cocycles using 1/2 = 2 in F3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source

record LagrangianFieldCandidateReceipt : Set where
  constructor lagrangian-field-candidate-receipt
  field
    sourceWordLabel : String
    sourceWordLength : Nat
    preservesChosenTranslationLagrangian : Bool
    inducedSixBySixOperatorComputed : Bool
    characteristicPolynomialComputed : Bool
    minimalPolynomialComputed : Bool
    degreeSixIrreducible : Bool
    fieldGeneratorRecognitionPaid : Bool
open LagrangianFieldCandidateReceipt public

record Monster3BFieldSelectionBoundary : Set where
  constructor monster-3b-field-selection-boundary
  field
    directTwelveModuleAbsolutelyIrreducible : Bool
    fullNormalizerPreservesChosenX6SubmodulePaid : Bool
    globalNormalizerX6FieldActionTargetRejected : Bool
    elementOrSubgroupLagrangianStabilizerSearchRequired : Bool
    symplecticBasisWeldRequired : Bool
    sixBySixPolynomialTestRequired : Bool
    matrixConsumerInstalled : Bool
    centralCorrectionPolarizationImplemented : Bool
    actualAtlasMatricesImported : Bool
    actualDegreeSixIrreducibleCandidateFound : Bool
    actualGF729RecognitionPaid : Bool
    note : String
open Monster3BFieldSelectionBoundary public

canonicalMonster3BFieldSelectionBoundary : Monster3BFieldSelectionBoundary
canonicalMonster3BFieldSelectionBoundary =
  monster-3b-field-selection-boundary
    Source.canonicalDirectTwelveModuleReceipt.absolutelyIrreducible
    false
    true
    true
    true
    true
    true
    true
    false
    false
    false
    "Because the certified source module is absolutely irreducible in dimension 12, the full 2.Suz:2 normalizer is not promoted to a global X6 action. Field selection now searches only source elements/subgroups that stabilize the chosen repository Lagrangian after the exact symplectic basis weld, then tests their induced 6x6 operators for an irreducible degree-six polynomial."
