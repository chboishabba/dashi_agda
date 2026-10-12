module DASHI.Reasoning.E6MinusculeFirstTitsTitsExtensionExact where

------------------------------------------------------------------------
-- E6 MINUSCULE / FIRST-TITS MONOMIAL LIFT: TITS-EXTENSION MAX-CUT
--
-- The previous owner paid the 27-point weight/basis-label bridge and the full
-- 51,840-element permutation image, while leaving the one-dimensional
-- weight-space scalar lift open.
--
-- `scripts/check_e6_first_tits_tits_extension.py` advances that seam using the
-- ACTUAL first-Tits cubic
--
--   N(X,Y,Z) = det X + det Y + det Z - tr(XYZ).
--
-- For each of six genuine E6 simple reflections, the transported 27-point
-- permutation preserves the support of all 45 cubic monomials.  A finite F2
-- solve then supplies signs epsilon_i in {+1,-1} such that the signed monomial
-- operator
--
--   e_i |-> epsilon_i e_{p(i)}
--
-- preserves the complete cubic coefficient tensor exactly.
--
-- Crucial non-collapse:
-- selected cubic-preserving lifts do not necessarily form a strict section of
-- W(E6).  Squares / Coxeter words can close by diagonal cubic-preserving
-- 2-torsion.  That is the expected Weyl-normalizer / Tits-extension surface,
-- and is strictly stronger and more accurate than pretending the permutation
-- action itself already supplies canonical linear Weyl representatives.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.E6MinusculeFirstTitsWeightBasisBridgeExact as WeightBridge

record E6FirstTitsTitsExtensionExecutionReceipt : Set where
  constructor e6-first-tits-tits-extension-execution-receipt
  field
    firstTitsCubicMonomialCount : Nat
    simpleReflectionCount : Nat
    allSimplePermutationsPreserveCubicSupport : Bool
    everySimpleReflectionHasSignedCubicPreservingLift : Bool
    signedLiftsPreserveFullCubicCoefficientTensor : Bool
    selectedLiftsFormStrictWeylSection : Bool
    diagonalCubicPreservingTwoTorsionResidualsObserved : Bool
    pythonExecutionCountsAsAgdaKernelProof : Bool
open E6FirstTitsTitsExtensionExecutionReceipt public

canonicalE6FirstTitsTitsExtensionExecutionReceipt :
  E6FirstTitsTitsExtensionExecutionReceipt
canonicalE6FirstTitsTitsExtensionExecutionReceipt =
  e6-first-tits-tits-extension-execution-receipt
    45 6 true true true false true false

record E6FirstTitsTitsExtensionBoundary : Set where
  constructor e6-first-tits-tits-extension-boundary
  field
    finiteWeightBasisBridgeAlreadyPaid : Bool
    simpleReflectionSignedMonomialLiftsPaidAtExecutionGrade : Bool
    actualFirstTitsCubicPreservationPaidAtExecutionGrade : Bool
    scalarLiftReducedFromArbitraryNonzeroScalarsToSignedMonomialTitsExtension : Bool
    strictLinearWeylSectionPaid : Bool
    coherentTitsExtensionPresentationKernelPaid : Bool
    fullE6AlgebraicGroupRepresentationPaid : Bool
    note : String
open E6FirstTitsTitsExtensionBoundary public

canonicalE6FirstTitsTitsExtensionBoundary : E6FirstTitsTitsExtensionBoundary
canonicalE6FirstTitsTitsExtensionBoundary =
  e6-first-tits-tits-extension-boundary
    WeightBridge.canonicalE6FirstTitsWeightBasisBoundary.finiteWeightBasisLabelBridgePaid
    true true true
    false false false
    "The finite E6/first-Tits bridge now reaches explicit signed monomial operators preserving the actual 45-term first-Tits cubic for all six simple reflections. The residual is not another 27-point recognition: it is the coherent Weyl-normalizer/Tits-extension presentation, whose squares and Coxeter words may carry diagonal cubic-preserving 2-torsion, followed by algebraic-group/kernel certification."
