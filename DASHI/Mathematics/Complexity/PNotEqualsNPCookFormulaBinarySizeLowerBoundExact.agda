module DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinarySizeLowerBoundExact where

------------------------------------------------------------------------
-- BINARY QUOTATION COST DOMINATES COOK SYNTAX SIZE
--
-- Prefix token code:
--   every Cook syntax constructor contributes at least one token;
--   variable nodes contribute extra unary index tokens.
--
-- Binary code:
--   every token contributes exactly three bits.
--
-- Therefore:
--
--   3 * nodeCount(phi) <= bitCodeLength(phi).
--
-- This theorem lets the bounded self-reference programme compare literal
-- quotation cost against the SAME Cook syntax size used elsewhere in #1040.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

three : Nat
three = suc (suc (suc zero))

------------------------------------------------------------------------
-- One prefix token per AST node, plus variable-index overhead.
------------------------------------------------------------------------

nodeCountBelowTokenCount :
  (formula : Cook.BooleanFormula) →
  Size.formulaNodeCount formula
  ≤
  Prefix.cookFormulaTokenCount formula
nodeCountBelowTokenCount
    (Cook.variable index) =
  s≤s z≤n
nodeCountBelowTokenCount
    (Cook.constant value) =
  NatP.≤-refl
nodeCountBelowTokenCount
    (Cook.negate formula) =
  s≤s
    (nodeCountBelowTokenCount formula)
nodeCountBelowTokenCount
    (Cook.conjunction left right) =
  s≤s
    (NatP.+-mono-≤
      (nodeCountBelowTokenCount left)
      (nodeCountBelowTokenCount right))
nodeCountBelowTokenCount
    (Cook.disjunction left right) =
  s≤s
    (NatP.+-mono-≤
      (nodeCountBelowTokenCount left)
      (nodeCountBelowTokenCount right))

------------------------------------------------------------------------
-- Multiply by the exact three-bit token width.
------------------------------------------------------------------------

threeTimesNodeCountBelowThreeTimesTokenCount :
  (formula : Cook.BooleanFormula) →
  three * Size.formulaNodeCount formula
  ≤
  three * Prefix.cookFormulaTokenCount formula
threeTimesNodeCountBelowThreeTimesTokenCount formula =
  NatP.*-monoʳ-≤
    three
    (nodeCountBelowTokenCount formula)

binaryCodeAtLeastThreeBitsPerNode :
  (formula : Cook.BooleanFormula) →
  three * Size.formulaNodeCount formula
  ≤
  Binary.formulaBitCodeLength formula
binaryCodeAtLeastThreeBitsPerNode formula
    rewrite
      Binary.formulaBitCodeLengthExact formula =
  threeTimesNodeCountBelowThreeTimesTokenCount formula

------------------------------------------------------------------------
-- Research consequence.
--
-- Under this concrete quotation, the binary payload already costs at least
-- three bits per Cook AST node.  Combined with
-- PNotEqualsNPLiteralSelfCodeGrowthNoGoExact, any concrete constructor whose
-- quoted output is proved longer than its proposed input cannot have a raw
-- source-string fixed point.  The surviving route is behavioural/semantic
-- self-reference plus resource closure.
------------------------------------------------------------------------
