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
-- If the generated formula has at least as many AST nodes as the proposed
-- input has bits, literal self-code equality is impossible for nonempty input.
------------------------------------------------------------------------

positiveInputAndFormulaAtLeastInputKillsLiteralFixedPoint :
  (constructor :
    Agda.Builtin.List.List Agda.Builtin.Bool.Bool →
    Cook.BooleanFormula) →
  (input :
    Agda.Builtin.List.List Agda.Builtin.Bool.Bool) →
  suc zero
    ≤ Binary.listLength input →
  Binary.listLength input
    ≤ Size.formulaNodeCount (constructor input) →
  input
    ≡ Binary.encodeFormulaBits (constructor input) →
  Agda.Builtin.Empty.⊥
positiveInputAndFormulaAtLeastInputKillsLiteralFixedPoint
    constructor
    input
    inputPositive
    inputBelowNodes
    fixed =
  NatP.<-irrefl
    inputLength
    (NatP.<-≤-trans
      inputBelowTriple
      codeBelowInput)
  where
    inputLength : Nat
    inputLength =
      Binary.listLength input

    inputBelowDouble :
      inputLength
      <
      inputLength + inputLength
    inputBelowDouble =
      NatP.m<n+m
        inputLength
        inputPositive

    inputBelowTriple :
      inputLength
      <
      three * Size.formulaNodeCount
        (constructor input)
    inputBelowTriple =
      NatP.<-≤-trans
        inputBelowDouble
        tripleNodeLower
      where
        doubleInputBelowDoubleNodes :
          inputLength + inputLength
          ≤
          Size.formulaNodeCount (constructor input)
          + Size.formulaNodeCount (constructor input)
        doubleInputBelowDoubleNodes =
          NatP.+-mono-≤
            inputBelowNodes
            inputBelowNodes

        doubleNodesBelowTripleNodes :
          Size.formulaNodeCount (constructor input)
          + Size.formulaNodeCount (constructor input)
          ≤
          three * Size.formulaNodeCount
            (constructor input)
        doubleNodesBelowTripleNodes =
          NatP.m≤m+n
            (Size.formulaNodeCount (constructor input)
             + Size.formulaNodeCount (constructor input))
            (Size.formulaNodeCount (constructor input))

        tripleNodeLower :
          inputLength + inputLength
          ≤
          three * Size.formulaNodeCount
            (constructor input)
        tripleNodeLower =
          NatP.≤-trans
            doubleInputBelowDoubleNodes
            doubleNodesBelowTripleNodes

    codeBelowInput :
      Binary.formulaBitCodeLength
        (constructor input)
      ≤ inputLength
    codeBelowInput =
      NatP.≤-reflexive
        (congLength fixed)

    congLength :
      input
      ≡ Binary.encodeFormulaBits (constructor input) →
      Binary.listLength input
      ≡
      Binary.formulaBitCodeLength (constructor input)
    congLength refl =
      refl

------------------------------------------------------------------------
-- Research consequence.
--
-- Under this concrete quotation, a same-or-larger AST cannot literally equal
-- its own nonempty binary input code.  Hence any viable resource-bounded
-- diagonal constructor in that regime must use behavioural/semantic
-- self-reference rather than raw source-string equality.
------------------------------------------------------------------------
