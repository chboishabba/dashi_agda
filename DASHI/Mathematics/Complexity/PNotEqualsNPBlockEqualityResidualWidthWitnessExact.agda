module DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact where

------------------------------------------------------------------------
-- LITERAL 2^n RESIDUAL-WIDTH WITNESS FOR BLOCK-ORDERED EQUALITY
--
-- Root variable order:
--
--   x_0 ... x_(n-1)  y_0 ... y_(n-1)
--
-- Formula:
--
--   EQ_n(x,y) = AND_i (x_i <-> y_i).
--
-- After Shannon-restricting the first n variables to a prefix a : Bool^n,
-- the remaining n-variable residual computes
--
--   y |-> [a = y].
--
-- Hence the 2^n possible x-prefixes give 2^n pairwise distinct residual
-- Boolean functions at one literal Shannon layer.  This file packages those
-- reachable residuals as the repository's actual ResidualWidthWitness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as FinBase
import Data.Fin.Properties as FinP
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPIndexedFormulaVariableReorderingExact as Rename
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact as Equality
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal

------------------------------------------------------------------------
-- Canonical left/right block embeddings.
------------------------------------------------------------------------

leftBlock :
  ∀ {left right : Nat} →
  Fin left →
  Fin (left + right)
leftBlock {left} {right} index =
  FinBase.join left right (inj₁ index)

rightBlock :
  ∀ {left right : Nat} →
  Fin right →
  Fin (left + right)
rightBlock {left} {right} index =
  FinBase.join left right (inj₂ index)

------------------------------------------------------------------------
-- Formula for Boolean equality of two selected variables.
------------------------------------------------------------------------

bitEqualityFormula :
  ∀ {variables : Nat} →
  Fin variables →
  Fin variables →
  SAT.BooleanFormula variables
bitEqualityFormula left right =
  SAT.disjunction
    (SAT.conjunction
      (SAT.variable left)
      (SAT.variable right))
    (SAT.conjunction
      (SAT.negate (SAT.variable left))
      (SAT.negate (SAT.variable right)))

bitEqualityEvaluation :
  ∀ {variables : Nat}
    (left right : Fin variables)
    (assignment : SAT.Assignment variables) →
  SAT.evaluate
      (bitEqualityFormula left right)
      assignment
  ≡
  Equality.boolEq
    (assignment left)
    (assignment right)
bitEqualityEvaluation left right assignment
    with assignment left | assignment right
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

------------------------------------------------------------------------
-- Tail embedding:
--
--   old x_i -> new x_(i+1)
--   old y_i -> new y_(i+1).
------------------------------------------------------------------------

tailEmbedding :
  ∀ {width : Nat} →
  Fin (width + width) →
  Fin (suc width + suc width)
tailEmbedding {width} index
    with FinBase.splitAt width index
... | inj₁ left =
  leftBlock
    {left = suc width}
    {right = suc width}
    (FinBase.suc left)
... | inj₂ right =
  rightBlock
    {left = suc width}
    {right = suc width}
    (FinBase.suc right)

------------------------------------------------------------------------
-- Compact block-ordered equality formula.
------------------------------------------------------------------------

blockEqualityFormula :
  (width : Nat) →
  SAT.BooleanFormula (width + width)
blockEqualityFormula zero =
  SAT.constant true
blockEqualityFormula (suc width) =
  SAT.conjunction
    (bitEqualityFormula
      (leftBlock
        {left = suc width}
        {right = suc width}
        FinBase.zero)
      (rightBlock
        {left = suc width}
        {right = suc width}
        FinBase.zero))
    (Rename.renameFormula
      tailEmbedding
      (blockEqualityFormula width))

------------------------------------------------------------------------
-- Vector-backed block assignments.
------------------------------------------------------------------------

vecAssignment :
  ∀ {width : Nat} →
  Vec Bool width →
  SAT.Assignment width
vecAssignment bits index =
  Circuit.lookupVec index bits

prefixAssignment :
  ∀ {prefix remaining : Nat} →
  Vec Bool prefix →
  SAT.Assignment remaining →
  SAT.Assignment (prefix + remaining)
prefixAssignment [] tail =
  tail
prefixAssignment (bit ∷ bits) tail =
  SAT.extendAssignment
    bit
    (prefixAssignment bits tail)

blockAssignment :
  ∀ {width : Nat} →
  Vec Bool width →
  Vec Bool width →
  SAT.Assignment (width + width)
blockAssignment left right =
  prefixAssignment
    left
    (vecAssignment right)

------------------------------------------------------------------------
-- Lookup of canonical block embeddings.
------------------------------------------------------------------------

prefixAssignmentLeftBlock :
  ∀ {prefix remaining : Nat}
    (bits : Vec Bool prefix)
    (tail : SAT.Assignment remaining)
    (index : Fin prefix) →
  prefixAssignment bits tail
    (leftBlock
      {left = prefix}
      {right = remaining}
      index)
  ≡
  Circuit.lookupVec index bits
prefixAssignmentLeftBlock
    (bit ∷ bits)
    tail
    FinBase.zero =
  refl
prefixAssignmentLeftBlock
    (bit ∷ bits)
    tail
    (FinBase.suc index) =
  prefixAssignmentLeftBlock
    bits
    tail
    index

prefixAssignmentRightBlock :
  ∀ {prefix remaining : Nat}
    (bits : Vec Bool prefix)
    (tail : SAT.Assignment remaining)
    (index : Fin remaining) →
  prefixAssignment bits tail
    (rightBlock
      {left = prefix}
      {right = remaining}
      index)
  ≡
  tail index
prefixAssignmentRightBlock [] tail index =
  refl
prefixAssignmentRightBlock
    (bit ∷ bits)
    tail
    index =
  prefixAssignmentRightBlock
    bits
    tail
    index

------------------------------------------------------------------------
-- Under a successor-width block assignment, the renamed tail sees exactly the
-- tail block assignment.
------------------------------------------------------------------------

tailEmbeddingAssignmentExact :
  ∀ {width : Nat}
    (leftBit rightBit : Bool)
    (leftTail rightTail : Vec Bool width)
    (index : Fin (width + width)) →
  Rename.renameAssignment
      tailEmbedding
      (blockAssignment
        (leftBit ∷ leftTail)
        (rightBit ∷ rightTail))
      index
  ≡
  blockAssignment leftTail rightTail index
tailEmbeddingAssignmentExact
    {width}
    leftBit
    rightBit
    leftTail
    rightTail
    index
    with FinBase.splitAt width index
       | FinP.join-splitAt width width index
... | inj₁ left | joined
    rewrite
      sym joined
      |
      FinP.splitAt-join
        width
        width
        (inj₁ left)
      |
      prefixAssignmentLeftBlock
        (leftBit ∷ leftTail)
        (vecAssignment (rightBit ∷ rightTail))
        (FinBase.suc left)
      |
      prefixAssignmentLeftBlock
        leftTail
        (vecAssignment rightTail)
        left =
  refl
... | inj₂ right | joined
    rewrite
      sym joined
      |
      FinP.splitAt-join
        width
        width
        (inj₂ right)
      |
      prefixAssignmentRightBlock
        (leftBit ∷ leftTail)
        (vecAssignment (rightBit ∷ rightTail))
        (FinBase.suc right)
      |
      prefixAssignmentRightBlock
        leftTail
        (vecAssignment rightTail)
        right =
  refl

------------------------------------------------------------------------
-- Exact block-equality semantics.
------------------------------------------------------------------------

blockEqualityEvaluation :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  SAT.evaluate
      (blockEqualityFormula width)
      (blockAssignment left right)
  ≡
  Equality.vecEq left right
blockEqualityEvaluation [] [] =
  refl
blockEqualityEvaluation
    {suc width}
    (leftBit ∷ leftTail)
    (rightBit ∷ rightTail) =
  trans
    (cong₂
      SAT.andBool
      headExact
      tailExact)
    refl
  where
    assignment :
      SAT.Assignment
        (suc width + suc width)
    assignment =
      blockAssignment
        (leftBit ∷ leftTail)
        (rightBit ∷ rightTail)

    headExact :
      SAT.evaluate
        (bitEqualityFormula
          (leftBlock
            {left = suc width}
            {right = suc width}
            FinBase.zero)
          (rightBlock
            {left = suc width}
            {right = suc width}
            FinBase.zero))
        assignment
      ≡
      Equality.boolEq leftBit rightBit
    headExact =
      trans
        (bitEqualityEvaluation
          (leftBlock
            {left = suc width}
            {right = suc width}
            FinBase.zero)
          (rightBlock
            {left = suc width}
            {right = suc width}
            FinBase.zero)
          assignment)
        pairLookups
      where
        pairLookups :
          Equality.boolEq
            (assignment
              (leftBlock
                {left = suc width}
                {right = suc width}
                FinBase.zero))
            (assignment
              (rightBlock
                {left = suc width}
                {right = suc width}
                FinBase.zero))
          ≡
          Equality.boolEq leftBit rightBit
        pairLookups
          rewrite
            prefixAssignmentLeftBlock
              (leftBit ∷ leftTail)
              (vecAssignment (rightBit ∷ rightTail))
              FinBase.zero
            |
            prefixAssignmentRightBlock
              (leftBit ∷ leftTail)
              (vecAssignment (rightBit ∷ rightTail))
              FinBase.zero =
          refl

    renamedTailExact :
      SAT.evaluate
        (Rename.renameFormula
          tailEmbedding
          (blockEqualityFormula width))
        assignment
      ≡
      SAT.evaluate
        (blockEqualityFormula width)
        (blockAssignment leftTail rightTail)
    renamedTailExact =
      trans
        (Rename.renameEvaluation
          tailEmbedding
          (blockEqualityFormula width)
          assignment)
        (SAT.evaluateExtensional
          (blockEqualityFormula width)
          (tailEmbeddingAssignmentExact
            leftBit
            rightBit
            leftTail
            rightTail))

    tailExact :
      SAT.evaluate
        (Rename.renameFormula
          tailEmbedding
          (blockEqualityFormula width))
        assignment
      ≡
      Equality.vecEq leftTail rightTail
    tailExact =
      trans
        renamedTailExact
        (blockEqualityEvaluation
          leftTail
          rightTail)

------------------------------------------------------------------------
-- Replay a literal Boolean prefix through repeated head restrictions.
------------------------------------------------------------------------

restrictPrefix :
  ∀ {prefix remaining : Nat} →
  Vec Bool prefix →
  SAT.BooleanFormula (prefix + remaining) →
  SAT.BooleanFormula remaining
restrictPrefix [] formula =
  formula
restrictPrefix (false ∷ bits) formula =
  restrictPrefix bits
    (SAT.restrictHead false formula)
restrictPrefix (true ∷ bits) formula =
  restrictPrefix bits
    (SAT.restrictHead true formula)

restrictPrefixDerivationFrom :
  ∀ {rootVariables prefix remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula (prefix + remaining)}
    (derivation : Family.RestrictionDerivation root current)
    (bits : Vec Bool prefix) →
  Family.RestrictionDerivation
    root
    (restrictPrefix bits current)
restrictPrefixDerivationFrom derivation [] =
  derivation
restrictPrefixDerivationFrom derivation (false ∷ bits) =
  restrictPrefixDerivationFrom
    (Family.restrictionFalse derivation)
    bits
restrictPrefixDerivationFrom derivation (true ∷ bits) =
  restrictPrefixDerivationFrom
    (Family.restrictionTrue derivation)
    bits

restrictPrefixDerivation :
  ∀ {prefix remaining : Nat}
    (bits : Vec Bool prefix)
    (root : SAT.BooleanFormula (prefix + remaining)) →
  Family.RestrictionDerivation
    root
    (restrictPrefix bits root)
restrictPrefixDerivation bits root =
  restrictPrefixDerivationFrom
    Family.restrictionRoot
    bits

restrictPrefixEvaluation :
  ∀ {prefix remaining : Nat}
    (bits : Vec Bool prefix)
    (formula : SAT.BooleanFormula (prefix + remaining))
    (tail : SAT.Assignment remaining) →
  SAT.evaluate
      (restrictPrefix bits formula)
      tail
  ≡
  SAT.evaluate
      formula
      (prefixAssignment bits tail)
restrictPrefixEvaluation [] formula tail =
  refl
restrictPrefixEvaluation
    (false ∷ bits)
    formula
    tail =
  trans
    (restrictPrefixEvaluation
      bits
      (SAT.restrictHead false formula)
      tail)
    (SAT.restrictionEvaluation
      false
      formula
      (prefixAssignment bits tail))
restrictPrefixEvaluation
    (true ∷ bits)
    formula
    tail =
  trans
    (restrictPrefixEvaluation
      bits
      (SAT.restrictHead true formula)
      tail)
    (SAT.restrictionEvaluation
      true
      formula
      (prefixAssignment bits tail))

------------------------------------------------------------------------
-- Equality residual after fixing the whole x-block.
------------------------------------------------------------------------

equalityResidualFormula :
  ∀ {width : Nat} →
  Vec Bool width →
  SAT.BooleanFormula width
equalityResidualFormula {width} prefix =
  restrictPrefix
    prefix
    (blockEqualityFormula width)

equalityResidualEvaluation :
  ∀ {width : Nat}
    (prefix remaining : Vec Bool width) →
  SAT.evaluate
      (equalityResidualFormula prefix)
      (vecAssignment remaining)
  ≡
  Equality.equalityResidual
    prefix
    remaining
equalityResidualEvaluation prefix remaining =
  trans
    (restrictPrefixEvaluation
      prefix
      (blockEqualityFormula _)
      (vecAssignment remaining))
    (blockEqualityEvaluation
      prefix
      remaining)

------------------------------------------------------------------------
-- Actual reachable layer node for each prefix.
------------------------------------------------------------------------

equalityPrefixLayerNode :
  ∀ {width : Nat} →
  Vec Bool width →
  Width.LayerNode
    {root = blockEqualityFormula width}
    width
equalityPrefixLayerNode {width} prefix =
  Width.layer-node
    (Family.restriction-node
      width
      (equalityResidualFormula prefix)
      (restrictPrefixDerivation
        prefix
        (blockEqualityFormula width)))
    refl

------------------------------------------------------------------------
-- Residual equality reflects equality of prefixes.
------------------------------------------------------------------------

equalityPrefixResidualEqualImpliesPrefixEqual :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  Width.LayerResidualEqual
      (equalityPrefixLayerNode left)
      (equalityPrefixLayerNode right) →
  left ≡ right
equalityPrefixResidualEqualImpliesPrefixEqual
    left
    right
    residualEqual =
  Bits.bitsToFinInjective
    indicesEqual
  where
    leftIndex :
      Fin (Bits.bitCardinality _)
    leftIndex =
      Bits.bitsToFin left

    rightIndex :
      Fin (Bits.bitCardinality _)
    rightIndex =
      Bits.bitsToFin right

    pointwiseIndexed :
      (remaining : Vec Bool _) →
      Equality.indexedResidualFunction
        leftIndex
        remaining
      ≡
      Equality.indexedResidualFunction
        rightIndex
        remaining
    pointwiseIndexed remaining
      rewrite
        Bits.finToBitsAfterBitsToFin left
        |
        Bits.finToBitsAfterBitsToFin right =
      trans
        (sym
          (equalityResidualEvaluation
            left
            remaining))
        (trans
          (residualEqual
            (vecAssignment remaining))
          (equalityResidualEvaluation
            right
            remaining))

    indicesEqual :
      leftIndex ≡ rightIndex
    indicesEqual =
      Equality.indexedResidualFunctionInjective
        pointwiseIndexed

------------------------------------------------------------------------
-- Literal exponential width witness.
------------------------------------------------------------------------

blockEqualityResidualWidthWitness :
  (width : Nat) →
  Width.ResidualWidthWitness
    {root = blockEqualityFormula width}
    width
    (Bits.bitCardinality width)
blockEqualityResidualWidthWitness width =
  Width.residual-width-witness
    (λ index →
      equalityPrefixLayerNode
        (Bits.finToBits index))
    (λ {left} {right} residualEqual →
      Bits.finToBitsInjective
        (equalityPrefixResidualEqualImpliesPrefixEqual
          (Bits.finToBits left)
          (Bits.finToBits right)
          residualEqual))

------------------------------------------------------------------------
-- Direct consequence for any arity-tracked Q1 candidate on this literal root.
------------------------------------------------------------------------

blockEqualityNeedsTwoPowerNStates :
  ∀ {width : Nat}
    {candidate :
      Candidate.TransitionTableCandidate
        (blockEqualityFormula width)} →
  ArityTerminal.ArityTrackedTerminalAdmission
    candidate →
  Bits.bitCardinality width
  ≤
  Candidate.stateCount
    candidate
blockEqualityNeedsTwoPowerNStates admission =
  Width.residualWidthBelowArityAdmittedCandidateStateCount
    admission
    (blockEqualityResidualWidthWitness _)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The generic equality no-go is now in the exact currency of the live Q1 lane:
--
--   one concrete indexed root
--   one actual Shannon layer
--   2^n reachable residual functions
--   literal ResidualWidthWitness.
--
-- No abstract quotient, no external subfunction-count theorem and no
-- representation assumption remains between equality and the Q1 state lower
-- bound.
------------------------------------------------------------------------
