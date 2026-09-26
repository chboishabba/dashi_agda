module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact where

------------------------------------------------------------------------
-- LAYERED RESIDUAL-FUNCTION WIDTH OF A SHANNON RESTRICTION FAMILY
--
-- The future-congruence owner proves, at fixed remaining arity:
--
--   FutureEquivalent
--     iff
--   equality of the residual Boolean functions.
--
-- This file turns that semantic normalization into a literal finite-state
-- lower bound for every honest Q1 quotient.
--
-- A width witness of size w at remaining arity r is an enumeration of w
-- reachable restriction nodes whose residual Boolean functions are pairwise
-- distinct.
--
-- Main theorem:
--
--   width witness w at layer r
--       ->
--   w <= stateCount(Q)
--
-- for every Q1 quotient Q on the same root.
--
-- CROSS-LAYER BOUNDARY:
--
-- The current Q1 interface does not forbid one finite state from being reused
-- at different remaining arities.  Therefore a sum of per-layer widths is NOT
-- derived unconditionally.
--
-- A separate AritySeparatedQ1 condition is introduced for exactly that stronger
-- accounting regime.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future

------------------------------------------------------------------------
-- A reachable node known to live at one exact remaining arity.
------------------------------------------------------------------------

record LayerNode
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining : Nat) : Set₁ where
  constructor layer-node
  field
    node :
      Family.RestrictionNode root

    arityExact :
      Family.currentVariables node
      ≡ remaining

open LayerNode public

------------------------------------------------------------------------
-- Residual-function equality inside one layer.
------------------------------------------------------------------------

LayerResidualEqual :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  LayerNode {root = root} remaining →
  LayerNode {root = root} remaining →
  Set
LayerResidualEqual left right =
  (assignment : SAT.Assignment remaining) →
  SAT.evaluate
      (Family.currentFormula (node left))
      (Future.transportAssignment
        (sym (arityExact left))
        assignment)
  ≡
  SAT.evaluate
      (Family.currentFormula (node right))
      (Future.transportAssignment
        (sym (arityExact right))
        assignment)

------------------------------------------------------------------------
-- A finite family of pairwise semantically distinct residuals.
--
-- Extensional formulation:
-- if two enumerated residual functions are equal, the indices were equal.
------------------------------------------------------------------------

record ResidualWidthWitness
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining width : Nat) : Set₁ where
  constructor residual-width-witness
  field
    representative :
      Fin width →
      LayerNode {root = root} remaining

    residualEqualIndicesEqual :
      ∀ {left right : Fin width} →
      LayerResidualEqual
        (representative left)
        (representative right) →
      left ≡ right

open ResidualWidthWitness public

------------------------------------------------------------------------
-- Q1 classification of a width witness.
------------------------------------------------------------------------

widthWitnessClassify :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (witness : ResidualWidthWitness remaining width) →
  Fin width →
  Fin (Quotient.stateCount quotient)
widthWitnessClassify quotient witness index =
  Quotient.classify
    quotient
    (Family.derivation
      (node
        (representative witness index)))

------------------------------------------------------------------------
-- Same Q1 state forces residual equality, hence width-witness indices equal.
------------------------------------------------------------------------

widthWitnessClassifyInjective :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (witness : ResidualWidthWitness remaining width)
    {left right : Fin width} →
  widthWitnessClassify quotient witness left
  ≡
  widthWitnessClassify quotient witness right →
  left ≡ right
widthWitnessClassifyInjective
    quotient
    witness
    {left}
    {right}
    sameState =
  residualEqualIndicesEqual witness
    residualEqual
  where
    leftNode :
      LayerNode remaining
    leftNode =
      representative witness left

    rightNode :
      LayerNode remaining
    rightNode =
      representative witness right

    sameArity :
      Family.currentVariables (node leftNode)
      ≡
      Family.currentVariables (node rightNode)
    sameArity =
      trans
        (arityExact leftNode)
        (sym (arityExact rightNode))

    pointwise :
      (assignment :
        SAT.Assignment
          (Family.currentVariables (node leftNode))) →
      SAT.evaluate
          (Family.currentFormula (node leftNode))
          assignment
      ≡
      SAT.evaluate
          (Family.currentFormula (node rightNode))
          (Future.transportAssignment
            sameArity
            assignment)
    pointwise =
      Future.sameLayerSameQ1StateImpliesPointwiseResidualEquality
        quotient
        sameArity
        sameState

    residualEqual :
      LayerResidualEqual leftNode rightNode
    residualEqual assignment
        with arityExact leftNode
           | arityExact rightNode
    ... | refl | refl =
      pointwise assignment

------------------------------------------------------------------------
-- Main per-layer semantic width lower bound.
------------------------------------------------------------------------

residualWidthBelowQ1StateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  ResidualWidthWitness remaining width →
  width ≤ Quotient.stateCount quotient
residualWidthBelowQ1StateCount quotient witness =
  FinP.injective⇒≤
    (widthWitnessClassifyInjective quotient witness)

------------------------------------------------------------------------
-- Exact-width certificate.
--
-- This avoids choosing a quotient implementation: width is exact when
--
--  1. width distinct residual functions are exhibited; and
--  2. every other finite same-layer future-distinct family has size <= width.
------------------------------------------------------------------------

record ExactResidualWidth
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining width : Nat) : Set₁ where
  constructor exact-residual-width
  field
    lowerWitness :
      ResidualWidthWitness {root = root} remaining width

    maximal :
      ∀ {candidateWidth : Nat} →
      ResidualWidthWitness {root = root} remaining candidateWidth →
      candidateWidth ≤ width

open ExactResidualWidth public

exactResidualWidthBelowQ1StateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  ExactResidualWidth {root = root} remaining width →
  width ≤ Quotient.stateCount quotient
exactResidualWidthBelowQ1StateCount quotient exact =
  residualWidthBelowQ1StateCount
    quotient
    (lowerWitness exact)

------------------------------------------------------------------------
-- Width profile.
--
-- We index by remaining arity rather than restriction depth.  For a root with
-- n variables, remaining arity r corresponds to depth n-r.
------------------------------------------------------------------------

record ResidualWidthProfile
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor residual-width-profile
  field
    widthAt :
      (remaining : Nat) →
      remaining ≤ rootVariables →
      Nat

    exactAt :
      (remaining : Nat) →
      (inRoot : remaining ≤ rootVariables) →
      ExactResidualWidth
        {root = root}
        remaining
        (widthAt remaining inRoot)

open ResidualWidthProfile public

profileLayerBelowQ1StateCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (profile : ResidualWidthProfile root)
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (remaining : Nat)
    (inRoot : remaining ≤ rootVariables) →
  widthAt profile remaining inRoot
  ≤
  Quotient.stateCount quotient
profileLayerBelowQ1StateCount
    profile quotient remaining inRoot =
  exactResidualWidthBelowQ1StateCount
    quotient
    (exactAt profile remaining inRoot)

------------------------------------------------------------------------
-- Cross-layer reuse boundary.
------------------------------------------------------------------------

record AritySeparatedQ1
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) : Set₁ where
  constructor arity-separated-q1
  field
    sameStateImpliesSameArity :
      {left right : Family.RestrictionNode root} →
      Quotient.classify quotient
          (Family.derivation left)
      ≡
      Quotient.classify quotient
          (Family.derivation right) →
      Family.currentVariables left
      ≡
      Family.currentVariables right

open AritySeparatedQ1 public

------------------------------------------------------------------------
-- Typed warning: the existing Q1 specification does not itself inhabit
-- AritySeparatedQ1.  Any summed-layer width theorem must consume this extra
-- separation theorem or an equivalent valid cross-layer normalization.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The semantic lower bound is now quotient-independent:
--
--   W_r(root) <= stateCount(Q)
--
-- at every Shannon layer r.
--
-- Summing W_r across layers is a strictly stronger statement and requires
-- proof that the finite Q1 carrier does not reuse states across different
-- remaining arities.
--
-- The next falsification test is therefore about the SPECIAL self-instantiated
-- roots: can generic high-width residual families be embedded into those roots
-- while preserving a layer's residual-function distinctions?
------------------------------------------------------------------------
