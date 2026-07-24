module DASHI.Physics.YangMills.BalabanQuadraticOperatorPerturbationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _+ℝ_; +-assoc)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact A* A - B* B algebra in inner-product form.
--
-- If a background-dependent operator is written as B+D, its quadratic penalty
-- is the base penalty plus two cross terms and the D^*D term.  Gauge fixing and
-- the covariant block constraint both use this theorem, so their analytic work
-- is reduced to bounding the same three explicit pieces.
------------------------------------------------------------------------

record AdditiveInnerProductCarrier (State : Set) : Set₁ where
  field
    addState : State → State → State
    inner : State → State → ℝ

    innerAddLeft : ∀ left right test →
      inner (addState left right) test
      ≡ inner left test +ℝ inner right test

    innerAddRight : ∀ test left right →
      inner test (addState left right)
      ≡ inner test left +ℝ inner test right

open AdditiveInnerProductCarrier public

quadraticValue :
  ∀ {State} → AdditiveInnerProductCarrier State → State → ℝ
quadraticValue carrier state = inner carrier state state

quadraticPerturbationR :
  ∀ {State} → AdditiveInnerProductCarrier State → State → State → ℝ
quadraticPerturbationR carrier base perturbation =
  inner carrier base perturbation
  +ℝ (inner carrier perturbation base
  +ℝ inner carrier perturbation perturbation)

quadraticOperatorPerturbationExact :
  ∀ {State}
    (carrier : AdditiveInnerProductCarrier State)
    base perturbation →
  quadraticValue carrier (addState carrier base perturbation)
  ≡ quadraticValue carrier base
    +ℝ quadraticPerturbationR carrier base perturbation
quadraticOperatorPerturbationExact carrier base perturbation =
  trans
    (innerAddLeft carrier base perturbation
      (addState carrier base perturbation))
    (trans
      (cong
        (λ right →
          inner carrier base (addState carrier base perturbation) +ℝ right)
        (innerAddRight carrier perturbation base perturbation))
      (trans
        (cong
          (λ left →
            left +ℝ
              (inner carrier perturbation base
              +ℝ inner carrier perturbation perturbation))
          (innerAddRight carrier base base perturbation))
        (+-assoc
          (inner carrier base base)
          (inner carrier base perturbation)
          (inner carrier perturbation base
            +ℝ inner carrier perturbation perturbation))))

record SymmetricAdditiveInnerProductCarrier (State : Set) : Set₁ where
  field
    additiveCarrier : AdditiveInnerProductCarrier State
    innerSymmetric : ∀ left right →
      inner additiveCarrier left right ≡ inner additiveCarrier right left

open SymmetricAdditiveInnerProductCarrier public

symmetricQuadraticPerturbationR :
  ∀ {State} → SymmetricAdditiveInnerProductCarrier State →
  State → State → ℝ
symmetricQuadraticPerturbationR carrier base perturbation =
  inner (additiveCarrier carrier) base perturbation
  +ℝ (inner (additiveCarrier carrier) base perturbation
  +ℝ inner (additiveCarrier carrier) perturbation perturbation)

symmetricQuadraticOperatorPerturbationExact :
  ∀ {State}
    (carrier : SymmetricAdditiveInnerProductCarrier State)
    base perturbation →
  quadraticValue (additiveCarrier carrier)
    (addState (additiveCarrier carrier) base perturbation)
  ≡ quadraticValue (additiveCarrier carrier) base
    +ℝ symmetricQuadraticPerturbationR carrier base perturbation
symmetricQuadraticOperatorPerturbationExact carrier base perturbation =
  trans
    (quadraticOperatorPerturbationExact
      (additiveCarrier carrier) base perturbation)
    (cong
      (λ remainder →
        quadraticValue (additiveCarrier carrier) base +ℝ remainder)
      (cong
        (λ middle →
          inner (additiveCarrier carrier) base perturbation
          +ℝ (middle
          +ℝ inner (additiveCarrier carrier) perturbation perturbation))
        (sym (innerSymmetric carrier base perturbation))))

record OperatorDifferenceCarrier (Index State : Set) : Set₁ where
  field
    innerCarrier : SymmetricAdditiveInnerProductCarrier State
    baseOperator perturbationOperator fullOperator : Index → State → State

    fullOperatorDefinition : ∀ index state →
      fullOperator index state
      ≡ addState (additiveCarrier innerCarrier)
          (baseOperator index state)
          (perturbationOperator index state)

open OperatorDifferenceCarrier public

operatorQuadraticPerturbationExact :
  ∀ {Index State}
    (dataSet : OperatorDifferenceCarrier Index State)
    index state →
  quadraticValue (additiveCarrier (innerCarrier dataSet))
    (fullOperator dataSet index state)
  ≡ quadraticValue (additiveCarrier (innerCarrier dataSet))
      (baseOperator dataSet index state)
    +ℝ symmetricQuadraticPerturbationR
      (innerCarrier dataSet)
      (baseOperator dataSet index state)
      (perturbationOperator dataSet index state)
operatorQuadraticPerturbationExact dataSet index state
  rewrite fullOperatorDefinition dataSet index state =
  symmetricQuadraticOperatorPerturbationExact
    (innerCarrier dataSet)
    (baseOperator dataSet index state)
    (perturbationOperator dataSet index state)

quadraticOperatorPerturbationAlgebraLevel : ProofLevel
quadraticOperatorPerturbationAlgebraLevel = machineChecked

gaugeFixingDifferenceExpansionLevel : ProofLevel
gaugeFixingDifferenceExpansionLevel = machineChecked

blockPenaltyDifferenceExpansionLevel : ProofLevel
blockPenaltyDifferenceExpansionLevel = machineChecked

physicalCrossTermBoundsLevel : ProofLevel
physicalCrossTermBoundsLevel = conditional
