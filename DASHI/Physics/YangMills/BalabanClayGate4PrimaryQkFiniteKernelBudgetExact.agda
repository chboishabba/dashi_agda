module DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Balaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Equations (42)--(43) give the local averaging operation. Immediately after
-- (43), Balaban states that the kth average at a coarse bond c depends only on
-- fine bonds in B^k(c_-) union B^k(c_+). Proposition 4 and equations
-- (146)--(147) give the linearized estimate
--
--   |Q_k(U_0) A| <= (1 + 2 C'_1 alpha_0) Q'_k |A|,
--   |Q_k(U_0;c,b)| <= 1 + 2 C'_1 alpha_0.
--
-- The theorem below performs the finite step that is implicit but necessary for
-- numerical budgets: point-level matrix entries bounded by M on a finite set of
-- size S imply that the row sum is bounded by S * M.
------------------------------------------------------------------------

record OrderedAdditiveScale (Scalar : Set) : Set₁ where
  field
    zeroScalar : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left right leftUpper rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

open OrderedAdditiveScale public

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) = function value ∷ mapList function values

mapListLength : ∀ {A B : Set} (function : A → B) (values : List A) →
  listLength (mapList function values) ≡ listLength values
mapListLength function [] = refl
mapListLength function (value ∷ values) = cong suc (mapListLength function values)

finiteSum : ∀ {Scalar : Set} →
  OrderedAdditiveScale Scalar → List Scalar → Scalar
finiteSum algebra [] = zeroScalar algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

natScale : ∀ {Scalar : Set} →
  OrderedAdditiveScale Scalar → Nat → Scalar → Scalar
natScale algebra zero value = zeroScalar algebra
natScale algebra (suc count) value =
  add algebra value (natScale algebra count value)

data AllBelow {Scalar : Set}
    (algebra : OrderedAdditiveScale Scalar)
    (bound : Scalar) : List Scalar → Set where
  allBelowNil : AllBelow algebra bound []
  allBelowCons : ∀ {value values} →
    LessEqual algebra value bound →
    AllBelow algebra bound values →
    AllBelow algebra bound (value ∷ values)

finiteSumBelowCardinalityScale :
  ∀ {Scalar : Set}
    (algebra : OrderedAdditiveScale Scalar)
    (bound : Scalar)
    {values : List Scalar} →
  AllBelow algebra bound values →
  LessEqual algebra
    (finiteSum algebra values)
    (natScale algebra (listLength values) bound)
finiteSumBelowCardinalityScale algebra bound allBelowNil =
  reflexive algebra (zeroScalar algebra)
finiteSumBelowCardinalityScale algebra bound
  (allBelowCons valueBelow restBelow) =
  addMonotone algebra valueBelow
    (finiteSumBelowCardinalityScale algebra bound restBelow)

record BalabanPrimaryQkRowData
    (CoarseBond FineBond Scalar : Set)
    (algebra : OrderedAdditiveScale Scalar) : Set₁ where
  field
    kernelAbsoluteValue : CoarseBond → FineBond → Scalar
    localSupport : CoarseBond → List FineBond

    primaryEntryBound : Scalar
    rowBudget : CoarseBond → Scalar

    -- Proposition 4, equation (147), after the physical kernel and norm are
    -- identified with the selected Scalar carrier.
    proposition4PointwiseBound : ∀ (coarse : CoarseBond) (fine : FineBond) →
      LessEqual algebra
        (kernelAbsoluteValue coarse fine)
        primaryEntryBound

    -- Locality after equation (43), together with the literal finite block
    -- enumeration, supplies this cardinality-to-budget estimate.
    localSupportCardinalityBudget : ∀ (coarse : CoarseBond) →
      LessEqual algebra
        (natScale algebra
          (listLength (localSupport coarse))
          primaryEntryBound)
        (rowBudget coarse)

open BalabanPrimaryQkRowData public

localKernelValues :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : OrderedAdditiveScale Scalar} →
  BalabanPrimaryQkRowData CoarseBond FineBond Scalar algebra →
  CoarseBond → List Scalar
localKernelValues dataSet coarse =
  mapList (kernelAbsoluteValue dataSet coarse) (localSupport dataSet coarse)

localKernelValuesPointwiseBelow :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : OrderedAdditiveScale Scalar}
    (dataSet : BalabanPrimaryQkRowData
      CoarseBond FineBond Scalar algebra)
    (coarse : CoarseBond) →
  AllBelow algebra
    (primaryEntryBound dataSet)
    (localKernelValues dataSet coarse)
localKernelValuesPointwiseBelow {FineBond = FineBond} {algebra = algebra} dataSet coarse =
  go (localSupport dataSet coarse)
  where
  go : (support : List FineBond) →
    AllBelow algebra
      (primaryEntryBound dataSet)
      (mapList (kernelAbsoluteValue dataSet coarse) support)
  go [] = allBelowNil
  go (fine ∷ support) =
    allBelowCons
      (proposition4PointwiseBound dataSet coarse fine)
      (go support)

primaryQkLocalRowSumBelowBudget :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : OrderedAdditiveScale Scalar}
    (dataSet : BalabanPrimaryQkRowData
      CoarseBond FineBond Scalar algebra)
    (coarse : CoarseBond) →
  LessEqual algebra
    (finiteSum algebra (localKernelValues dataSet coarse))
    (rowBudget dataSet coarse)
primaryQkLocalRowSumBelowBudget {algebra = algebra} dataSet coarse =
  transitive algebra
    (subst (λ len → LessEqual algebra (finiteSum algebra (localKernelValues dataSet coarse)) (natScale algebra len (primaryEntryBound dataSet)))
      (mapListLength (kernelAbsoluteValue dataSet coarse) (localSupport dataSet coarse))
      (finiteSumBelowCardinalityScale algebra
        (primaryEntryBound dataSet)
        (localKernelValuesPointwiseBelow dataSet coarse)))
    (localSupportCardinalityBudget dataSet coarse)

record UniformFiniteKernelBudget
    (Index Entry Scalar : Set)
    (algebra : OrderedAdditiveScale Scalar) : Set₁ where
  field
    rowData : BalabanPrimaryQkRowData Index Entry Scalar algebra
    uniformBudget : Scalar
    everyRowBudgetUniform : ∀ (index : Index) →
      LessEqual algebra (rowBudget rowData index) uniformBudget

open UniformFiniteKernelBudget public

primaryQkEveryLocalRowBelowUniformBudget :
  ∀ {Index Entry Scalar : Set}
    {algebra : OrderedAdditiveScale Scalar}
    (dataSet : UniformFiniteKernelBudget Index Entry Scalar algebra)
    (index : Index) →
  LessEqual algebra
    (finiteSum algebra
      (localKernelValues (rowData dataSet) index))
    (uniformBudget dataSet)
primaryQkEveryLocalRowBelowUniformBudget {algebra = algebra} dataSet index =
  transitive algebra
    (primaryQkLocalRowSumBelowBudget (rowData dataSet) index)
    (everyRowBudgetUniform dataSet index)

finitePointwiseToRowSumLevel : ProofLevel
finitePointwiseToRowSumLevel = machineChecked

primaryQkLocalityToFiniteSupportLevel : ProofLevel
primaryQkLocalityToFiniteSupportLevel = standardImported

primaryQkPointwiseKernelBoundLevel : ProofLevel
primaryQkPointwiseKernelBoundLevel = standardImported

physicalQkKernelAndNormIdentificationInputsLevel : ProofLevel
physicalQkKernelAndNormIdentificationInputsLevel = conditional

physicalQkSupportCardinalityInputsLevel : ProofLevel
physicalQkSupportCardinalityInputsLevel = conditional
