module DASHI.Physics.Closure.NSTriadKNQGapTransfer where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP
  using (≤-refl; ≤-trans; *-monoʳ-≤; *-assoc; *-comm)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as OperatorCN
import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

------------------------------------------------------------------------
-- q_gap transfer surface.
--
-- The operator C/N theorem does not by itself imply q_gap(N) >= c / N^2. The
-- missing ingredient is an explicit residue / gap scaling compatibility.

record NSTriadKNQGapTransferModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    operatorCNModel :
      OperatorCN.NSTriadKNPairIncidenceCNTheoremModel {ℓS} {ℓE} {ℓV} {ℓR}

    residueScaleCompatibility :
      (N : Shell (OperatorCN.cnDecompositionModel operatorCNModel)) ->
      Set ℓR

    qGapTarget :
      Shell (OperatorCN.cnDecompositionModel operatorCNModel) ->
      CrossMatrix.Bound
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel operatorCNModel))

    qGapFunctional :
      Shell (OperatorCN.cnDecompositionModel operatorCNModel) ->
      CrossMatrix.Bound
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel operatorCNModel))

    operatorCNToQGapN2Transfer :
      (N : Shell (OperatorCN.cnDecompositionModel operatorCNModel)) ->
      residueScaleCompatibility N ->
      CrossMatrix._≤_
        (WeightedSchur.profileMatrixModel
          (OperatorCN.weightedSchurModel operatorCNModel))
        (qGapFunctional N)
        (qGapTarget N)

open NSTriadKNQGapTransferModel public

qGapDecompositionModel :
  ∀ {ℓS ℓE ℓV ℓR} ->
  NSTriadKNQGapTransferModel {ℓS} {ℓE} {ℓV} {ℓR} ->
  _
qGapDecompositionModel m =
  OperatorCN.cnDecompositionModel (operatorCNModel m)

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record WeakStrongNormScaling (Carrier : Set) : Set₁ where
  constructor mkWeakStrongNormScaling
  field
    -- The q-gap bridge is not formal from an operator C/N bound alone;
    -- it needs an auxiliary weak/strong norm comparison or an equivalent
    -- quadratic perturbation mechanism.
    weakNormSquared : Carrier → Nat
    strongNormSquared : Carrier → Nat

    operatorWeakCN : Set
    weakStrongN1 : Set
    operatorCNToStrongErrorN2 : Set

    -- This lane is the first actual Blocker 2 theorem target.
    normScalingClosed : Bool

record WeakStrongNormScalingTarget : Set₁ where
  constructor mkWeakStrongNormScalingTarget
  field
    residueNormModel : ResidueNorm.ResidueNormModel
    shellIndex : Nat
    carrierElement : ResidueNorm.Carrier residueNormModel shellIndex

    operatorWeakCN : Set

    -- Explicitly names the composed N⁻¹ → N⁻² error conversion route.
    operatorCNToStrongErrorN2 : Set

    targetClosed : Bool

normModelWeakStrongN1 :
  (target : WeakStrongNormScalingTarget) →
  Set
normModelWeakStrongN1 target =
  WeakStrongNormScalingTarget.shellIndex target
    * ResidueNorm.weakNormSquared
        (WeakStrongNormScalingTarget.residueNormModel target)
        (WeakStrongNormScalingTarget.shellIndex target)
        (WeakStrongNormScalingTarget.carrierElement target)
    ≤
    ResidueNorm.strongNormSquared
      (WeakStrongNormScalingTarget.residueNormModel target)
      (WeakStrongNormScalingTarget.shellIndex target)
      (WeakStrongNormScalingTarget.carrierElement target)

operatorStrongErrorN2Target :
  {Carrier : Set} →
  (N : Nat) →
  (strongNormSquared : Carrier → Nat) →
  (weakError : Carrier → Nat) →
  (errorConstant : Nat) →
  Set
operatorStrongErrorN2Target {Carrier} N strongNormSquared weakError errorConstant =
  (x : Carrier) → N * (N * weakError x) ≤ errorConstant * strongNormSquared x

operatorCNWeakStrongComposeN2 :
  {Carrier : Set} →
  (N : Nat) →
  (weakNormSquared : Carrier → Nat) →
  (strongNormSquared : Carrier → Nat) →
  (weakError : Carrier → Nat) →
  (errorConstant : Nat) →
  ((x : Carrier) →
    N * weakError x ≤ errorConstant * weakNormSquared x) →
  ((x : Carrier) →
    N * weakNormSquared x ≤ strongNormSquared x) →
  operatorStrongErrorN2Target
    N
    strongNormSquared
    weakError
    errorConstant
operatorCNWeakStrongComposeN2
  N weakNormSquared strongNormSquared weakError errorConstant
  operatorWeakCNArithmetic weakStrongArithmetic x =
  ≤-trans step1 step2
  where
    step1 :
      N * (N * weakError x) ≤
      N * (errorConstant * weakNormSquared x)
    step1 =
      *-monoʳ-≤
        N
        (operatorWeakCNArithmetic x)

    step2 :
      N * (errorConstant * weakNormSquared x) ≤
      errorConstant * strongNormSquared x
    step2
      rewrite sym (*-assoc N errorConstant (weakNormSquared x))
            | *-comm N errorConstant
            | *-assoc errorConstant N (weakNormSquared x) =
      *-monoʳ-≤
        errorConstant
        (weakStrongArithmetic x)

record BaseGapMinusErrorAbsorption : Set₁ where
  constructor mkBaseGapMinusErrorAbsorption
  field
    baseGapN2 : Set
    operatorErrorN2 : Set
    gapPerturbationAbsorption : Set

    -- This lane is the second actual Blocker 2 theorem target.
    perturbationAbsorptionClosed : Bool

record BaseGapMinusErrorAbsorptionTarget : Set₁ where
  constructor mkBaseGapMinusErrorAbsorptionTarget
  field
    -- Placeholder theorem surface for the second live Blocker 2 estimate:
    --
    --   q_N = q_N^base - err_N
    --   q_N^base ≥ a / N²
    --   err_N ≤ b / N²
    --   b < a
    --
    -- so q_N ≥ (a - b) / N².
    baseGapN2 : Set
    operatorErrorN2 : Set
    gapMarginPositive : Set
    gapPerturbationAbsorption : Set

    targetClosed : Bool

toWeakStrongNormScaling :
  (target : WeakStrongNormScalingTarget) →
  WeakStrongNormScaling
    (ResidueNorm.Carrier
      (WeakStrongNormScalingTarget.residueNormModel target)
      (WeakStrongNormScalingTarget.shellIndex target))
toWeakStrongNormScaling target =
  mkWeakStrongNormScaling
    (λ x →
      ResidueNorm.weakNormSquared
        (WeakStrongNormScalingTarget.residueNormModel target)
        (WeakStrongNormScalingTarget.shellIndex target)
        x)
    (λ x →
      ResidueNorm.strongNormSquared
        (WeakStrongNormScalingTarget.residueNormModel target)
        (WeakStrongNormScalingTarget.shellIndex target)
        x)
    (WeakStrongNormScalingTarget.operatorWeakCN target)
    (normModelWeakStrongN1 target)
    (WeakStrongNormScalingTarget.operatorCNToStrongErrorN2 target)
    (WeakStrongNormScalingTarget.targetClosed target)

toBaseGapMinusErrorAbsorption :
  BaseGapMinusErrorAbsorptionTarget →
  BaseGapMinusErrorAbsorption
toBaseGapMinusErrorAbsorption target =
  mkBaseGapMinusErrorAbsorption
    (BaseGapMinusErrorAbsorptionTarget.baseGapN2 target)
    (BaseGapMinusErrorAbsorptionTarget.operatorErrorN2 target)
    (BaseGapMinusErrorAbsorptionTarget.gapPerturbationAbsorption target)
    (BaseGapMinusErrorAbsorptionTarget.targetClosed target)

record ResidueScaleCompatibility : Set₁ where
  constructor mkResidueScaleCompatibility
  field
    Carrier : Set
    weakStrongScaling : WeakStrongNormScaling Carrier
    baseGapAbsorption : BaseGapMinusErrorAbsorption

    -- Named closure witness for the actual C/N -> q_gap >= c/N^2 route.
    qGapTransferWitness : Set
    compatibilityRouteClosed : Bool

open ResidueScaleCompatibility public

weakNormSquared :
  (compat : ResidueScaleCompatibility) →
  Carrier compat → Nat
weakNormSquared compat =
  WeakStrongNormScaling.weakNormSquared
    (weakStrongScaling compat)

strongNormSquared :
  (compat : ResidueScaleCompatibility) →
  Carrier compat → Nat
strongNormSquared compat =
  WeakStrongNormScaling.strongNormSquared
    (weakStrongScaling compat)

operatorWeakCN :
  (compat : ResidueScaleCompatibility) →
  Set
operatorWeakCN compat =
  WeakStrongNormScaling.operatorWeakCN
    (weakStrongScaling compat)

weakStrongN1 :
  (compat : ResidueScaleCompatibility) →
  Set
weakStrongN1 compat =
  WeakStrongNormScaling.weakStrongN1
    (weakStrongScaling compat)

operatorCNToStrongErrorN2 :
  (compat : ResidueScaleCompatibility) →
  Set
operatorCNToStrongErrorN2 compat =
  WeakStrongNormScaling.operatorCNToStrongErrorN2
    (weakStrongScaling compat)

baseGapN2 :
  (compat : ResidueScaleCompatibility) →
  Set
baseGapN2 compat =
  BaseGapMinusErrorAbsorption.baseGapN2
    (baseGapAbsorption compat)

operatorErrorN2 :
  (compat : ResidueScaleCompatibility) →
  Set
operatorErrorN2 compat =
  BaseGapMinusErrorAbsorption.operatorErrorN2
    (baseGapAbsorption compat)

gapMarginPositive :
  (target : BaseGapMinusErrorAbsorptionTarget) →
  Set
gapMarginPositive target =
  BaseGapMinusErrorAbsorptionTarget.gapMarginPositive target

gapPerturbationAbsorption :
  (compat : ResidueScaleCompatibility) →
  Set
gapPerturbationAbsorption compat =
  BaseGapMinusErrorAbsorption.gapPerturbationAbsorption
    (baseGapAbsorption compat)

qGapTransferClosed : ResidueScaleCompatibility → Bool
qGapTransferClosed compat
  with OperatorCN.pairIncidenceCNTheoremClosed
     | compatibilityRouteClosed compat
... | true | true = true
... | true | false = false
... | false | _ = false

qGapTransferClosedIsTrue :
  (compat : ResidueScaleCompatibility) →
  compatibilityRouteClosed compat ≡ true →
  qGapTransferClosed compat ≡ true
qGapTransferClosedIsTrue compat routeClosed
  rewrite OperatorCN.pairIncidenceCNTheoremClosedIsTrue
        | routeClosed = refl
