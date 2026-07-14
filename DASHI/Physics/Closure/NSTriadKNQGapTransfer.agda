module DASHI.Physics.Closure.NSTriadKNQGapTransfer where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; _<_; _∸_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties as NatP
  using (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; *-mono-≤; *-monoʳ-≤; *-assoc; *-comm; *-distribˡ-∸; *-distribʳ-∸; ∸-monoˡ-≤; ∸-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import Data.Product using (_×_)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as OperatorCN
import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness as ConcreteSchur
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
    errorIdentifiedWithOperatorStrongError : Set
    gapMarginPositive : Set
    gapPerturbationAbsorption : Set

    -- This lane is the second actual Blocker 2 theorem target.
    perturbationAbsorptionClosed : Bool

record GapQuadraticFormsTarget : Set₁ where
  constructor mkGapQuadraticFormsTarget
  field
    Carrier : Nat → Set
    shellIndex : Nat
    compatibilityScale : ScaleHeadroom.CompatibilityScale shellIndex

    qBase : Carrier shellIndex → Nat
    qError : Carrier shellIndex → Nat
    qGap : Carrier shellIndex → Nat

    gapDecompositionWitness :
      (x : Carrier shellIndex) →
      qGap x ≡ qBase x ∸ qError x

baseGapN2Target :
  (gapQuadraticForms : GapQuadraticFormsTarget) →
  (strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  (baseGapConstant : Nat) →
  Set
baseGapN2Target gapQuadraticForms strongNormSquared baseGapConstant =
  (x :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
  baseGapConstant * strongNormSquared x
    ≤
  ScaleHeadroom.CompatibilityScale.scaleSq
    (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    * GapQuadraticFormsTarget.qBase gapQuadraticForms x

record BaseFormCoercivity
    (gapQuadraticForms : GapQuadraticFormsTarget)
    (strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) : Set₁ where
  constructor mkBaseFormCoercivity
  field
    baseConstant : Nat
    basePositive : Set
    baseCoercive :
      baseGapN2Target gapQuadraticForms strongNormSquared baseConstant

record BaseGapN2Theorem
    (gapQuadraticForms : GapQuadraticFormsTarget)
    (strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) : Set₁ where
  constructor mkBaseGapN2Theorem
  field
    baseGapConstant : Nat
    baseGapPositive : Set
    baseGapN2Witness :
      baseGapN2Target gapQuadraticForms strongNormSquared baseGapConstant

baseGapFromCoercivity :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  BaseFormCoercivity gapQuadraticForms strongNormSquared →
  BaseGapN2Theorem gapQuadraticForms strongNormSquared
baseGapFromCoercivity coercivity =
  mkBaseGapN2Theorem
    (BaseFormCoercivity.baseConstant coercivity)
    (BaseFormCoercivity.basePositive coercivity)
    (BaseFormCoercivity.baseCoercive coercivity)

operatorErrorIdentifiedWithOperatorStrongErrorTarget :
  (gapQuadraticForms : GapQuadraticFormsTarget) →
  (operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  Set
operatorErrorIdentifiedWithOperatorStrongErrorTarget
  gapQuadraticForms operatorStrongError =
  (x :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
  GapQuadraticFormsTarget.qError gapQuadraticForms x
    ≤
  operatorStrongError x

operatorErrorN2Target :
  (gapQuadraticForms : GapQuadraticFormsTarget) →
  (strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  (errorConstant : Nat) →
  Set
operatorErrorN2Target gapQuadraticForms strongNormSquared errorConstant =
  (x :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
  ScaleHeadroom.CompatibilityScale.scaleSq
    (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    * GapQuadraticFormsTarget.qError gapQuadraticForms x
      ≤
  errorConstant * strongNormSquared x

record OperatorErrorIdentification
    (gapQuadraticForms : GapQuadraticFormsTarget)
    (operatorStrongError :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat)
    (strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) : Set₁ where
  constructor mkOperatorErrorIdentification
  field
    errorConstant : Nat
    errorIdentifiedWithOperatorStrongError :
      operatorErrorIdentifiedWithOperatorStrongErrorTarget
        gapQuadraticForms
        operatorStrongError
    operatorErrorN2Witness :
      operatorErrorN2Target
        gapQuadraticForms
        strongNormSquared
        errorConstant

record ScaledOperatorErrorBridge (N : Nat) (Carrier : Set) : Set₁ where
  constructor mkScaledOperatorErrorBridge
  field
    compatibilityScale : ScaleHeadroom.CompatibilityScale N
    qError : Carrier → Nat
    strongNormSquared : Carrier → Nat
    errorConstant : Nat
    scaledOperatorError :
      (x : Carrier) →
      ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
        * qError x
        ≤ errorConstant * strongNormSquared x

------------------------------------------------------------------------
-- Typed post-Schur bridge.
--
-- The concrete Schur layer supplies a numeric bound on its operator norm.
-- This helper lifts that bound to the q-gap error target only when the three
-- required comparisons are supplied explicitly: scale agreement, pointwise
-- q-error domination by the operator norm, and comparison of the Schur
-- constant with the strong-energy side.  No analytic premise is discharged
-- here.

postSchurScaledOperatorErrorBridgeFromNatHandoff :
  {N : Nat} ->
  {Carrier : Set} ->
  {operatorNorm rowBound columnBound scaledConstant : Nat} ->
  (scale : ScaleHeadroom.CompatibilityScale N) ->
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    ≡ suc N * suc N ->
  (handoff :
    ConcreteSchur.BipartiteNatSchurHandoff
      N operatorNorm rowBound columnBound scaledConstant) ->
  (qError : Carrier → Nat) ->
  (strongNormSquared : Carrier → Nat) ->
  (errorConstant : Nat) ->
  ((x : Carrier) → qError x ≤ operatorNorm) ->
  ((x : Carrier) → scaledConstant ≤ errorConstant * strongNormSquared x) ->
  ScaledOperatorErrorBridge N Carrier
postSchurScaledOperatorErrorBridgeFromNatHandoff
  {N = N}
  scale scaleMatches handoff qError strongNormSquared errorConstant
  qErrorBound constantBound =
  mkScaledOperatorErrorBridge
    scale
    qError
    strongNormSquared
    errorConstant
    (λ x ->
      ≤-trans
        (≤-reflexive
          (cong
            (λ z -> z * qError x)
            scaleMatches))
        (≤-trans
          (*-monoʳ-≤ (suc N * suc N) (qErrorBound x))
          (≤-trans
            (ConcreteSchur.BipartiteNatSchurHandoff.scaledOperatorBound
              handoff)
            (constantBound x))))

record SharperScaledOperatorErrorBridge (N : Nat) (Carrier : Set) : Set₁ where
  constructor mkSharperScaledOperatorErrorBridge
  field
    scaledBridge : ScaledOperatorErrorBridge N Carrier
    errorConstantBelowFour :
      ScaledOperatorErrorBridge.errorConstant scaledBridge
        < suc (suc (suc (suc zero)))

open SharperScaledOperatorErrorBridge public

record Stage3StrictKernelDefect (N : Nat) (Carrier : Set) : Set₁ where
  constructor mkStage3StrictKernelDefect
  field
    compatibilityScale : ScaleHeadroom.CompatibilityScale N
    qError : Carrier → Nat
    strongNormSquared : Carrier → Nat
    defectNorm : Carrier → Nat
    defectConstant : Nat
    defectPositive : zero < defectConstant
    stage3ErrorDefect :
      (x : Carrier) →
      ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
        * qError x
        + defectConstant * defectNorm x
        ≤
      ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
        * strongNormSquared x

stage3StrictKernelDefectTarget :
  {N : Nat} →
  {Carrier : Set} →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  (qError : Carrier → Nat) →
  (strongNormSquared : Carrier → Nat) →
  (defectNorm : Carrier → Nat) →
  (defectConstant : Nat) →
  Set
stage3StrictKernelDefectTarget
  {N} {Carrier} scale qError strongNormSquared defectNorm defectConstant =
  (zero < defectConstant)
  ×
  ((x : Carrier) →
    ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
      + defectConstant * defectNorm x
      ≤
    ScaleHeadroom.CompatibilityScale.scaleSq scale
      * strongNormSquared x)

sharperScaledOperatorErrorBridgeTarget :
  {N : Nat} →
  {Carrier : Set} →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  (qError : Carrier → Nat) →
  (strongNormSquared : Carrier → Nat) →
  (errorConstant : Nat) →
  Set
sharperScaledOperatorErrorBridgeTarget
  {N} {Carrier} scale qError strongNormSquared errorConstant =
  (errorConstant < suc (suc (suc (suc zero))))
  ×
  ((x : Carrier) →
    ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
      ≤ errorConstant * strongNormSquared x)

scaledOperatorErrorBridgeTarget :
  {N : Nat} →
  {Carrier : Set} →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  (qError : Carrier → Nat) →
  (strongNormSquared : Carrier → Nat) →
  (errorConstant : Nat) →
  Set
scaledOperatorErrorBridgeTarget {N} {Carrier} scale qError strongNormSquared errorConstant =
  (x : Carrier) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
    ≤ errorConstant * strongNormSquared x

scaledOperatorErrorBridgeAtScale :
  {N : Nat} →
  {Carrier : Set} →
  (bridge : ScaledOperatorErrorBridge N Carrier) →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    ≡
  ScaleHeadroom.CompatibilityScale.scaleSq
    (ScaledOperatorErrorBridge.compatibilityScale bridge) →
  scaledOperatorErrorBridgeTarget
    scale
    (ScaledOperatorErrorBridge.qError bridge)
    (ScaledOperatorErrorBridge.strongNormSquared bridge)
    (ScaledOperatorErrorBridge.errorConstant bridge)
scaledOperatorErrorBridgeAtScale bridge scale scaleMatches x =
  ≤-trans
    (≤-reflexive
      (cong
        (λ z → z * ScaledOperatorErrorBridge.qError bridge x)
        scaleMatches))
    (ScaledOperatorErrorBridge.scaledOperatorError bridge x)

postulate
  operatorErrorIdentificationFromStrongOperatorError
    :
    {gapQuadraticForms : GapQuadraticFormsTarget} →
    {operatorStrongError :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
    {strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
    (errorConstant : Nat) →
    operatorStrongErrorN2Target
      (ScaleHeadroom.CompatibilityScale.scaleSq
        (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms))
      strongNormSquared
      operatorStrongError
      errorConstant →
    operatorErrorIdentifiedWithOperatorStrongErrorTarget
      gapQuadraticForms
      operatorStrongError →
    OperatorErrorIdentification
      gapQuadraticForms
      operatorStrongError
      strongNormSquared

record GapMargin : Set₁ where
  constructor mkGapMargin
  field
    baseGapConstant : Nat
    errorConstant : Nat
    marginConstant : Nat
    marginPositive : zero < marginConstant
    marginEquation :
      baseGapConstant ≡ errorConstant + marginConstant

gapMarginFromTheorems :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms
      operatorStrongError
      strongNormSquared) →
  (marginConstant : Nat) →
  zero < marginConstant →
  (marginEquation :
    BaseGapN2Theorem.baseGapConstant baseGapTheorem
      ≡
    OperatorErrorIdentification.errorConstant operatorErrorIdentification
      + marginConstant) →
  GapMargin
gapMarginFromTheorems
  baseGapTheorem operatorErrorIdentification marginConstant
  marginPositive marginEquation =
  mkGapMargin
    (BaseGapN2Theorem.baseGapConstant baseGapTheorem)
    (OperatorErrorIdentification.errorConstant operatorErrorIdentification)
    marginConstant
    marginPositive
    marginEquation

baseMinusErrorEquation :
  (base error : Nat) →
  error ≤ base →
  base ≡ error + (base ∸ error)
baseMinusErrorEquation zero zero ≤base = refl
baseMinusErrorEquation (suc base) zero ≤base = refl
baseMinusErrorEquation zero (suc error) ()
baseMinusErrorEquation (suc base) (suc error) (s≤s error≤base) =
  cong suc (baseMinusErrorEquation base error error≤base)

positiveDifferenceFromStrictLess :
  (error base : Nat) →
  error < base →
  zero < (base ∸ error)
positiveDifferenceFromStrictLess zero zero ()
positiveDifferenceFromStrictLess zero (suc base) _ = s≤s z≤n
positiveDifferenceFromStrictLess (suc error) zero ()
positiveDifferenceFromStrictLess (suc error) (suc base) (s≤s error<base) =
  positiveDifferenceFromStrictLess error base error<base

gapMarginFromTheoremsAndLeq :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms
      operatorStrongError
      strongNormSquared) →
  zero <
    (BaseGapN2Theorem.baseGapConstant baseGapTheorem
      ∸ OperatorErrorIdentification.errorConstant operatorErrorIdentification) →
  OperatorErrorIdentification.errorConstant operatorErrorIdentification
    ≤
  BaseGapN2Theorem.baseGapConstant baseGapTheorem →
  GapMargin
gapMarginFromTheoremsAndLeq
  baseGapTheorem operatorErrorIdentification marginPositive error≤base =
  mkGapMargin
    base
    error
    (base ∸ error)
    marginPositive
    (baseMinusErrorEquation base error error≤base)
  where
    base : Nat
    base = BaseGapN2Theorem.baseGapConstant baseGapTheorem

    error : Nat
    error = OperatorErrorIdentification.errorConstant operatorErrorIdentification

record BaseGapMinusErrorAbsorptionTarget : Set₁ where
  constructor mkBaseGapMinusErrorAbsorptionTarget
  field
    gapQuadraticForms : GapQuadraticFormsTarget
    strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat
    operatorStrongError :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat
    baseGapTheorem :
      BaseGapN2Theorem gapQuadraticForms strongNormSquared
    operatorErrorIdentification :
      OperatorErrorIdentification
        gapQuadraticForms
        operatorStrongError
        strongNormSquared
    gapMargin : GapMargin
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
    (baseGapN2Target
    (BaseGapMinusErrorAbsorptionTarget.gapQuadraticForms target)
    (BaseGapMinusErrorAbsorptionTarget.strongNormSquared target)
      (BaseGapN2Theorem.baseGapConstant
        (BaseGapMinusErrorAbsorptionTarget.baseGapTheorem target)))
    (operatorErrorN2Target
      (BaseGapMinusErrorAbsorptionTarget.gapQuadraticForms target)
      (BaseGapMinusErrorAbsorptionTarget.strongNormSquared target)
      (OperatorErrorIdentification.errorConstant
        (BaseGapMinusErrorAbsorptionTarget.operatorErrorIdentification target)))
    (operatorErrorIdentifiedWithOperatorStrongErrorTarget
      (BaseGapMinusErrorAbsorptionTarget.gapQuadraticForms target)
      (BaseGapMinusErrorAbsorptionTarget.operatorStrongError target))
    (zero <
      GapMargin.marginConstant
        (BaseGapMinusErrorAbsorptionTarget.gapMargin target))
    (BaseGapMinusErrorAbsorptionTarget.gapPerturbationAbsorption target)
    (BaseGapMinusErrorAbsorptionTarget.targetClosed target)

record ResidueScaleCompatibility : Set₁ where
  constructor mkResidueScaleCompatibility
  field
    Carrier : Set
    compatibilityScale : ScaleHeadroom.CompatibilityScale 1
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

errorIdentifiedWithOperatorStrongError :
  (compat : ResidueScaleCompatibility) →
  Set
errorIdentifiedWithOperatorStrongError compat =
  BaseGapMinusErrorAbsorption.errorIdentifiedWithOperatorStrongError
    (baseGapAbsorption compat)

gapMarginPositive :
  (target : BaseGapMinusErrorAbsorptionTarget) →
  Set
gapMarginPositive target =
  zero <
    GapMargin.marginConstant
      (BaseGapMinusErrorAbsorptionTarget.gapMargin target)

gapPerturbationAbsorption :
  (compat : ResidueScaleCompatibility) →
  Set
gapPerturbationAbsorption compat =
  BaseGapMinusErrorAbsorption.gapPerturbationAbsorption
    (baseGapAbsorption compat)

gapPerturbationAbsorptionTarget :
  (gapQuadraticForms : GapQuadraticFormsTarget) →
  (strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms
      operatorStrongError
      strongNormSquared) →
  Set
gapPerturbationAbsorptionTarget
  gapQuadraticForms strongNormSquared baseGapTheorem
  operatorStrongError operatorErrorIdentification =
  (x :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
  ScaleHeadroom.CompatibilityScale.scaleSq
    (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    * GapQuadraticFormsTarget.qGap gapQuadraticForms x
      ≥
  (BaseGapN2Theorem.baseGapConstant baseGapTheorem
    ∸ OperatorErrorIdentification.errorConstant operatorErrorIdentification)
    * strongNormSquared x

operatorErrorN2FromWeakStrong :
  (compat : ResidueScaleCompatibility) →
  Set
operatorErrorN2FromWeakStrong compat =
  operatorCNToStrongErrorN2 compat

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

proveBaseGapMinusErrorAbsorption :
  (gapQuadraticForms : GapQuadraticFormsTarget) →
  (strongNormSquared : GapQuadraticFormsTarget.Carrier gapQuadraticForms (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) →
  (A C-err : Nat) →
  (baseGapN2 : (x : GapQuadraticFormsTarget.Carrier gapQuadraticForms (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
    A * strongNormSquared x ≤
      ScaleHeadroom.CompatibilityScale.scaleSq
        (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
        * GapQuadraticFormsTarget.qBase gapQuadraticForms x) →
  (operatorErrorN2 : (x : GapQuadraticFormsTarget.Carrier gapQuadraticForms (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
    ScaleHeadroom.CompatibilityScale.scaleSq
      (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
      * GapQuadraticFormsTarget.qError gapQuadraticForms x
      ≤ C-err * strongNormSquared x) →
  (gapDecomposition : (x : GapQuadraticFormsTarget.Carrier gapQuadraticForms (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
    GapQuadraticFormsTarget.qGap gapQuadraticForms x ≡ GapQuadraticFormsTarget.qBase gapQuadraticForms x ∸ GapQuadraticFormsTarget.qError gapQuadraticForms x) →
  (x : GapQuadraticFormsTarget.Carrier gapQuadraticForms (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)) →
  ScaleHeadroom.CompatibilityScale.scaleSq
    (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    * GapQuadraticFormsTarget.qGap gapQuadraticForms x
    ≥
  (A ∸ C-err) * strongNormSquared x
proveBaseGapMinusErrorAbsorption gapQuadraticForms strongNormSquared A C-err baseGapN2 operatorErrorN2 gapDecomposition x =
  let
    N = GapQuadraticFormsTarget.shellIndex gapQuadraticForms
    N2 = ScaleHeadroom.CompatibilityScale.scaleSq
      (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    qBase = GapQuadraticFormsTarget.qBase gapQuadraticForms x
    qError = GapQuadraticFormsTarget.qError gapQuadraticForms x
    qGap = GapQuadraticFormsTarget.qGap gapQuadraticForms x
    normSq = strongNormSquared x

    -- 1. (A ∸ C-err) * normSq ≡ A * normSq ∸ C-err * normSq
    eq1 : (A ∸ C-err) * normSq ≡ A * normSq ∸ C-err * normSq
    eq1 = *-distribʳ-∸ normSq A C-err

    -- 2. A * normSq ∸ C-err * normSq ≤ N2 * qBase ∸ C-err * normSq
    step2 : A * normSq ∸ C-err * normSq ≤ N2 * qBase ∸ C-err * normSq
    step2 = ∸-monoˡ-≤ (C-err * normSq) (baseGapN2 x)

    -- 3. N2 * qBase ∸ C-err * normSq ≤ N2 * qBase ∸ N2 * qError
    step3 : N2 * qBase ∸ C-err * normSq ≤ N2 * qBase ∸ N2 * qError
    step3 = ∸-monoʳ-≤ (N2 * qBase) (operatorErrorN2 x)

    -- 4. N2 * qBase ∸ N2 * qError ≡ N2 * (qBase ∸ qError)
    eq4 : N2 * qBase ∸ N2 * qError ≡ N2 * (qBase ∸ qError)
    eq4 = sym (*-distribˡ-∸ N2 qBase qError)

    -- 5. N2 * (qBase ∸ qError) ≡ N2 * qGap
    eq5 : N2 * (qBase ∸ qError) ≡ N2 * qGap
    eq5 = cong (λ z → N2 * z) (sym (gapDecomposition x))
  in
  ≤-trans (≤-reflexive eq1)
    (≤-trans step2
      (≤-trans step3
        (≤-trans (≤-reflexive eq4)
          (≤-reflexive eq5))))

strictGapMarginFromConstants :
  (baseGapConstant errorConstant : Nat) →
  errorConstant < baseGapConstant →
  GapMargin
strictGapMarginFromConstants baseGapConstant errorConstant error<base =
  mkGapMargin
    baseGapConstant
    errorConstant
    (baseGapConstant ∸ errorConstant)
    (positiveDifferenceFromStrictLess
      errorConstant
      baseGapConstant
      error<base)
    (baseMinusErrorEquation
      baseGapConstant
      errorConstant
      (<⇒≤ error<base))

strictScaledBaseGapMinusErrorAbsorption :
  {N : Nat} →
  {Carrier : Set} →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  (qBase qError qGap strongNormSquared : Carrier → Nat) →
  (baseGapConstant errorConstant : Nat) →
  ((x : Carrier) →
    baseGapConstant * strongNormSquared x ≤
    ScaleHeadroom.CompatibilityScale.scaleSq scale * qBase x) →
  ((x : Carrier) →
    ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x ≤
    errorConstant * strongNormSquared x) →
  ((x : Carrier) → qGap x ≡ qBase x ∸ qError x) →
  errorConstant < baseGapConstant →
  (x : Carrier) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale * qGap x
    ≥
  (baseGapConstant ∸ errorConstant) * strongNormSquared x
strictScaledBaseGapMinusErrorAbsorption
  scale qBase qError qGap strongNormSquared
  baseGapConstant errorConstant
  baseGapN2 operatorErrorN2 gapDecomposition error<base x =
  let
    scaleSq = ScaleHeadroom.CompatibilityScale.scaleSq scale
    qBaseX = qBase x
    qErrorX = qError x
    qGapX = qGap x
    normSq = strongNormSquared x

    -- The strict premise supplies the positive subtraction margin.
    margin : GapMargin
    margin = strictGapMarginFromConstants
      baseGapConstant errorConstant error<base

    eq1 :
      (baseGapConstant ∸ errorConstant) * normSq
        ≡
      baseGapConstant * normSq ∸ errorConstant * normSq
    eq1 = *-distribʳ-∸ normSq baseGapConstant errorConstant

    step2 :
      baseGapConstant * normSq ∸ errorConstant * normSq
        ≤
      scaleSq * qBaseX ∸ errorConstant * normSq
    step2 = ∸-monoˡ-≤ (errorConstant * normSq) (baseGapN2 x)

    step3 :
      scaleSq * qBaseX ∸ errorConstant * normSq
        ≤
      scaleSq * qBaseX ∸ scaleSq * qErrorX
    step3 = ∸-monoʳ-≤ (scaleSq * qBaseX) (operatorErrorN2 x)

    eq4 :
      scaleSq * qBaseX ∸ scaleSq * qErrorX
        ≡
      scaleSq * (qBaseX ∸ qErrorX)
    eq4 = sym (*-distribˡ-∸ scaleSq qBaseX qErrorX)

    eq5 :
      scaleSq * (qBaseX ∸ qErrorX)
        ≡
      scaleSq * qGapX
    eq5 = cong (λ z → scaleSq * z) (sym (gapDecomposition x))
  in
  ≤-trans (≤-reflexive eq1)
    (≤-trans step2
      (≤-trans step3
        (≤-trans (≤-reflexive eq4)
          (≤-reflexive eq5))))

strictScaledBaseGapMinusErrorAbsorptionFromWitness :
  {N : Nat} →
  {Carrier : Set} →
  (scale : ScaleHeadroom.CompatibilityScale N) →
  (bridge : ScaledOperatorErrorBridge N Carrier) →
  (qBase qGap : Carrier → Nat) →
  (baseGapConstant errorConstant : Nat) →
  ((x : Carrier) →
    baseGapConstant *
      ScaledOperatorErrorBridge.strongNormSquared bridge x
      ≤
    ScaleHeadroom.CompatibilityScale.scaleSq scale * qBase x) →
  ((x : Carrier) → qGap x ≡
    qBase x ∸ ScaledOperatorErrorBridge.qError bridge x) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    ≡
  ScaleHeadroom.CompatibilityScale.scaleSq
    (ScaledOperatorErrorBridge.compatibilityScale bridge) →
  errorConstant ≡
    ScaledOperatorErrorBridge.errorConstant bridge →
  errorConstant < baseGapConstant →
  (x : Carrier) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale * qGap x
    ≥
  (baseGapConstant ∸ errorConstant) *
    ScaledOperatorErrorBridge.strongNormSquared bridge x
strictScaledBaseGapMinusErrorAbsorptionFromWitness
  scale bridge qBase qGap baseGapConstant errorConstant
  baseGapN2 gapDecomposition scaleMatches refl error<base =
  strictScaledBaseGapMinusErrorAbsorption
    scale
    qBase
    (ScaledOperatorErrorBridge.qError bridge)
    qGap
    (ScaledOperatorErrorBridge.strongNormSquared bridge)
    baseGapConstant
    errorConstant
    baseGapN2
    (scaledOperatorErrorBridgeAtScale bridge scale scaleMatches)
    gapDecomposition
    error<base

gapAbsorptionFromMargin :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms
      operatorStrongError
      strongNormSquared) →
  GapMargin →
  gapPerturbationAbsorptionTarget
    gapQuadraticForms
    strongNormSquared
    baseGapTheorem
    operatorStrongError
    operatorErrorIdentification
gapAbsorptionFromMargin
  {gapQuadraticForms} {strongNormSquared} {operatorStrongError}
  baseGapTheorem operatorErrorIdentification gapMargin =
  proveBaseGapMinusErrorAbsorption
    gapQuadraticForms
    strongNormSquared
    (BaseGapN2Theorem.baseGapConstant baseGapTheorem)
    (OperatorErrorIdentification.errorConstant operatorErrorIdentification)
    (BaseGapN2Theorem.baseGapN2Witness baseGapTheorem)
    (OperatorErrorIdentification.operatorErrorN2Witness
      operatorErrorIdentification)
    (GapQuadraticFormsTarget.gapDecompositionWitness gapQuadraticForms)

------------------------------------------------------------------------
-- Explicit post-Schur ladder.
--
-- This record is deliberately a witness surface, not a closure gate.  It
-- keeps the scale used by the residue bridge visible while requiring every
-- analytic rung to be supplied: base coercivity, scaled operator error,
-- strict gap margin, and the resulting quadratic absorption bound.

record PostSchurQGapLadder
    (gapQuadraticForms : GapQuadraticFormsTarget)
    (strongNormSquared :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat)
    (operatorStrongError :
      GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat) : Set₁ where
  constructor mkPostSchurQGapLadder
  field
    compatibilityScale :
      ScaleHeadroom.CompatibilityScale
        (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)

    compatibilityScaleMatchesGapForms :
      ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
        ≡
      ScaleHeadroom.CompatibilityScale.scaleSq
        (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)

    baseGapTheorem :
      BaseGapN2Theorem gapQuadraticForms strongNormSquared

    operatorErrorIdentification :
      OperatorErrorIdentification
        gapQuadraticForms operatorStrongError strongNormSquared

    -- The N^-2 base-gap rung, expressed with the shared CompatibilityScale.
    baseGapN2Witness :
      baseGapN2Target
        gapQuadraticForms
        strongNormSquared
        (BaseGapN2Theorem.baseGapConstant baseGapTheorem)

    -- The N^-2 operator-error rung, expressed with the same scale.
    operatorErrorN2Witness :
      operatorErrorN2Target
        gapQuadraticForms
        strongNormSquared
        (OperatorErrorIdentification.errorConstant
          operatorErrorIdentification)

    gapMargin : GapMargin

    gapMarginPositiveWitness :
      zero < GapMargin.marginConstant gapMargin

    gapMarginMatchesBase :
      GapMargin.baseGapConstant gapMargin
        ≡ BaseGapN2Theorem.baseGapConstant baseGapTheorem

    gapMarginMatchesError :
      GapMargin.errorConstant gapMargin
        ≡ OperatorErrorIdentification.errorConstant
            operatorErrorIdentification

    -- This is the post-subtraction q-gap bound; it remains conditional on
    -- the theorem witnesses above and does not assert qGapTransferClosed.
    gapPerturbationAbsorptionWitness :
      gapPerturbationAbsorptionTarget
        gapQuadraticForms
        strongNormSquared
        baseGapTheorem
        operatorStrongError
        operatorErrorIdentification

gapMarginFromTheoremsAndStrict :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms operatorStrongError strongNormSquared) →
  OperatorErrorIdentification.errorConstant operatorErrorIdentification
    < BaseGapN2Theorem.baseGapConstant baseGapTheorem →
  GapMargin
gapMarginFromTheoremsAndStrict
  baseGapTheorem operatorErrorIdentification error<base =
  gapMarginFromTheoremsAndLeq
    baseGapTheorem
    operatorErrorIdentification
    (positiveDifferenceFromStrictLess error base error<base)
    (<⇒≤ error<base)
  where
    base : Nat
    base = BaseGapN2Theorem.baseGapConstant baseGapTheorem

    error : Nat
    error = OperatorErrorIdentification.errorConstant
      operatorErrorIdentification

postSchurQGapLadderFromStrictMargin :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (baseGapTheorem :
    BaseGapN2Theorem gapQuadraticForms strongNormSquared) →
  (operatorErrorIdentification :
    OperatorErrorIdentification
      gapQuadraticForms operatorStrongError strongNormSquared) →
  OperatorErrorIdentification.errorConstant operatorErrorIdentification
    < BaseGapN2Theorem.baseGapConstant baseGapTheorem →
  PostSchurQGapLadder
    gapQuadraticForms strongNormSquared operatorStrongError
postSchurQGapLadderFromStrictMargin
  {gapQuadraticForms} {operatorStrongError} {strongNormSquared}
  baseGapTheorem operatorErrorIdentification error<base =
  let margin =
        gapMarginFromTheoremsAndStrict
          baseGapTheorem operatorErrorIdentification error<base
  in
  mkPostSchurQGapLadder
    (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
    refl
    baseGapTheorem
    operatorErrorIdentification
    (BaseGapN2Theorem.baseGapN2Witness baseGapTheorem)
    (OperatorErrorIdentification.operatorErrorN2Witness
      operatorErrorIdentification)
    margin
    (GapMargin.marginPositive margin)
    refl
    refl
    (gapAbsorptionFromMargin
      baseGapTheorem operatorErrorIdentification margin)

------------------------------------------------------------------------
-- Generic strict q-gap / scale bridge.
--
-- The witness keeps the analytic absorption premise supplied by the caller.
-- The bridge only transports its scale square to the explicit N² form; it
-- does not construct ResidueScaleCompatibility or change any gate state.

record StrictQGapScaleAbsorption (N : Nat) (Carrier : Set) : Set₁ where
  constructor mkStrictQGapScaleAbsorption
  field
    scale : ScaleHeadroom.CompatibilityScale N
    qGap : Carrier → Nat
    gapStrongNormSquared : Carrier → Nat
    gapConstant : Nat
    gapConstantPositive : zero < gapConstant
    scaleMatchesN2 :
      ScaleHeadroom.CompatibilityScale.scaleSq scale ≡ N * N
    scaleAbsorption :
      (x : Carrier) →
      gapConstant * gapStrongNormSquared x
        ≤
      ScaleHeadroom.CompatibilityScale.scaleSq scale * qGap x

record QGapN2Control (N : Nat) (Carrier : Set) : Set₁ where
  constructor mkQGapN2Control
  field
    qGap : Carrier → Nat
    gapStrongNormSquared : Carrier → Nat
    gapConstant : Nat
    gapConstantPositive : zero < gapConstant
    qGapN2Bound :
      (x : Carrier) →
      gapConstant * gapStrongNormSquared x
        ≤
      (N * N) * qGap x

strictQGapScaleAbsorptionToQGapN2 :
  {N : Nat} →
  {Carrier : Set} →
  (witness : StrictQGapScaleAbsorption N Carrier) →
  QGapN2Control N Carrier
strictQGapScaleAbsorptionToQGapN2 witness =
  mkQGapN2Control
    (StrictQGapScaleAbsorption.qGap witness)
    (StrictQGapScaleAbsorption.gapStrongNormSquared witness)
    (StrictQGapScaleAbsorption.gapConstant witness)
    (StrictQGapScaleAbsorption.gapConstantPositive witness)
    (λ x →
      ≤-trans
        (StrictQGapScaleAbsorption.scaleAbsorption witness x)
        (≤-reflexive
          (cong
            (λ z → z * StrictQGapScaleAbsorption.qGap witness x)
            (StrictQGapScaleAbsorption.scaleMatchesN2 witness))))

postSchurQGapLadderToStrictQGapScaleAbsorption :
  {gapQuadraticForms : GapQuadraticFormsTarget} →
  {operatorStrongError :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  {strongNormSquared :
    GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  (ladder :
    PostSchurQGapLadder
      gapQuadraticForms strongNormSquared operatorStrongError) →
  (scaleMatchesN2 :
    ScaleHeadroom.CompatibilityScale.scaleSq
      (PostSchurQGapLadder.compatibilityScale ladder)
      ≡
    GapQuadraticFormsTarget.shellIndex gapQuadraticForms
      * GapQuadraticFormsTarget.shellIndex gapQuadraticForms) →
  (marginMatchesDifference :
    GapMargin.marginConstant (PostSchurQGapLadder.gapMargin ladder)
      ≡
    BaseGapN2Theorem.baseGapConstant
        (PostSchurQGapLadder.baseGapTheorem ladder)
      ∸
    OperatorErrorIdentification.errorConstant
      (PostSchurQGapLadder.operatorErrorIdentification ladder)) →
  StrictQGapScaleAbsorption
    (GapQuadraticFormsTarget.shellIndex gapQuadraticForms)
    (GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (GapQuadraticFormsTarget.shellIndex gapQuadraticForms))
postSchurQGapLadderToStrictQGapScaleAbsorption
  {gapQuadraticForms = gapQuadraticForms}
  {strongNormSquared = strongNormSquared}
  ladder
  scaleMatchesN2 marginMatchesDifference =
  let
    scaleAgreement :
      ScaleHeadroom.CompatibilityScale.scaleSq
        (GapQuadraticFormsTarget.compatibilityScale gapQuadraticForms)
        ≡
      ScaleHeadroom.CompatibilityScale.scaleSq
        (PostSchurQGapLadder.compatibilityScale ladder)
    scaleAgreement = sym
      (PostSchurQGapLadder.compatibilityScaleMatchesGapForms ladder)
  in
  mkStrictQGapScaleAbsorption
    (PostSchurQGapLadder.compatibilityScale ladder)
    (GapQuadraticFormsTarget.qGap gapQuadraticForms)
    strongNormSquared
    (GapMargin.marginConstant (PostSchurQGapLadder.gapMargin ladder))
    (PostSchurQGapLadder.gapMarginPositiveWitness ladder)
    scaleMatchesN2
    (λ x →
      ≤-trans
        (≤-trans
          (≤-reflexive
            (cong
              (λ z → z * strongNormSquared x)
              marginMatchesDifference))
          (PostSchurQGapLadder.gapPerturbationAbsorptionWitness ladder x))
        (≤-reflexive
          (cong
            (λ z → z * GapQuadraticFormsTarget.qGap gapQuadraticForms x)
            scaleAgreement)))
