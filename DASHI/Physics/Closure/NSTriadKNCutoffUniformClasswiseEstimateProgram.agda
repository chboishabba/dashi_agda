module DASHI.Physics.Closure.NSTriadKNCutoffUniformClasswiseEstimateProgram where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as Nat

------------------------------------------------------------------------
-- Uniformity ledger.
------------------------------------------------------------------------

data PermittedConstantDependency : Set where
  fixedViscosity fixedShellOverlap fixedNormConvention :
    PermittedConstantDependency

record UniformConstant : Set₁ where
  constructor uniform-constant
  field
    value : Nat
    independentOfCutoff : Set
    independentOfTime : Set
    independentOfSolution : Set
    independentOfTriad : Set
    independentOfShellLocation : Set
    independentOfFiberSize : Set

open UniformConstant public

------------------------------------------------------------------------
-- Cancellation-preserving classwise quadratic estimates.
------------------------------------------------------------------------

record ClasswiseQuadraticForms {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    scaleSquare : Cutoff → Nat
    strongNormSquared : Cutoff → State → Nat

    qForcedTail qTransition qAdversarial qResidual :
      Cutoff → State → Nat

open ClasswiseQuadraticForms public

qError :
  ∀ {c s} → ClasswiseQuadraticForms {c} {s} →
  Cutoff _ → State _ → Nat
qError forms N state =
  qForcedTail forms N state
  + qTransition forms N state
  + qAdversarial forms N state
  + qResidual forms N state

record DirectUniformClasswiseBounds
    {c s : Level}
    (forms : ClasswiseQuadraticForms {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    forcedTailConstant transitionConstant adversarialConstant residualConstant :
      UniformConstant

    forcedTailBound : ∀ N state →
      scaleSquare forms N * qForcedTail forms N state
      ≤ value forcedTailConstant * strongNormSquared forms N state

    transitionBound : ∀ N state →
      scaleSquare forms N * qTransition forms N state
      ≤ value transitionConstant * strongNormSquared forms N state

    adversarialBound : ∀ N state →
      scaleSquare forms N * qAdversarial forms N state
      ≤ value adversarialConstant * strongNormSquared forms N state

    residualBound : ∀ N state →
      scaleSquare forms N * qResidual forms N state
      ≤ value residualConstant * strongNormSquared forms N state

open DirectUniformClasswiseBounds public

totalClassConstant :
  ∀ {c s} {forms : ClasswiseQuadraticForms {c} {s}} →
  DirectUniformClasswiseBounds forms → Nat
totalClassConstant bounds =
  value (forcedTailConstant bounds)
  + value (transitionConstant bounds)
  + value (adversarialConstant bounds)
  + value (residualConstant bounds)

record TotalClasswiseErrorBound
    {c s : Level}
    (forms : ClasswiseQuadraticForms {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    bounds : DirectUniformClasswiseBounds forms

    totalBound : ∀ N state →
      scaleSquare forms N * qError forms N state
      ≤ totalClassConstant bounds * strongNormSquared forms N state

open TotalClasswiseErrorBound public

------------------------------------------------------------------------
-- Residual domination is a theorem with literal coefficients, not a Boolean.
------------------------------------------------------------------------

record ResidualDomination
    {c s : Level}
    (forms : ClasswiseQuadraticForms {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    alphaForcedTail alphaTransition alphaAdversarial : Nat

    residualControlled : ∀ N state →
      qResidual forms N state
      ≤ alphaForcedTail * qForcedTail forms N state
        + alphaTransition * qTransition forms N state
        + alphaAdversarial * qAdversarial forms N state

open ResidualDomination public

------------------------------------------------------------------------
-- Two admissible routes: absolute majorisation or signed cancellation.
------------------------------------------------------------------------

data EstimateStrategy : Set where
  positiveMajorant signedBlockCancellation modifiedEnergy : EstimateStrategy

record ClasswisePromotionCertificate
    {c s : Level}
    (forms : ClasswiseQuadraticForms {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    strategy : EstimateStrategy
    exactSignedPhysicalOperatorUsed : Set
    everyPhysicalInteractionCovered : Set
    noPostulatedCoefficientUsed : Set
    noCutoffDependentConstantUsed : Set

    totalError : TotalClasswiseErrorBound forms

open ClasswisePromotionCertificate public

record StrictClasswiseComparison
    {c s : Level}
    {forms : ClasswiseQuadraticForms {c} {s}}
    (promotion : ClasswisePromotionCertificate forms) : Set where
  field
    baseConstant : Nat
    strictComparison :
      totalClassConstant (bounds (totalError promotion)) < baseConstant

open StrictClasswiseComparison public

uniformityLedgerImplemented : Bool
uniformityLedgerImplemented = true

uniformityLedgerImplementedIsTrue : uniformityLedgerImplemented ≡ true
uniformityLedgerImplementedIsTrue = refl

cancellationPreservingClasswiseTargetImplemented : Bool
cancellationPreservingClasswiseTargetImplemented = true

cancellationPreservingClasswiseTargetImplementedIsTrue :
  cancellationPreservingClasswiseTargetImplemented ≡ true
cancellationPreservingClasswiseTargetImplementedIsTrue = refl

concreteCutoffUniformClassConstantsClosed : Bool
concreteCutoffUniformClassConstantsClosed = false

concreteCutoffUniformClassConstantsClosedIsFalse :
  concreteCutoffUniformClassConstantsClosed ≡ false
concreteCutoffUniformClassConstantsClosedIsFalse = refl
