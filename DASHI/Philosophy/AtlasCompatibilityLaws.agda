module DASHI.Philosophy.AtlasCompatibilityLaws where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Partial translations retain domains, asymmetric residuals, and voice.

record PartialTranslation (A B Residual Cost : Set) : Set₁ where
  field
    Domain : A → Set
    translate : (a : A) → Domain a → B
    residual : (a : A) → Domain a → Residual
    cost : (a : A) → Domain a → Cost
    voicePreserved : (a : A) → (p : Domain a) → Set

open PartialTranslation public

record ComposableTranslations
       {A B C ResidualAB ResidualBC CostAB CostBC : Set}
       (first : PartialTranslation A B ResidualAB CostAB)
       (second : PartialTranslation B C ResidualBC CostBC) : Set₁ where
  field
    source : A
    sourceInFirst : Domain first source
    intermediateInSecond : Domain second (translate first source sourceInFirst)

open ComposableTranslations public

compositeTranslate :
  ∀ {A B C ResidualAB ResidualBC CostAB CostBC : Set}
    {first : PartialTranslation A B ResidualAB CostAB}
    {second : PartialTranslation B C ResidualBC CostBC} →
  ComposableTranslations first second → C
compositeTranslate {first = first} {second = second} receipt =
  translate second
    (translate first (source receipt) (sourceInFirst receipt))
    (intermediateInSecond receipt)

record CompositeResidualReceipt
       (ResidualAB ResidualBC CostAB CostBC : Set) : Set₁ where
  field
    firstResidual : ResidualAB
    secondResidual : ResidualBC
    firstCost : CostAB
    secondCost : CostBC
    noZeroResidualClaim : Bool
    noSymmetricCostClaim : Bool

open CompositeResidualReceipt public

composeResidualReceipt :
  ∀ {A B C ResidualAB ResidualBC CostAB CostBC : Set}
    {first : PartialTranslation A B ResidualAB CostAB}
    {second : PartialTranslation B C ResidualBC CostBC} →
  (receipt : ComposableTranslations first second) →
  CompositeResidualReceipt ResidualAB ResidualBC CostAB CostBC
composeResidualReceipt {first = first} {second = second} receipt =
  record
    { firstResidual = residual first (source receipt) (sourceInFirst receipt)
    ; secondResidual = residual second
        (translate first (source receipt) (sourceInFirst receipt))
        (intermediateInSecond receipt)
    ; firstCost = cost first (source receipt) (sourceInFirst receipt)
    ; secondCost = cost second
        (translate first (source receipt) (sourceInFirst receipt))
        (intermediateInSecond receipt)
    ; noZeroResidualClaim = true
    ; noSymmetricCostClaim = true
    }

record FailedTranslation (A Reason : Set) : Set₁ where
  field
    source : A
    reason : Reason
    failureRecorded : Set
    forcedTranslation : Bool

open FailedTranslation public

failedTranslationDoesNotForcePassage :
  ∀ {A Reason : Set} (failure : FailedTranslation A Reason) →
  forcedTranslation failure ≡ false →
  forcedTranslation failure ≡ false
failedTranslationDoesNotForcePassage failure proof = proof
