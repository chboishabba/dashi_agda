module DASHI.Physics.Closure.NSPeriodicCompactGammaPDEBalance where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicCompactGammaPotentialDerivativeExact as Potential
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact substitution seam between the differentiated potential and the PDE.
--
-- Each of the three reserve derivatives must be expanded from the Galerkin
-- equation into
--
--   reserve derivative + loss = supply.
--
-- This module performs the nontrivial commutative-additive reassociation and
-- proves that the literal derivative of the selected compact-Gamma potential
-- satisfies one combined balance.  Consequently a downstream expenditure
-- theorem cannot combine unrelated packet, Gamma and off-packet identities.
------------------------------------------------------------------------

record CommutativeAdditiveLaws
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    addAssociative : ∀ a b c →
      Calculus._+_ A (Calculus._+_ A a b) c
      ≡ Calculus._+_ A a (Calculus._+_ A b c)

    addCommutative : ∀ a b →
      Calculus._+_ A a b ≡ Calculus._+_ A b a

open CommutativeAdditiveLaws public

swapMiddle :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (L : CommutativeAdditiveLaws Time Scalar A) →
  ∀ a b c d →
  Calculus._+_ A (Calculus._+_ A a b) (Calculus._+_ A c d)
  ≡
  Calculus._+_ A (Calculus._+_ A a c) (Calculus._+_ A b d)
swapMiddle {A = A} L a b c d =
  trans
    (addAssociative L a b (Calculus._+_ A c d))
    (trans
      (cong
        (Calculus._+_ A a)
        (sym (addAssociative L b c d)))
      (trans
        (cong
          (λ middle → Calculus._+_ A a
            (Calculus._+_ A middle d))
          (addCommutative L b c))
        (trans
          (cong
            (Calculus._+_ A a)
            (addAssociative L c b d))
          (sym
            (addAssociative L a c
              (Calculus._+_ A b d))))))

record CompactGammaPDEComponentBalances
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    additiveLaws : CommutativeAdditiveLaws Time Scalar A

    potentialInputs :
      Potential.CompactGammaPotentialDerivativeInputs Time Scalar A

    packetLoss gammaLoss ratioLoss : Time → Scalar
    packetSupply gammaSupply ratioSupply : Time → Scalar

    packetPDEBalance : ∀ τ →
      Calculus._+_ A
        (Potential.packetReserveDerivativeFormula potentialInputs τ)
        (packetLoss τ)
      ≡ packetSupply τ

    gammaPDEBalance : ∀ τ →
      Calculus._+_ A
        (Potential.gammaReserveDerivativeFormula potentialInputs τ)
        (gammaLoss τ)
      ≡ gammaSupply τ

    ratioPDEBalance : ∀ τ →
      Calculus._+_ A
        (Potential.ratioReserveDerivativeFormula potentialInputs τ)
        (ratioLoss τ)
      ≡ ratioSupply τ

open CompactGammaPDEComponentBalances public

combinedPotentialLoss combinedPotentialSupply :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPDEComponentBalances Time Scalar A → Time → Scalar
combinedPotentialLoss {A = A} P τ =
  Calculus._+_ A
    (packetLoss P τ)
    (Calculus._+_ A (gammaLoss P τ) (ratioLoss P τ))
combinedPotentialSupply {A = A} P τ =
  Calculus._+_ A
    (packetSupply P τ)
    (Calculus._+_ A (gammaSupply P τ) (ratioSupply P τ))

componentBalancesCombine :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPDEComponentBalances Time Scalar A) →
  ∀ τ →
  Calculus._+_ A
    (Potential.compactGammaPotentialDerivativeFormula
      (potentialInputs P) τ)
    (combinedPotentialLoss P τ)
  ≡ combinedPotentialSupply P τ
componentBalancesCombine {A = A} P τ =
  trans
    firstInterleave
    (trans
      secondInterleave
      (cong₂Balances
        (packetPDEBalance P τ)
        (gammaPDEBalance P τ)
        (ratioPDEBalance P τ)))
  where
  L = additiveLaws P

  packetDerivative =
    Potential.packetReserveDerivativeFormula (potentialInputs P) τ
  gammaDerivative =
    Potential.gammaReserveDerivativeFormula (potentialInputs P) τ
  ratioDerivative =
    Potential.ratioReserveDerivativeFormula (potentialInputs P) τ

  firstInterleave :
    Calculus._+_ A
      (Calculus._+_ A packetDerivative
        (Calculus._+_ A gammaDerivative ratioDerivative))
      (Calculus._+_ A (packetLoss P τ)
        (Calculus._+_ A (gammaLoss P τ) (ratioLoss P τ)))
    ≡
    Calculus._+_ A
      (Calculus._+_ A packetDerivative (packetLoss P τ))
      (Calculus._+_ A
        (Calculus._+_ A gammaDerivative ratioDerivative)
        (Calculus._+_ A (gammaLoss P τ) (ratioLoss P τ)))
  firstInterleave =
    swapMiddle L
      packetDerivative
      (Calculus._+_ A gammaDerivative ratioDerivative)
      (packetLoss P τ)
      (Calculus._+_ A (gammaLoss P τ) (ratioLoss P τ))

  secondInterleave :
    Calculus._+_ A
      (Calculus._+_ A packetDerivative (packetLoss P τ))
      (Calculus._+_ A
        (Calculus._+_ A gammaDerivative ratioDerivative)
        (Calculus._+_ A (gammaLoss P τ) (ratioLoss P τ)))
    ≡
    Calculus._+_ A
      (Calculus._+_ A packetDerivative (packetLoss P τ))
      (Calculus._+_ A
        (Calculus._+_ A gammaDerivative (gammaLoss P τ))
        (Calculus._+_ A ratioDerivative (ratioLoss P τ)))
  secondInterleave =
    cong
      (Calculus._+_ A
        (Calculus._+_ A packetDerivative (packetLoss P τ)))
      (swapMiddle L
        gammaDerivative ratioDerivative
        (gammaLoss P τ) (ratioLoss P τ))

  cong₂Balances :
    Calculus._+_ A packetDerivative (packetLoss P τ)
      ≡ packetSupply P τ →
    Calculus._+_ A gammaDerivative (gammaLoss P τ)
      ≡ gammaSupply P τ →
    Calculus._+_ A ratioDerivative (ratioLoss P τ)
      ≡ ratioSupply P τ →
    Calculus._+_ A
      (Calculus._+_ A packetDerivative (packetLoss P τ))
      (Calculus._+_ A
        (Calculus._+_ A gammaDerivative (gammaLoss P τ))
        (Calculus._+_ A ratioDerivative (ratioLoss P τ)))
    ≡ combinedPotentialSupply P τ
  cong₂Balances refl refl refl = refl

literalPotentialDerivativePDEBalance :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPDEComponentBalances Time Scalar A) →
  ∀ τ →
  Calculus._+_ A
    (Calculus.derivative A
      (Potential.compactGammaPotential (potentialInputs P)) τ)
    (combinedPotentialLoss P τ)
  ≡ combinedPotentialSupply P τ
literalPotentialDerivativePDEBalance {A = A} P τ =
  trans
    (cong
      (λ derivativeValue →
        Calculus._+_ A derivativeValue (combinedPotentialLoss P τ))
      (Potential.compactGammaPotentialDerivativeExact
        (potentialInputs P) τ))
    (componentBalancesCombine P τ)

------------------------------------------------------------------------
-- The combined supply/loss can now be identified with the viscosity, forcing,
-- near/far and switch terms used by the strict-margin expenditure adapter.
------------------------------------------------------------------------

record CompactGammaPDEBudgetIdentification
    {Time Scalar : Set}
    {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    (P : CompactGammaPDEComponentBalances Time Scalar A) : Set₁ where
  field
    coerciveEnvelopeRate forcingRate nonlinearLoss : Time → Scalar

    supplyMeaning : ∀ τ →
      combinedPotentialSupply P τ
      ≡ Calculus._+_ A (coerciveEnvelopeRate τ) (forcingRate τ)

    lossMeaning : ∀ τ →
      combinedPotentialLoss P τ ≡ nonlinearLoss τ

open CompactGammaPDEBudgetIdentification public

identifiedPotentialPDEBalance :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPDEComponentBalances Time Scalar A) →
  (B : CompactGammaPDEBudgetIdentification P) →
  ∀ τ →
  Calculus._+_ A
    (Calculus.derivative A
      (Potential.compactGammaPotential (potentialInputs P)) τ)
    (nonlinearLoss B τ)
  ≡ Calculus._+_ A (coerciveEnvelopeRate B τ) (forcingRate B τ)
identifiedPotentialPDEBalance {A = A} P B τ =
  trans
    (cong
      (Calculus._+_ A
        (Calculus.derivative A
          (Potential.compactGammaPotential (potentialInputs P)) τ))
      (sym (lossMeaning B τ)))
    (trans
      (literalPotentialDerivativePDEBalance P τ)
      (supplyMeaning B τ))

------------------------------------------------------------------------
-- Status: the Galerkin substitution is reduced to three literal component PDE
-- balances.  The remaining analytic leaf is to prove their supply/loss formulas
-- and then fit the combined nonlinear loss into the 1/4+1/8+1/8 budget.
------------------------------------------------------------------------

compactGammaPDEBalanceLevel : ProofLevel
compactGammaPDEBalanceLevel = machineChecked
