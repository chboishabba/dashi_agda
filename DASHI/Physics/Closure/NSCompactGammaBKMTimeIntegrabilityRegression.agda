module DASHI.Physics.Closure.NSCompactGammaBKMTimeIntegrabilityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit.Polymorphic using (⊤; tt)

open import DASHI.Physics.Closure.NSCompactGammaBKMTimeIntegrability

-- A minimal proof-carrying model checks that expenditure is constructed before
-- the vorticity integral and that BKM is invoked only at the final stage.

unitData : CompactGammaBKMData
unitData =
  record
    { State = ⊤
    ; Time = ⊤
    ; Continuation = ⊤
    ; Value = ⊤
    ; path = λ _ → tt
    ; _≤ᵥ_ = λ _ _ → ⊤
    ; one = tt
    ; add = λ _ _ → tt
    ; scale = λ _ _ → tt
    ; bernsteinConstant = tt
    ; bernsteinWeight = λ _ → tt
    ; shellVelocityL2 = λ _ _ → tt
    ; shellVorticityLInfinity = λ _ _ → tt
    ; shellVorticitySum = λ _ → tt
    ; compactGammaEnvelope = λ _ → tt
    ; vorticityLInfinity = λ _ → tt
    ; timeIntegral = λ _ → tt
    ; expenditureBudget = tt
    ; EnergyDissipationControl = ⊤
    ; CompactGammaInequalities = ⊤
    ; NoBKMSobolevBootstrap = ⊤
    ; energyDissipationControl = tt
    ; compactGammaInequalities = tt
    ; noBKMSobolevBootstrap = tt
    ; BernsteinShellEstimate = ⊤
    ; bernsteinShellEstimate = tt
    ; bernsteinMeaning = λ _ _ → tt
    ; WeightedShellSummation = ⊤
    ; weightedShellSummation = tt
    ; shellSumMeaning = λ _ → tt
    ; CompactGammaToVorticity = ⊤
    ; compactGammaToVorticity = tt
    ; vorticityDominationMeaning = λ _ → tt
    ; FiniteEnvelopeExpenditure = ⊤
    ; deriveFiniteEnvelopeExpenditure = λ _ _ _ _ _ → tt
    ; envelopeExpenditureMeaning = λ _ → tt
    ; FiniteVorticityIntegral = ⊤
    ; integrateVorticityDomination = λ _ _ → tt
    ; vorticityIntegralMeaning = λ _ → tt
    ; invokeBKMContinuation = λ _ → tt
    }

unitExpenditure : FiniteEnvelopeExpenditure unitData
unitExpenditure = finiteEnvelopeExpenditure unitData

unitVorticityIntegral : FiniteVorticityIntegral unitData
unitVorticityIntegral = finiteVorticityIntegral unitData

unitContinuation : Continuation unitData
unitContinuation = compactGammaBKMContinuation unitData

unitContinuationIsCanonical : unitContinuation ≡ tt
unitContinuationIsCanonical = refl
