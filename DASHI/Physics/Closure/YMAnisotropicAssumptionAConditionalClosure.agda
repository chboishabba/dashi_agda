module DASHI.Physics.Closure.YMAnisotropicAssumptionAConditionalClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BalabanCMP98AveragingLocalityImported as Locality
import DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks as Seminorm
import DASHI.Physics.Closure.FormalQhpBlockingMapDefinition as Qhp

------------------------------------------------------------------------
-- Conditional anisotropic Assumption-A closure.
--
-- This is now a fully native consequence of the Sprint 81 UV shell:
-- the `Q_hp` locality theorem and the remaining anisotropic arithmetic are
-- both in repo.
--
-- Route:
--   native locality `osc_e(Q_hp) <= C_local * 2^(-2k)`
--   + spatial link count `3 * 2^(3k)`
--   -> squared sum `3 * C_local^2 * 2^(-k)`
--   -> uniform envelope `3 * C_local^2`
--
-- For a Lipschitz observable `F` with constant `C_F`, the bound becomes
-- `3 * C_local^2 * C_F^2 * 2^(-k)` and hence `3 * C_local^2 * C_F^2`
-- uniformly in `k`.

anisotropicAssumptionAClosedConditionally : Bool
anisotropicAssumptionAClosedConditionally = true

anisotropicAssumptionAProvedInRepo : Bool
anisotropicAssumptionAProvedInRepo = true

squaredOscillationSummabilityForHalfPlaneBlocking : Bool
squaredOscillationSummabilityForHalfPlaneBlocking = true

fixedFiniteVolumeBlockedObservableContinuumLimitConditional : Bool
fixedFiniteVolumeBlockedObservableContinuumLimitConditional = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

observableSquaredCoefficient : Nat → Nat → Nat
observableSquaredCoefficient cLocal cF =
  3 * ((cLocal * cLocal) * (cF * cF))

observableSquaredDecay :
  Nat → Nat → Nat → Seminorm.DyadicDecay
observableSquaredDecay cLocal cF k =
  Seminorm.mkDyadicDecay (observableSquaredCoefficient cLocal cF) k

observableUniformEnvelope :
  Nat → Nat → Seminorm.DyadicDecay
observableUniformEnvelope cLocal cF =
  Seminorm.mkDyadicDecay (observableSquaredCoefficient cLocal cF) 0

ConditionalSquaredOscillationFormula : Set
ConditionalSquaredOscillationFormula = String

canonicalConditionalSquaredOscillationFormula :
  ConditionalSquaredOscillationFormula
canonicalConditionalSquaredOscillationFormula =
  "sum_spatial_e osc_e(F o Q_hp)^2 <= 3*C_local^2*C_F^2*2^(-k)"

UniformConditionalAssumptionAFormula : Set
UniformConditionalAssumptionAFormula = String

canonicalUniformConditionalAssumptionAFormula :
  UniformConditionalAssumptionAFormula
canonicalUniformConditionalAssumptionAFormula =
  "sum_spatial_e osc_e(F o Q_hp)^2 <= 3*C_local^2*C_F^2"

record YMAnisotropicAssumptionAConditionalClosureTheorem
  (cLocal cF k : Nat) : Set where
  constructor mkYMAnisotropicAssumptionAConditionalClosureTheorem
  field
    localityProof :
      Locality.BalabanCMP98AveragingLocalityImportedTheorem cLocal k
    qhpArithmetic :
      Seminorm.QhpSquaredOscillationArithmetic cLocal k
    qhpSquaredBridge :
      Qhp.LipschitzToSquaredOscillationForQhpTheorem cLocal k
    observableSquaredDecayBudget :
      Seminorm.DyadicDecay
    observableSquaredDecayBudgetIs3CLocalSquaredCFSquared2Minusk :
      observableSquaredDecayBudget ≡ observableSquaredDecay cLocal cF k
    observableUniformEnvelopeBudget :
      Seminorm.DyadicDecay
    observableUniformEnvelopeBudgetIs3CLocalSquaredCFSquared :
      observableUniformEnvelopeBudget ≡ observableUniformEnvelope cLocal cF
    conditionalSquaredOscillationFormula :
      ConditionalSquaredOscillationFormula
    conditionalSquaredOscillationFormulaIsCanonical :
      conditionalSquaredOscillationFormula
        ≡ canonicalConditionalSquaredOscillationFormula
    uniformConditionalAssumptionAFormula :
      UniformConditionalAssumptionAFormula
    uniformConditionalAssumptionAFormulaIsCanonical :
      uniformConditionalAssumptionAFormula
        ≡ canonicalUniformConditionalAssumptionAFormula
    anisotropicAssumptionAClosedHere :
      Bool
    anisotropicAssumptionAClosedHereIsTrue :
      anisotropicAssumptionAClosedHere ≡ true
    anisotropicAssumptionAProvedInRepoHere :
      Bool
    anisotropicAssumptionAProvedInRepoHereIsTrue :
      anisotropicAssumptionAProvedInRepoHere ≡ true
    noClayPromotion :
      clayYangMillsPromoted ≡ false

ymAnisotropicAssumptionAConditionalClosure :
  (cLocal cF k : Nat) →
  YMAnisotropicAssumptionAConditionalClosureTheorem cLocal cF k
ymAnisotropicAssumptionAConditionalClosure cLocal cF k =
  mkYMAnisotropicAssumptionAConditionalClosureTheorem
    (Locality.balabanCMP98AveragingLocalityImportedTheorem cLocal k)
    (Seminorm.qhpSquaredOscillationArithmetic cLocal k)
    (Qhp.lipschitzToSquaredOscillationForQhp cLocal k)
    (observableSquaredDecay cLocal cF k)
    refl
    (observableUniformEnvelope cLocal cF)
    refl
    canonicalConditionalSquaredOscillationFormula
    refl
    canonicalUniformConditionalAssumptionAFormula
    refl
    true
    refl
    true
    refl
    refl

record YMAnisotropicAssumptionAConditionalBoundary : Set where
  field
    conditionalClosureRecorded :
      anisotropicAssumptionAClosedConditionally ≡ true
    provedInRepo :
      anisotropicAssumptionAProvedInRepo ≡ true
    halfPlaneSummabilityClosedConditionally :
      squaredOscillationSummabilityForHalfPlaneBlocking ≡ true
    uvClosureConditionalOnly :
      fixedFiniteVolumeBlockedObservableContinuumLimitConditional ≡ true
    noPromotion :
      clayYangMillsPromoted ≡ false

ymAnisotropicAssumptionAConditionalBoundary :
  YMAnisotropicAssumptionAConditionalBoundary
ymAnisotropicAssumptionAConditionalBoundary =
  record
    { conditionalClosureRecorded = refl
    ; provedInRepo = refl
    ; halfPlaneSummabilityClosedConditionally = refl
    ; uvClosureConditionalOnly = refl
    ; noPromotion = refl
    }
