module DASHI.Physics.Closure.NSCompactGammaBKMTimeIntegrability where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Compact-Gamma time integrability and the BKM link.
--
-- This module deliberately separates the five analytic leaves needed by the
-- continuation argument.  Finite envelope expenditure is an output of the
-- energy/dissipation and compact-Gamma inequalities; it is not accepted as an
-- independent hypothesis.  The no-circularity field rules out deriving any
-- leaf from a high-Sobolev persistence statement whose proof already uses BKM.
--
-- The intended numerical meaning of `bernsteinWeight j` is 2^(5j/2):
--
--   || Delta_j omega ||_infinity
--     <= C_B 2^(5j/2) || Delta_j u ||_2.
--
-- Concrete analytic developments instantiate the abstract evidence types with
-- inequalities in their chosen real/integration library.

record CompactGammaBKMData
  {ls lt le lc lv : Level} :
  Set (lsuc (ls ⊔ lt ⊔ le ⊔ lc ⊔ lv)) where

  field
    State : Set ls
    Time : Set lt
    Continuation : Set lc
    Value : Set lv

    path : Time → State

    _≤ᵥ_ : Value → Value → Set le
    one : Value
    add : Value → Value → Value
    scale : Value → Value → Value
    bernsteinConstant : Value
    bernsteinWeight : Nat → Value

    shellVelocityL2 : Nat → State → Value
    shellVorticityLInfinity : Nat → State → Value
    shellVorticitySum : State → Value
    compactGammaEnvelope : State → Value
    vorticityLInfinity : State → Value

    timeIntegral : (Time → Value) → Value
    expenditureBudget : Value

    -- Primitive non-circular inputs.
    EnergyDissipationControl : Set le
    CompactGammaInequalities : Set le
    NoBKMSobolevBootstrap : Set le

    energyDissipationControl : EnergyDissipationControl
    compactGammaInequalities : CompactGammaInequalities
    noBKMSobolevBootstrap : NoBKMSobolevBootstrap

    -- 1. Bernstein on every shell.
    BernsteinShellEstimate : Set le
    bernsteinShellEstimate : BernsteinShellEstimate
    bernsteinMeaning :
      (j : Nat) (t : Time) →
      shellVorticityLInfinity j (path t)
        ≤ᵥ scale bernsteinConstant
             (scale (bernsteinWeight j) (shellVelocityL2 j (path t)))

    -- 2. Compact-Gamma decay is strong enough to sum the weighted shells.
    WeightedShellSummation : Set le
    weightedShellSummation : WeightedShellSummation
    shellSumMeaning :
      (t : Time) →
      shellVorticitySum (path t)
        ≤ᵥ compactGammaEnvelope (path t)

    -- 3. Full vorticity is controlled by C(1 + G_Gamma); the concrete
    --    instantiation may absorb C into its chosen envelope.
    CompactGammaToVorticity : Set le
    compactGammaToVorticity : CompactGammaToVorticity
    vorticityDominationMeaning :
      (t : Time) →
      vorticityLInfinity (path t)
        ≤ᵥ add one (compactGammaEnvelope (path t))

    -- 4. Expenditure is DERIVED, not supplied.  Only energy/dissipation,
    --    compact-Gamma inequalities, shell estimates, and the explicit
    --    no-BKM certificate may enter this derivation.
    FiniteEnvelopeExpenditure : Set le
    deriveFiniteEnvelopeExpenditure :
      EnergyDissipationControl →
      CompactGammaInequalities →
      BernsteinShellEstimate →
      WeightedShellSummation →
      NoBKMSobolevBootstrap →
      FiniteEnvelopeExpenditure

    envelopeExpenditureMeaning :
      FiniteEnvelopeExpenditure →
      timeIntegral (λ t → compactGammaEnvelope (path t))
        ≤ᵥ expenditureBudget

    -- 5. Integrating pointwise domination gives the BKM integral.
    FiniteVorticityIntegral : Set le
    integrateVorticityDomination :
      CompactGammaToVorticity →
      FiniteEnvelopeExpenditure →
      FiniteVorticityIntegral

    vorticityIntegralMeaning :
      FiniteVorticityIntegral →
      timeIntegral (λ t → vorticityLInfinity (path t))
        ≤ᵥ add (timeIntegral (λ _ → one)) expenditureBudget

    -- The established BKM continuation theorem is consumed only here.
    invokeBKMContinuation : FiniteVorticityIntegral → Continuation

open CompactGammaBKMData public

finiteEnvelopeExpenditure :
  ∀ {ls lt le lc lv : Level}
    (D : CompactGammaBKMData {ls} {lt} {le} {lc} {lv}) →
  FiniteEnvelopeExpenditure D
finiteEnvelopeExpenditure D =
  deriveFiniteEnvelopeExpenditure D
    (energyDissipationControl D)
    (compactGammaInequalities D)
    (bernsteinShellEstimate D)
    (weightedShellSummation D)
    (noBKMSobolevBootstrap D)

finiteVorticityIntegral :
  ∀ {ls lt le lc lv : Level}
    (D : CompactGammaBKMData {ls} {lt} {le} {lc} {lv}) →
  FiniteVorticityIntegral D
finiteVorticityIntegral D =
  integrateVorticityDomination D
    (compactGammaToVorticity D)
    (finiteEnvelopeExpenditure D)

compactGammaBKMContinuation :
  ∀ {ls lt le lc lv : Level}
    (D : CompactGammaBKMData {ls} {lt} {le} {lc} {lv}) →
  Continuation D
compactGammaBKMContinuation D =
  invokeBKMContinuation D (finiteVorticityIntegral D)

------------------------------------------------------------------------
-- Proof-relevant dependency audit.  BKM is intentionally absent from every
-- field used to construct envelope expenditure and vorticity integrability.

data CompactGammaBKMStage : Set where
  energyAndDissipation : CompactGammaBKMStage
  compactGammaDecay : CompactGammaBKMStage
  bernsteinShells : CompactGammaBKMStage
  weightedShellSum : CompactGammaBKMStage
  envelopeExpenditure : CompactGammaBKMStage
  vorticityIntegral : CompactGammaBKMStage
  bkmContinuation : CompactGammaBKMStage

record CompactGammaBKMDependencyAudit : Set where
  constructor mkCompactGammaBKMDependencyAudit
  field
    expenditureEnergyStage : CompactGammaBKMStage
    expenditureEnergyStageIsCanonical :
      expenditureEnergyStage ≡ energyAndDissipation
    expenditureGammaStage : CompactGammaBKMStage
    expenditureGammaStageIsCanonical :
      expenditureGammaStage ≡ compactGammaDecay
    expenditureBernsteinStage : CompactGammaBKMStage
    expenditureBernsteinStageIsCanonical :
      expenditureBernsteinStage ≡ bernsteinShells
    expenditureShellSumStage : CompactGammaBKMStage
    expenditureShellSumStageIsCanonical :
      expenditureShellSumStage ≡ weightedShellSum
    integralStage : CompactGammaBKMStage
    integralStageIsCanonical : integralStage ≡ vorticityIntegral
    finalStage : CompactGammaBKMStage
    finalStageIsCanonical : finalStage ≡ bkmContinuation

canonicalCompactGammaBKMDependencyAudit : CompactGammaBKMDependencyAudit
canonicalCompactGammaBKMDependencyAudit =
  mkCompactGammaBKMDependencyAudit
    energyAndDissipation refl
    compactGammaDecay refl
    bernsteinShells refl
    weightedShellSum refl
    vorticityIntegral refl
    bkmContinuation refl
