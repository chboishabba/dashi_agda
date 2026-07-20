module DASHI.Physics.Closure.NSCompactGammaBernsteinWeightedExpenditure where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Bernstein-weighted compact-Gamma expenditure, with BKM only at the
-- endpoint.
--
-- This owner expands the previously compressed BKM bridge into the exact
-- B1--B8 dependency chain.  The analytic carrier remains parametric in the
-- real/norm/integration library, but every theorem exposes its admissible
-- inputs.  In particular, no high-Sobolev persistence or pre-existing BKM
-- integral can enter B4--B7.
------------------------------------------------------------------------

record BernsteinExpenditureData
  {ls lt lv le lc : Level} :
  Set (lsuc (ls ⊔ lt ⊔ lv ⊔ le ⊔ lc)) where

  field
    State : Set ls
    Time : Set lt
    Value : Set lv
    Continuation : Set lc

    path : Time → State
    _≤ᵥ_ : Value → Value → Set le
    ≤ᵥ-trans : {a b c : Value} → a ≤ᵥ b → b ≤ᵥ c → a ≤ᵥ c

    zero one : Value
    add multiply : Value → Value → Value
    timeScale : Value

    shellVelocityL2 : Nat → State → Value
    shellVorticityL2 : Nat → State → Value
    shellVorticityLInfinity : Nat → State → Value
    weightedVelocityShell : Nat → State → Value
    weightedShellSum : State → Value
    vorticityLInfinity : State → Value

    bernsteinL2ToLInfinityWeight : Nat → Value
    curlDerivativeWeight : Nat → Value
    bernsteinWeightFiveHalves : Nat → Value
    bernsteinConstant : Value

    compactGammaEnvelope : State → Value
    coefficient : Nat → Value
    coefficientSumBound : Value

    dissipation : Time → Value
    viscosity : Value
    initialEnergy : Value

    potential : Time → Value
    potentialInitial : Value
    potentialLowerBound : Value
    expenditureCoercivity : Value
    expenditureConstant : Value
    dissipationConstant : Value
    expenditureBudget : Value

    timeIntegral : (Time → Value) → Value

    -- The invariant-region theorem is an explicit input to the decay and
    -- differential estimates.  It is kept distinct from any regularity or
    -- continuation conclusion.
    InvariantRegion : Set le
    invariantRegion : InvariantRegion

    EnergyDissipationControl : Set le
    energyDissipationControl : EnergyDissipationControl

    CompactGammaPacketEstimates : Set le
    compactGammaPacketEstimates : CompactGammaPacketEstimates

    -- Negative dependency witnesses.  Concrete instantiations use these to
    -- certify that B4 does not consume a Sobolev supremum, a vorticity
    -- integral, BKM continuation, or a theorem whose proof used BKM.
    NoHighSobolevPersistenceInput : Set le
    NoPreexistingVorticityIntegralInput : Set le
    NoBKMContinuationInput : Set le
    NoBKMDerivedInput : Set le

    noHighSobolevPersistenceInput : NoHighSobolevPersistenceInput
    noPreexistingVorticityIntegralInput : NoPreexistingVorticityIntegralInput
    noBKMContinuationInput : NoBKMContinuationInput
    noBKMDerivedInput : NoBKMDerivedInput

    --------------------------------------------------------------------
    -- B1: shell vorticity Bernstein estimate.

    shellBernsteinL2ToLInfinity :
      (j : Nat) (t : Time) →
      shellVorticityLInfinity j (path t)
        ≤ᵥ multiply bernsteinConstant
             (multiply (bernsteinL2ToLInfinityWeight j)
               (shellVorticityL2 j (path t)))

    shellCurlL2Estimate :
      (j : Nat) (t : Time) →
      multiply bernsteinConstant
        (multiply (bernsteinL2ToLInfinityWeight j)
          (shellVorticityL2 j (path t)))
        ≤ᵥ weightedVelocityShell j (path t)

    weightedVelocityShellMeaning :
      (j : Nat) (state : State) →
      weightedVelocityShell j state ≡
        multiply bernsteinConstant
          (multiply (bernsteinWeightFiveHalves j)
            (shellVelocityL2 j state))

    --------------------------------------------------------------------
    -- B2: reconstruction and shell summation.

    vorticityReconstruction :
      (t : Time) →
      vorticityLInfinity (path t) ≤ᵥ weightedShellSum (path t)

    --------------------------------------------------------------------
    -- B3: compact-Gamma weighted shell decay and summability.

    admissibleWeightedShellDecay :
      InvariantRegion → CompactGammaPacketEstimates →
      (j : Nat) (t : Time) →
      weightedVelocityShell j (path t)
        ≤ᵥ multiply (coefficient j) (compactGammaEnvelope (path t))

    SummableCoefficientFamily : Set le
    summableCoefficientFamily : SummableCoefficientFamily

    deriveWeightedShellSummation :
      InvariantRegion →
      CompactGammaPacketEstimates →
      SummableCoefficientFamily →
      (t : Time) →
      weightedShellSum (path t)
        ≤ᵥ multiply coefficientSumBound
             (compactGammaEnvelope (path t))

    --------------------------------------------------------------------
    -- B4: non-circular expenditure differential inequality.

    ExpenditureDifferentialInequality : Set le
    deriveExpenditureDifferentialInequality :
      InvariantRegion →
      EnergyDissipationControl →
      CompactGammaPacketEstimates →
      NoHighSobolevPersistenceInput →
      NoPreexistingVorticityIntegralInput →
      NoBKMContinuationInput →
      NoBKMDerivedInput →
      ExpenditureDifferentialInequality

    expenditureDifferentialMeaning :
      ExpenditureDifferentialInequality → Set le

    --------------------------------------------------------------------
    -- B5: integrate B4 and the energy inequality.

    FiniteEnvelopeExpenditure : Set le
    integrateExpenditureInequality :
      EnergyDissipationControl →
      ExpenditureDifferentialInequality →
      FiniteEnvelopeExpenditure

    envelopeExpenditureMeaning :
      FiniteEnvelopeExpenditure →
      timeIntegral (λ t → compactGammaEnvelope (path t))
        ≤ᵥ expenditureBudget

    energyBudgetMeaning :
      EnergyDissipationControl → Set le

    --------------------------------------------------------------------
    -- B6: finite Bernstein-weighted shell expenditure.

    FiniteWeightedShellExpenditure : Set le
    integrateWeightedShellDomination :
      ((t : Time) →
        weightedShellSum (path t)
          ≤ᵥ multiply coefficientSumBound
               (compactGammaEnvelope (path t))) →
      FiniteEnvelopeExpenditure →
      FiniteWeightedShellExpenditure

    weightedShellExpenditureMeaning :
      FiniteWeightedShellExpenditure → Set le

    --------------------------------------------------------------------
    -- B7: finite vorticity integral.

    FiniteVorticityIntegral : Set le
    integrateVorticityReconstruction :
      ((t : Time) →
        vorticityLInfinity (path t) ≤ᵥ weightedShellSum (path t)) →
      FiniteWeightedShellExpenditure →
      FiniteVorticityIntegral

    vorticityIntegralMeaning :
      FiniteVorticityIntegral → Set le

    --------------------------------------------------------------------
    -- B8: the established BKM theorem is consumed only here.

    invokeBKMContinuation : FiniteVorticityIntegral → Continuation

open BernsteinExpenditureData public

------------------------------------------------------------------------
-- B1
------------------------------------------------------------------------

shell-vorticity-Bernstein :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  (j : Nat) (t : Time D) →
  _≤ᵥ_ D
    (shellVorticityLInfinity D j (path D t))
    (weightedVelocityShell D j (path D t))
shell-vorticity-Bernstein D j t =
  ≤ᵥ-trans D
    (shellBernsteinL2ToLInfinity D j t)
    (shellCurlL2Estimate D j t)

------------------------------------------------------------------------
-- B2
------------------------------------------------------------------------

vorticity-shell-summation :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  (t : Time D) →
  _≤ᵥ_ D
    (vorticityLInfinity D (path D t))
    (weightedShellSum D (path D t))
vorticity-shell-summation D = vorticityReconstruction D

------------------------------------------------------------------------
-- B3
------------------------------------------------------------------------

compactGamma-weighted-shell-decay :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  (j : Nat) (t : Time D) →
  _≤ᵥ_ D
    (weightedVelocityShell D j (path D t))
    (multiply D (coefficient D j)
      (compactGammaEnvelope D (path D t)))
compactGamma-weighted-shell-decay D =
  admissibleWeightedShellDecay D
    (invariantRegion D)
    (compactGammaPacketEstimates D)

compactGamma-controls-weighted-shell-sum :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  (t : Time D) →
  _≤ᵥ_ D
    (weightedShellSum D (path D t))
    (multiply D (coefficientSumBound D)
      (compactGammaEnvelope D (path D t)))
compactGamma-controls-weighted-shell-sum D =
  deriveWeightedShellSummation D
    (invariantRegion D)
    (compactGammaPacketEstimates D)
    (summableCoefficientFamily D)

------------------------------------------------------------------------
-- B4
------------------------------------------------------------------------

expenditure-differential-inequality :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  ExpenditureDifferentialInequality D
expenditure-differential-inequality D =
  deriveExpenditureDifferentialInequality D
    (invariantRegion D)
    (energyDissipationControl D)
    (compactGammaPacketEstimates D)
    (noHighSobolevPersistenceInput D)
    (noPreexistingVorticityIntegralInput D)
    (noBKMContinuationInput D)
    (noBKMDerivedInput D)

------------------------------------------------------------------------
-- B5
------------------------------------------------------------------------

finite-envelope-expenditure :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  FiniteEnvelopeExpenditure D
finite-envelope-expenditure D =
  integrateExpenditureInequality D
    (energyDissipationControl D)
    (expenditure-differential-inequality D)

------------------------------------------------------------------------
-- B6
------------------------------------------------------------------------

finite-weighted-shell-expenditure :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  FiniteWeightedShellExpenditure D
finite-weighted-shell-expenditure D =
  integrateWeightedShellDomination D
    (compactGamma-controls-weighted-shell-sum D)
    (finite-envelope-expenditure D)

------------------------------------------------------------------------
-- B7
------------------------------------------------------------------------

finite-vorticity-integral :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  FiniteVorticityIntegral D
finite-vorticity-integral D =
  integrateVorticityReconstruction D
    (vorticity-shell-summation D)
    (finite-weighted-shell-expenditure D)

------------------------------------------------------------------------
-- B8
------------------------------------------------------------------------

bkm-continuation-at-endpoint :
  ∀ {ls lt lv le lc}
    (D : BernsteinExpenditureData {ls} {lt} {lv} {le} {lc}) →
  Continuation D
bkm-continuation-at-endpoint D =
  invokeBKMContinuation D (finite-vorticity-integral D)

------------------------------------------------------------------------
-- Machine-checkable dependency order.  There is no edge from BKM or a
-- BKM-derived Sobolev theorem into B1--B7.
------------------------------------------------------------------------

data BernsteinExpenditureStage : Set where
  invariantRegionStage : BernsteinExpenditureStage
  energyDissipationStage : BernsteinExpenditureStage
  bernsteinStage : BernsteinExpenditureStage
  compactGammaDecayStage : BernsteinExpenditureStage
  differentialExpenditureStage : BernsteinExpenditureStage
  envelopeIntegralStage : BernsteinExpenditureStage
  weightedShellIntegralStage : BernsteinExpenditureStage
  vorticityIntegralStage : BernsteinExpenditureStage
  bkmEndpointStage : BernsteinExpenditureStage

record BernsteinExpenditureDependencyAudit : Set where
  constructor mkBernsteinExpenditureDependencyAudit
  field
    b1 : BernsteinExpenditureStage
    b1-is-Bernstein : b1 ≡ bernsteinStage
    b3 : BernsteinExpenditureStage
    b3-is-compactGamma : b3 ≡ compactGammaDecayStage
    b4 : BernsteinExpenditureStage
    b4-is-differential : b4 ≡ differentialExpenditureStage
    b5 : BernsteinExpenditureStage
    b5-is-envelope : b5 ≡ envelopeIntegralStage
    b6 : BernsteinExpenditureStage
    b6-is-shell-integral : b6 ≡ weightedShellIntegralStage
    b7 : BernsteinExpenditureStage
    b7-is-vorticity-integral : b7 ≡ vorticityIntegralStage
    b8 : BernsteinExpenditureStage
    b8-is-endpoint : b8 ≡ bkmEndpointStage

canonicalBernsteinExpenditureDependencyAudit :
  BernsteinExpenditureDependencyAudit
canonicalBernsteinExpenditureDependencyAudit =
  mkBernsteinExpenditureDependencyAudit
    bernsteinStage refl
    compactGammaDecayStage refl
    differentialExpenditureStage refl
    envelopeIntegralStage refl
    weightedShellIntegralStage refl
    vorticityIntegralStage refl
    bkmEndpointStage refl
