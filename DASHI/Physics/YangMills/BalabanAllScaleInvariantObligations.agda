module DASHI.Physics.YangMills.BalabanAllScaleInvariantObligations where

------------------------------------------------------------------------
-- Exact quantitative obligations for preservation of the all-scale RG
-- domain.  The hard analytic inequalities remain explicit inputs; this
-- module proves that those inputs discharge the six fields of
-- QuantitativeRGStep and the accumulated-error field used by the existing
-- all-scale induction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanAllScaleRGClosure as RG
import DASHI.Physics.YangMills.BalabanQuantitativeAllScaleInvariant as AllScale

------------------------------------------------------------------------
-- A1. Running coupling.
------------------------------------------------------------------------

record RunningCouplingPreservation
    {State Scalar : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    coupling : Nat → State → Scalar
    betaZero groupConstant : Scalar
    remainder : Nat → State → Scalar

    subtract multiply : Scalar → Scalar → Scalar
    cube fifthPower absoluteValue : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    couplingRecursion : ∀ scale state →
      coupling (suc scale) (renormalize scale state) ≡
      subtract (coupling scale state)
        (subtract
          (multiply betaZero (cube (coupling scale state)))
          (remainder scale state))

    remainderBound : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual
        (absoluteValue (remainder scale state))
        (multiply groupConstant (fifthPower (coupling scale state)))

    allowedIntervalPreserved : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      AllScale.CouplingAdmissible profile (suc scale)
        (renormalize scale state)

open RunningCouplingPreservation public

couplingPreserved :
  ∀ {State Scalar : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  RunningCouplingPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.CouplingAdmissible profile (suc scale)
    (renormalize scale state)
couplingPreserved data = allowedIntervalPreserved data

------------------------------------------------------------------------
-- A2. Small-field radius.
------------------------------------------------------------------------

record FieldRadiusPreservation
    {State Radius : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    fieldSize : Nat → State → Radius
    allowedRadius : Nat → Radius
    LessEqual : Radius → Radius → Set

    inputWithinRadius : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual (fieldSize scale state) (allowedRadius scale)

    radiusTransport : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual
        (fieldSize (suc scale) (renormalize scale state))
        (allowedRadius (suc scale))

    radiusBoundImpliesAdmissible : ∀ scale state →
      LessEqual (fieldSize scale state) (allowedRadius scale) →
      AllScale.FieldRadiusAdmissible profile scale state

open FieldRadiusPreservation public

fieldRadiusPreserved :
  ∀ {State Radius : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  FieldRadiusPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.FieldRadiusAdmissible profile (suc scale)
    (renormalize scale state)
fieldRadiusPreserved data scale state admissible =
  radiusBoundImpliesAdmissible data (suc scale)
    (renormalize _ scale state)
    (radiusTransport data scale state admissible)

------------------------------------------------------------------------
-- A3. Polymer norm: one-step small-field estimate plus Step V.
------------------------------------------------------------------------

record PolymerNormPreservation
    {State Bound : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    smallFieldContribution stepVContribution outputPolymerNorm :
      Nat → State → Bound
    nextPolymerBudget : Nat → Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    smallFieldEstimate : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual (smallFieldContribution scale state)
        (nextPolymerBudget (suc scale))

    stepVEstimate : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual (stepVContribution scale state)
        (nextPolymerBudget (suc scale))

    outputDecompositionBound : ∀ scale state →
      LessEqual
        (outputPolymerNorm (suc scale) (renormalize scale state))
        (add (smallFieldContribution scale state)
             (stepVContribution scale state))

    combinedBudgetBound : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual
        (outputPolymerNorm (suc scale) (renormalize scale state))
        (nextPolymerBudget (suc scale))

    polymerBoundImpliesAdmissible : ∀ scale state →
      LessEqual (outputPolymerNorm scale state) (nextPolymerBudget scale) →
      AllScale.PolymerAdmissible profile scale state

open PolymerNormPreservation public

polymerPreserved :
  ∀ {State Bound : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  PolymerNormPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.PolymerAdmissible profile (suc scale)
    (renormalize scale state)
polymerPreserved data scale state admissible =
  polymerBoundImpliesAdmissible data (suc scale)
    (renormalize _ scale state)
    (combinedBudgetBound data scale state admissible)

------------------------------------------------------------------------
-- A4. Analyticity radius under every nonlinear operation in the step.
------------------------------------------------------------------------

record AnalyticityRadiusPreservation
    {State Radius : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    inputRadius outputRadius requiredRadius : Nat → State → Radius
    compositionLoss bchLoss determinantLoss localizationLoss :
      Nat → State → Radius
    remainingRadius : Radius → Radius → Radius
    combineLosses : Radius → Radius → Radius
    LessEqual : Radius → Radius → Set

    totalLossControlled : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual
        (combineLosses (compositionLoss scale state)
          (combineLosses (bchLoss scale state)
            (combineLosses (determinantLoss scale state)
              (localizationLoss scale state))))
        (inputRadius scale state)

    outputRadiusAfterLoss : ∀ scale state →
      outputRadius (suc scale) (renormalize scale state) ≡
      remainingRadius (inputRadius scale state)
        (combineLosses (compositionLoss scale state)
          (combineLosses (bchLoss scale state)
            (combineLosses (determinantLoss scale state)
              (localizationLoss scale state))))

    nextRadiusRetained : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual (requiredRadius (suc scale) (renormalize scale state))
        (outputRadius (suc scale) (renormalize scale state))

    retainedRadiusImpliesAdmissible : ∀ scale state →
      LessEqual (requiredRadius scale state) (outputRadius scale state) →
      AllScale.AnalyticityAdmissible profile scale state

open AnalyticityRadiusPreservation public

analyticityPreserved :
  ∀ {State Radius : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  AnalyticityRadiusPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.AnalyticityAdmissible profile (suc scale)
    (renormalize scale state)
analyticityPreserved data scale state admissible =
  retainedRadiusImpliesAdmissible data (suc scale)
    (renormalize _ scale state)
    (nextRadiusRetained data scale state admissible)

------------------------------------------------------------------------
-- A5. Gauge chart and Faddeev--Popov invertibility.
------------------------------------------------------------------------

record GaugeFixingDomainPreservation
    {State : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    WithinGaugeChart : Nat → State → Set
    FaddeevPopovInvertible : Nat → State → Set

    nextBackgroundWithinChart : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      WithinGaugeChart (suc scale) (renormalize scale state)

    nextFaddeevPopovInvertible : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      FaddeevPopovInvertible (suc scale) (renormalize scale state)

    chartAndInvertibilityImplyAdmissible : ∀ scale state →
      WithinGaugeChart scale state →
      FaddeevPopovInvertible scale state →
      AllScale.GaugeFixingAdmissible profile scale state

open GaugeFixingDomainPreservation public

gaugeFixingPreserved :
  ∀ {State : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  GaugeFixingDomainPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.GaugeFixingAdmissible profile (suc scale)
    (renormalize scale state)
gaugeFixingPreserved data scale state admissible =
  chartAndInvertibilityImplyAdmissible data (suc scale)
    (renormalize _ scale state)
    (nextBackgroundWithinChart data scale state admissible)
    (nextFaddeevPopovInvertible data scale state admissible)

------------------------------------------------------------------------
-- A6. Exponential polymer locality.
------------------------------------------------------------------------

record LocalityPreservation
    {State Decay : Set}
    (profile : AllScale.RGAdmissibilityProfile State)
    (renormalize : Nat → State → State) : Set₁ where
  field
    outputDecayRate requiredDecayRate : Nat → State → Decay
    LessEqual : Decay → Decay → Set

    exponentialPolymerDecayRetained : ∀ scale state →
      AllScale.AdmissibleAt profile scale state →
      LessEqual
        (requiredDecayRate (suc scale) (renormalize scale state))
        (outputDecayRate (suc scale) (renormalize scale state))

    decayRateImpliesAdmissible : ∀ scale state →
      LessEqual (requiredDecayRate scale state) (outputDecayRate scale state) →
      AllScale.LocalityAdmissible profile scale state

open LocalityPreservation public

localityPreserved :
  ∀ {State Decay : Set}
    {profile : AllScale.RGAdmissibilityProfile State}
    {renormalize : Nat → State → State} →
  LocalityPreservation profile renormalize →
  ∀ scale state →
  AllScale.AdmissibleAt profile scale state →
  AllScale.LocalityAdmissible profile (suc scale)
    (renormalize scale state)
localityPreserved data scale state admissible =
  decayRateImpliesAdmissible data (suc scale)
    (renormalize _ scale state)
    (exponentialPolymerDecayRetained data scale state admissible)

------------------------------------------------------------------------
-- Assemble A1--A6 into the pre-existing QuantitativeRGStep.
------------------------------------------------------------------------

record QuantitativeInvariantObligations
    (State CouplingScalar Radius PolymerBound Decay : Set) : Set₁ where
  field
    profile : AllScale.RGAdmissibilityProfile State
    renormalize : Nat → State → State
    runningCoupling : RunningCouplingPreservation profile renormalize
    fieldRadius : FieldRadiusPreservation profile renormalize
    polymerNorm : PolymerNormPreservation profile renormalize
    analyticityRadius : AnalyticityRadiusPreservation profile renormalize
    gaugeFixingDomain : GaugeFixingDomainPreservation profile renormalize
    localityDecay : LocalityPreservation profile renormalize

open QuantitativeInvariantObligations public

quantitativeRGStep :
  ∀ {State CouplingScalar Radius PolymerBound Decay : Set} →
  QuantitativeInvariantObligations State CouplingScalar Radius PolymerBound Decay →
  AllScale.QuantitativeRGStep State
quantitativeRGStep obligations = record
  { profile = profile obligations
  ; renormalize = renormalize obligations
  ; couplingPreserved = couplingPreserved (runningCoupling obligations)
  ; fieldRadiusPreserved = fieldRadiusPreserved (fieldRadius obligations)
  ; polymerPreserved = polymerPreserved (polymerNorm obligations)
  ; analyticityPreserved = analyticityPreserved (analyticityRadius obligations)
  ; gaugeFixingPreserved = gaugeFixingPreserved (gaugeFixingDomain obligations)
  ; localityPreserved = localityPreserved (localityDecay obligations)
  }

------------------------------------------------------------------------
-- A7. Summability of accumulated RG errors.
------------------------------------------------------------------------

record RGErrorSummability (ErrorBound : Set) : Set₁ where
  field
    errorAt : Nat → ErrorBound
    partialSum : Nat → ErrorBound
    totalError : ErrorBound
    LessEqual : ErrorBound → ErrorBound → Set
    rgErrorsSummable : ∀ n → LessEqual (partialSum n) totalError

open RGErrorSummability public

toSummableRGErrors :
  ∀ {ErrorBound : Set} →
  RGErrorSummability ErrorBound →
  RG.SummableRGErrors ErrorBound
toSummableRGErrors errors = record
  { errorAt = errorAt errors
  ; partialSum = partialSum errors
  ; totalBound = totalError errors
  ; LessEqual = LessEqual errors
  ; partialSumsBounded = rgErrorsSummable errors
  }

allScaleInvariantObligationsAssemblyLevel : ProofLevel
allScaleInvariantObligationsAssemblyLevel = machineChecked

allScaleInvariantAnalyticInputsLevel : ProofLevel
allScaleInvariantAnalyticInputsLevel = conjectural
