module DASHI.Biology.AnaestheticErrorBoundMechanismFibreMonotonicityExact where

open import DASHI.Core.Prelude

import DASHI.Biology.CrossKingdomAnaestheticMechanismFibreRefinementExact as Fibre

------------------------------------------------------------------------
-- ORDERED ERROR BOUNDS / REVERSE-FIBRE MONOTONICITY
--
-- This owner adds the second reverse-refinement axis promised by the
-- anaesthetic mechanism-fibre lane:
--
--   more observables        -> smaller admissible mechanism fibre
--   tighter validated error -> smaller admissible mechanism fibre.
--
-- The generic theorem below assumes only that compatibility is monotone with
-- respect to an explicit error-bound preorder. It does not assume a metric,
-- Gaussian noise model, posterior distribution, or any particular experiment.
------------------------------------------------------------------------

record OrderedErrorCompatibility : Set₁ where
  constructor orderedErrorCompatibility
  field
    Candidate : Set
    Measurement : Set
    ErrorBound : Set

    _≼_ : ErrorBound → ErrorBound → Set
    errorRefl : (e : ErrorBound) → e ≼ e
    errorTrans :
      {e₁ e₂ e₃ : ErrorBound} → e₁ ≼ e₂ → e₂ ≼ e₃ → e₁ ≼ e₃

    compatible : Candidate → Measurement → ErrorBound → Set

    compatibilityMonotone :
      (candidate : Candidate) →
      (measurement : Measurement) →
      {tight loose : ErrorBound} →
      tight ≼ loose →
      compatible candidate measurement tight →
      compatible candidate measurement loose

open OrderedErrorCompatibility public

------------------------------------------------------------------------
-- Fibre at one measurement/error bound.
------------------------------------------------------------------------

AdmissibleMechanismFibre :
  (model : OrderedErrorCompatibility) →
  Measurement model →
  ErrorBound model →
  Set
AdmissibleMechanismFibre model measurement error =
  Σ (Candidate model)
    (λ candidate → compatible model candidate measurement error)

------------------------------------------------------------------------
-- Generic monotonicity theorem:
-- tighter <= looser implies every tightly compatible candidate remains
-- compatible under the looser validated bound.
------------------------------------------------------------------------

tighterBoundFibreEmbedsInLooserBoundFibre :
  (model : OrderedErrorCompatibility) →
  (measurement : Measurement model) →
  {tight loose : ErrorBound model} →
  _≼_ model tight loose →
  AdmissibleMechanismFibre model measurement tight →
  AdmissibleMechanismFibre model measurement loose
tighterBoundFibreEmbedsInLooserBoundFibre model measurement tight≼loose point =
  proj₁ point ,
  compatibilityMonotone model
    (proj₁ point)
    measurement
    tight≼loose
    (proj₂ point)

------------------------------------------------------------------------
-- Strictness witness: some candidate may enter only when the error bound is
-- loosened. This records proper fibre growth without requiring cardinalities.
------------------------------------------------------------------------

record StrictErrorFibreGrowth
    (model : OrderedErrorCompatibility)
    (measurement : Measurement model)
    (tight loose : ErrorBound model) : Set where
  constructor strictErrorFibreGrowth
  field
    tightNoLooserThanLoose : _≼_ model tight loose
    witnessCandidate : Candidate model
    compatibleAtLoose : compatible model witnessCandidate measurement loose
    incompatibleAtTight :
      compatible model witnessCandidate measurement tight → ⊥

open StrictErrorFibreGrowth public

strictGrowthWitnessProducesLooserOnlyPoint :
  {model : OrderedErrorCompatibility} →
  {measurement : Measurement model} →
  {tight loose : ErrorBound model} →
  StrictErrorFibreGrowth model measurement tight loose →
  Σ (AdmissibleMechanismFibre model measurement loose)
    (λ point →
      compatible model (proj₁ point) measurement tight → ⊥)
strictGrowthWitnessProducesLooserOnlyPoint witness =
  (witnessCandidate witness , compatibleAtLoose witness) ,
  incompatibleAtTight witness

------------------------------------------------------------------------
-- Finite synthetic anaesthetic-calibrated witness.
--
-- This is DASHI mathematics, not an empirical claim that any named candidate
-- has the error profile below. It proves the theorem shape needed by future
-- voltage/current datasets.
------------------------------------------------------------------------

data BoundLevel : Set where
  tightBound
  looseBound
  : BoundLevel

data SyntheticMeasurement : Set where
  measuredSuppressedTrace : SyntheticMeasurement

data SyntheticCandidate : Set where
  robustCandidate
  marginalCandidate
  : SyntheticCandidate

data BoundLeq : BoundLevel → BoundLevel → Set where
  tightTight : BoundLeq tightBound tightBound
  tightLoose : BoundLeq tightBound looseBound
  looseLoose : BoundLeq looseBound looseBound

boundRefl : (e : BoundLevel) → BoundLeq e e
boundRefl tightBound = tightTight
boundRefl looseBound = looseLoose

boundTrans :
  {e₁ e₂ e₃ : BoundLevel} →
  BoundLeq e₁ e₂ → BoundLeq e₂ e₃ → BoundLeq e₁ e₃
boundTrans tightTight proof = proof
boundTrans tightLoose looseLoose = tightLoose
boundTrans looseLoose looseLoose = looseLoose

data SyntheticCompatible :
    SyntheticCandidate → SyntheticMeasurement → BoundLevel → Set where
  robustAtTight :
    SyntheticCompatible robustCandidate measuredSuppressedTrace tightBound
  robustAtLoose :
    SyntheticCompatible robustCandidate measuredSuppressedTrace looseBound
  marginalAtLoose :
    SyntheticCompatible marginalCandidate measuredSuppressedTrace looseBound

syntheticCompatibilityMonotone :
  (candidate : SyntheticCandidate) →
  (measurement : SyntheticMeasurement) →
  {tight loose : BoundLevel} →
  BoundLeq tight loose →
  SyntheticCompatible candidate measurement tight →
  SyntheticCompatible candidate measurement loose
syntheticCompatibilityMonotone robustCandidate measuredSuppressedTrace tightTight proof = proof
syntheticCompatibilityMonotone robustCandidate measuredSuppressedTrace tightLoose robustAtTight = robustAtLoose
syntheticCompatibilityMonotone robustCandidate measuredSuppressedTrace looseLoose proof = proof
syntheticCompatibilityMonotone marginalCandidate measuredSuppressedTrace tightTight ()
syntheticCompatibilityMonotone marginalCandidate measuredSuppressedTrace tightLoose ()
syntheticCompatibilityMonotone marginalCandidate measuredSuppressedTrace looseLoose proof = proof

syntheticOrderedErrorModel : OrderedErrorCompatibility
syntheticOrderedErrorModel =
  orderedErrorCompatibility
    SyntheticCandidate
    SyntheticMeasurement
    BoundLevel
    BoundLeq
    boundRefl
    boundTrans
    SyntheticCompatible
    syntheticCompatibilityMonotone

marginalNotCompatibleAtTight :
  SyntheticCompatible marginalCandidate measuredSuppressedTrace tightBound → ⊥
marginalNotCompatibleAtTight ()

syntheticStrictErrorFibreGrowth :
  StrictErrorFibreGrowth
    syntheticOrderedErrorModel
    measuredSuppressedTrace
    tightBound
    looseBound
syntheticStrictErrorFibreGrowth =
  strictErrorFibreGrowth
    tightLoose
    marginalCandidate
    marginalAtLoose
    marginalNotCompatibleAtTight

------------------------------------------------------------------------
-- Weld to the preceding candidate-compatibility owner.
------------------------------------------------------------------------

record AnaestheticErrorBoundRefinementWeld : Set₁ where
  constructor anaestheticErrorBoundRefinementWeld
  field
    upstreamCompatibilityReceipt : Fibre.CandidateCompatibilityReceipt
    orderedCompatibility : OrderedErrorCompatibility
    MeasurementValue : Measurement orderedCompatibility
    tightBoundValue : ErrorBound orderedCompatibility
    looseBoundValue : ErrorBound orderedCompatibility
    tighterValidated :
      _≼_ orderedCompatibility tightBoundValue looseBoundValue
    strictGrowth :
      StrictErrorFibreGrowth
        orderedCompatibility
        MeasurementValue
        tightBoundValue
        looseBoundValue
    calibrationAuthorityReference : String
    errorOrderValidationReference : String

open AnaestheticErrorBoundRefinementWeld public

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record ErrorBoundMechanismFibreBoundary : Set where
  constructor errorBoundMechanismFibreBoundary
  field
    tighterValidatedBoundsMonotonicallyShrinkCandidateFibre : Bool
    tighterValidatedBoundsMonotonicallyShrinkCandidateFibreIsTrue :
      tighterValidatedBoundsMonotonicallyShrinkCandidateFibre ≡ true
    strictShrinkCanBeWitnessedWithoutUniqueIdentification : Bool
    strictShrinkCanBeWitnessedWithoutUniqueIdentificationIsTrue :
      strictShrinkCanBeWitnessedWithoutUniqueIdentification ≡ true
    tighterErrorBoundAutomaticallyMoreAccurate : Bool
    tighterErrorBoundAutomaticallyMoreAccurateIsFalse :
      tighterErrorBoundAutomaticallyMoreAccurate ≡ false
    boundOrderingRequiresValidationAuthority : Bool
    boundOrderingRequiresValidationAuthorityIsTrue :
      boundOrderingRequiresValidationAuthority ≡ true
    syntheticStrictnessWitnessIsEmpiricalAnaestheticMechanism : Bool
    syntheticStrictnessWitnessIsEmpiricalAnaestheticMechanismIsFalse :
      syntheticStrictnessWitnessIsEmpiricalAnaestheticMechanism ≡ false

canonicalErrorBoundMechanismFibreBoundary : ErrorBoundMechanismFibreBoundary
canonicalErrorBoundMechanismFibreBoundary =
  errorBoundMechanismFibreBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
