module DASHI.Physics.Closure.NSTriadKNAdmissibleFourierTriadCarrier where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_<_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNAdmissibleConstrainedSpectralAudit as Spectral
import DASHI.Physics.Closure.NSTriadKNVariationalRigidityOperatorRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- Local list membership, independent of decidable equality on Fourier modes.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Rich Stage-3 state space.
------------------------------------------------------------------------

record FourierCoefficient : Set where
  constructor coefficient
  field
    mode : Z3.FourierMode
    amplitude : Nat

open FourierCoefficient public

record RetainedTriad : Set where
  constructor triad
  field
    p q k : Z3.FourierMode
    resonance : Z3.Resonance p q k
    weight : Nat

open RetainedTriad public

sumAmplitudes : List FourierCoefficient → Nat
sumAmplitudes [] = zero
sumAmplitudes (x ∷ xs) = amplitude x + sumAmplitudes xs

sumTriadWeights : List RetainedTriad → Nat
sumTriadWeights [] = zero
sumTriadWeights (τ ∷ τs) = weight τ + sumTriadWeights τs

record FourierTriadAdmissibilityInputs : Set₁ where
  constructor mkFourierTriadAdmissibilityInputs
  field
    divergenceFree : FourierCoefficient → Set
    gaugeFixed : List FourierCoefficient → Set
    phaseCompatible : RetainedTriad → Set
    parityCompatible : RetainedTriad → Set
    retainedSector : RetainedTriad → Set

open FourierTriadAdmissibilityInputs public

record AdmissibleFourierTriadState
    (inputs : FourierTriadAdmissibilityInputs) : Set where
  constructor mkAdmissibleFourierTriadState
  field
    coefficients : List FourierCoefficient
    incidences : List RetainedTriad

    coefficientsDivergenceFree :
      (c : FourierCoefficient) → c ∈ coefficients → divergenceFree inputs c

    stateGaugeFixed : gaugeFixed inputs coefficients

    incidencesPhaseCompatible :
      (τ : RetainedTriad) → τ ∈ incidences → phaseCompatible inputs τ

    incidencesParityCompatible :
      (τ : RetainedTriad) → τ ∈ incidences → parityCompatible inputs τ

    incidencesRetained :
      (τ : RetainedTriad) → τ ∈ incidences → retainedSector inputs τ

open AdmissibleFourierTriadState public

------------------------------------------------------------------------
-- Late energy projection.
------------------------------------------------------------------------

fourierTriadResidueEnergy :
  {inputs : FourierTriadAdmissibilityInputs} →
  AdmissibleFourierTriadState inputs → Nat
fourierTriadResidueEnergy x =
  sumAmplitudes (coefficients x) + sumTriadWeights (incidences x)

forgetFourierTriadToEnergy :
  {inputs : FourierTriadAdmissibilityInputs} →
  AdmissibleFourierTriadState inputs → ResidueNorm.ResidueEnergyCarrier (suc zero)
forgetFourierTriadToEnergy x =
  ResidueNorm.mkResidueEnergyCarrier (fourierTriadResidueEnergy x)

forgetFourierTriadPreservesEnergy :
  {inputs : FourierTriadAdmissibilityInputs} →
  (x : AdmissibleFourierTriadState inputs) →
  ResidueNorm.residueEnergy (forgetFourierTriadToEnergy x)
    ≡ fourierTriadResidueEnergy x
forgetFourierTriadPreservesEnergy x = refl

------------------------------------------------------------------------
-- Actual Stage-3 operator boundary on the rich carrier.
------------------------------------------------------------------------

record RichStage3PairIncidenceOperator
    (inputs : FourierTriadAdmissibilityInputs) : Set₁ where
  constructor mkRichStage3PairIncidenceOperator
  field
    State : Set
    injectState : State → AdmissibleFourierTriadState inputs

    Index : Set
    finiteIndexCode : Index → Nat

    matrixEntry : Index → Index → Nat
    coefficientAt : State → Index → Nat
    operatorAction : State → State

    pairing : State → State → Nat
    qBase : State → Nat
    qError : State → Nat
    strongNormSquared : State → Nat

    operatorRealizesMatrix : Set
    qErrorIsOperatorQuadraticForm :
      (x : State) → qError x ≡ pairing (operatorAction x) x

    residueEnergy : State → Nat
    forgetToEnergy : State → ResidueNorm.ResidueEnergyCarrier (suc zero)
    forgetPreservesEnergy :
      (x : State) → ResidueNorm.residueEnergy (forgetToEnergy x) ≡ residueEnergy x

open RichStage3PairIncidenceOperator public

record RichStage3ConstrainedModel
    (inputs : FourierTriadAdmissibilityInputs) : Set₁ where
  constructor mkRichStage3ConstrainedModel
  field
    operator : RichStage3PairIncidenceOperator inputs

    admissible normalized rigid :
      RichStage3PairIncidenceOperator.State operator → Set

    everyStateCarriesAdmissibilityData :
      (x : RichStage3PairIncidenceOperator.State operator) → admissible x

open RichStage3ConstrainedModel public

richModelToSpectralCarrier :
  {inputs : FourierTriadAdmissibilityInputs} →
  RichStage3ConstrainedModel inputs → Spectral.AdmissibleStage3Carrier
richModelToSpectralCarrier {inputs} model =
  Spectral.mkAdmissibleStage3Carrier
    (RichStage3PairIncidenceOperator.State op)
    (RichStage3ConstrainedModel.admissible model)
    (RichStage3ConstrainedModel.normalized model)
    (RichStage3ConstrainedModel.rigid model)
    (RichStage3PairIncidenceOperator.residueEnergy op)
    (RichStage3PairIncidenceOperator.qBase op)
    (RichStage3PairIncidenceOperator.qError op)
    (RichStage3PairIncidenceOperator.strongNormSquared op)
    (RichStage3PairIncidenceOperator.forgetToEnergy op)
    (RichStage3PairIncidenceOperator.forgetPreservesEnergy op)
  where
  op : RichStage3PairIncidenceOperator inputs
  op = RichStage3ConstrainedModel.operator model

------------------------------------------------------------------------
-- Exact closure handoff.
------------------------------------------------------------------------

record RichStage3CompatibilityHandoff
    (inputs : FourierTriadAdmissibilityInputs)
    (model : RichStage3ConstrainedModel inputs) : Set₁ where
  constructor mkRichStage3CompatibilityHandoff
  field
    spectralGap :
      Spectral.AdmissibleStage3SpectralGap
        (richModelToSpectralCarrier model)

    scale : ScaleHeadroom.CompatibilityScale (suc zero)

    scaledRayleigh :
      Refinement.ScaledRayleighBaseCertificate
        (suc zero)
        (RichStage3PairIncidenceOperator.State
          (RichStage3ConstrainedModel.operator model))
        scale
        (RichStage3PairIncidenceOperator.strongNormSquared
          (RichStage3ConstrainedModel.operator model))
        (RichStage3PairIncidenceOperator.qBase
          (RichStage3ConstrainedModel.operator model))

    scaledOperator :
      Refinement.ScaledRefinedOperatorEstimate
        (suc zero)
        (RichStage3PairIncidenceOperator.State
          (RichStage3ConstrainedModel.operator model))
        scale
        (RichStage3PairIncidenceOperator.qError
          (RichStage3ConstrainedModel.operator model))
        (RichStage3PairIncidenceOperator.strongNormSquared
          (RichStage3ConstrainedModel.operator model))

    strictConstantGap :
      Refinement.ScaledRefinedOperatorEstimate.refinedErrorConstant scaledOperator
        < Refinement.ScaledRayleighBaseCertificate.baseConstant scaledRayleigh

open RichStage3CompatibilityHandoff public

handoffToVariationalCompatibility :
  {inputs : FourierTriadAdmissibilityInputs} →
  {model : RichStage3ConstrainedModel inputs} →
  (handoff : RichStage3CompatibilityHandoff inputs model) →
  Refinement.VariationalCompatibilityCertificate
    (suc zero)
    (RichStage3PairIncidenceOperator.State
      (RichStage3ConstrainedModel.operator model))
    (RichStage3CompatibilityHandoff.scale handoff)
    (RichStage3PairIncidenceOperator.qBase
      (RichStage3ConstrainedModel.operator model))
    (RichStage3PairIncidenceOperator.qError
      (RichStage3ConstrainedModel.operator model))
    (RichStage3PairIncidenceOperator.strongNormSquared
      (RichStage3ConstrainedModel.operator model))
handoffToVariationalCompatibility handoff =
  Refinement.mkVariationalCompatibilityCertificate
    (RichStage3CompatibilityHandoff.scaledRayleigh handoff)
    (RichStage3CompatibilityHandoff.scaledOperator handoff)
    (RichStage3CompatibilityHandoff.strictConstantGap handoff)

------------------------------------------------------------------------
-- Audit status.
------------------------------------------------------------------------

admissibleFourierTriadCarrierImplemented : Bool
admissibleFourierTriadCarrierImplemented = true

admissibleFourierTriadCarrierImplementedIsTrue :
  admissibleFourierTriadCarrierImplemented ≡ true
admissibleFourierTriadCarrierImplementedIsTrue = refl

richStage3OperatorHandoffImplemented : Bool
richStage3OperatorHandoffImplemented = true

richStage3OperatorHandoffImplementedIsTrue :
  richStage3OperatorHandoffImplemented ≡ true
richStage3OperatorHandoffImplementedIsTrue = refl

actualRetainedTriadEnumerationConnected : Bool
actualRetainedTriadEnumerationConnected = false

actualRetainedTriadEnumerationConnectedIsFalse :
  actualRetainedTriadEnumerationConnected ≡ false
actualRetainedTriadEnumerationConnectedIsFalse = refl

actualRichStage3OperatorClosed : Bool
actualRichStage3OperatorClosed = false

actualRichStage3OperatorClosedIsFalse :
  actualRichStage3OperatorClosed ≡ false
actualRichStage3OperatorClosedIsFalse = refl
