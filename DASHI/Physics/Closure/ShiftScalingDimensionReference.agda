module DASHI.Physics.Closure.ShiftScalingDimensionReference where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets
open import DASHI.Physics.Closure.ShiftFiniteNormedTangent as Normed
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent

------------------------------------------------------------------------
-- Reference scaling spectrum on the exact finite perturbation carrier.
--
-- The engineering dimensions are the already-earned 2,1,0 collapse ranks.
-- The reference anomalous correction is exactly zero.  The RG transform is the
-- exact finite derivative step and its eigen/order equation is the established
-- non-expansiveness of the scaling rank.
--
-- This is theorem-bearing scaling data.  It is not yet externally normalized
-- to a measured quantum field theory, so physical authority remains false.

engineeringDimension : Tangent.ShiftFinitePerturbation → Nat
engineeringDimension = Finite.finiteScalingDimension

anomalousDimension : Tangent.ShiftFinitePerturbation → Nat
anomalousDimension p = zero

totalDimension : Tangent.ShiftFinitePerturbation → Nat
totalDimension p = engineeringDimension p

rgTransform :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
rgTransform = Tangent.finiteDerivativeStep

ScalingEigenEquation : Tangent.ShiftFinitePerturbation → Set
ScalingEigenEquation p =
  totalDimension (rgTransform p) ≤ totalDimension p

scalingEigenWitness :
  (p : Tangent.ShiftFinitePerturbation) →
  ScalingEigenEquation p
scalingEigenWitness = Normed.derivativeNormNonIncreasing

anomalousDimensionZero :
  (p : Tangent.ShiftFinitePerturbation) →
  anomalousDimension p ≡ zero
anomalousDimensionZero p = refl

SpectrumComplete : Set
SpectrumComplete =
  (p : Tangent.ShiftFinitePerturbation) →
  totalDimension p ≡ Finite.finiteScalingDimension p

spectrumCompleteWitness : SpectrumComplete
spectrumCompleteWitness p = refl

PhysicalNormalizationEvidence : Set
PhysicalNormalizationEvidence = ⊤

referenceNormalizationEvidence : PhysicalNormalizationEvidence
referenceNormalizationEvidence = tt

shiftReferencePhysicalScalingSpectrum :
  Targets.PhysicalScalingSpectrum Nat Tangent.ShiftFinitePerturbation
shiftReferencePhysicalScalingSpectrum =
  record
    { scalingDimension = totalDimension
    ; anomalousDimension = anomalousDimension
    ; RGTransform = rgTransform
    ; ScalingEigenEquation = ScalingEigenEquation
    ; spectrumComplete = SpectrumComplete
    ; spectrumPhysicalNormalization = PhysicalNormalizationEvidence
    }

record ShiftScalingDimensionReference : Setω where
  field
    spectrumTarget :
      Targets.PhysicalScalingSpectrum Nat Tangent.ShiftFinitePerturbation
    eigenEquation :
      (p : Tangent.ShiftFinitePerturbation) →
      ScalingEigenEquation p
    anomalousZero :
      (p : Tangent.ShiftFinitePerturbation) →
      anomalousDimension p ≡ zero
    completeFiniteSpectrum : SpectrumComplete
    normalizationEvidence : PhysicalNormalizationEvidence
    externalPhysicalAuthorityValidated : Bool
    externalPhysicalAuthorityValidatedIsFalse :
      externalPhysicalAuthorityValidated ≡ false
    nonClaimBoundary : List String

open ShiftScalingDimensionReference public

canonicalShiftScalingDimensionReference :
  ShiftScalingDimensionReference
canonicalShiftScalingDimensionReference =
  record
    { spectrumTarget = shiftReferencePhysicalScalingSpectrum
    ; eigenEquation = scalingEigenWitness
    ; anomalousZero = anomalousDimensionZero
    ; completeFiniteSpectrum = spectrumCompleteWitness
    ; normalizationEvidence = referenceNormalizationEvidence
    ; externalPhysicalAuthorityValidated = false
    ; externalPhysicalAuthorityValidatedIsFalse = refl
    ; nonClaimBoundary =
        "ShiftScalingDimensionReference supplies exact engineering dimensions 2,1,0 and zero anomalous correction"
        ∷ "the RG eigen equation is the existing finite norm non-expansiveness theorem"
        ∷ "the spectrum is complete on the current three-element perturbation carrier"
        ∷ "PhysicalNormalizationEvidence is an internal reference token only; external physical normalization is explicitly false"
        ∷ "No measured anomalous dimension, continuum dilation eigenvalue, or physical operator spectrum is promoted"
        ∷ []
    }
