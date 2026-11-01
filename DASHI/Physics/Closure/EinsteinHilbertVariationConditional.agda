module DASHI.Physics.Closure.EinsteinHilbertVariationConditional where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Geometry.LorentzianLeviCivitaConditional as Geometry

------------------------------------------------------------------------
-- Conditional Einstein--Hilbert basis selection and action variation.
--
-- This module cross-pollinates the finite-jet admissibility row with the
-- Lorentzian / Levi-Civita witness chain.  It does not prove Lovelock's
-- theorem or perform tensor calculus internally.  Instead it defines the
-- exact producer obligations and proves that their conjunction closes the
-- requested receipt.

record EinsteinHilbertBasisWitness : Set where
  constructor mkEinsteinHilbertBasisWitness
  field
    basisLabel : String
    admissibilitySpec : Spec.DepthAdmissibilitySpec
    metricWitness : Geometry.LorentzianMetricWitness
    diffeomorphismInvariant : Bool
    localScalarDensity : Bool
    metricOnlyDynamicalGeometry : Bool
    atMostSecondMetricDerivatives : Bool
    fourDimensions : Bool
    boundaryTermsSeparated : Bool
    cosmologicalTermAdmitted : Bool
    LovelockClassificationSupplied : Bool
    onlyConstantAndRicciScalarAtLeadingOrder : Bool
    basisStatement : String

open EinsteinHilbertBasisWitness public

record EinsteinHilbertBasisReceipt (w : EinsteinHilbertBasisWitness) : Set where
  constructor mkEinsteinHilbertBasisReceipt
  field
    diffeomorphismReceipt : diffeomorphismInvariant w ≡ true
    localityReceipt : localScalarDensity w ≡ true
    metricOnlyReceipt : metricOnlyDynamicalGeometry w ≡ true
    twoDerivativeReceipt : atMostSecondMetricDerivatives w ≡ true
    fourDimensionalReceipt : fourDimensions w ≡ true
    boundaryReceipt : boundaryTermsSeparated w ≡ true
    LovelockReceipt : LovelockClassificationSupplied w ≡ true
    basisClosureReceipt : onlyConstantAndRicciScalarAtLeadingOrder w ≡ true

open EinsteinHilbertBasisReceipt public

record EinsteinHilbertVariationWitness (basis : EinsteinHilbertBasisWitness) : Set where
  constructor mkEinsteinHilbertVariationWitness
  field
    variationLabel : String
    metricVariationSupplied : Bool
    boundaryVariationControlled : Bool
    EinsteinTensorObtained : Bool
    cosmologicalVariationObtained : Bool
    normalizationConstantsTracked : Bool
    variationStatement : String

open EinsteinHilbertVariationWitness public

record EinsteinEquationReceipt
  (basis : EinsteinHilbertBasisWitness)
  (basisReceipt : EinsteinHilbertBasisReceipt basis)
  (variation : EinsteinHilbertVariationWitness basis) : Set where
  constructor mkEinsteinEquationReceipt
  field
    metricVariationReceipt : metricVariationSupplied variation ≡ true
    boundaryVariationReceipt : boundaryVariationControlled variation ≡ true
    EinsteinTensorReceipt : EinsteinTensorObtained variation ≡ true
    cosmologicalReceipt : cosmologicalVariationObtained variation ≡ true
    normalizationReceipt : normalizationConstantsTracked variation ≡ true

open EinsteinEquationReceipt public

assembleEinsteinEquationReceipt :
  (basis : EinsteinHilbertBasisWitness) →
  (basisReceipt : EinsteinHilbertBasisReceipt basis) →
  (variation : EinsteinHilbertVariationWitness basis) →
  metricVariationSupplied variation ≡ true →
  boundaryVariationControlled variation ≡ true →
  EinsteinTensorObtained variation ≡ true →
  cosmologicalVariationObtained variation ≡ true →
  normalizationConstantsTracked variation ≡ true →
  EinsteinEquationReceipt basis basisReceipt variation
assembleEinsteinEquationReceipt basis basisReceipt variation metric boundary einstein cosmological constants =
  mkEinsteinEquationReceipt metric boundary einstein cosmological constants

canonicalConditionalEHBasis : EinsteinHilbertBasisWitness
canonicalConditionalEHBasis =
  mkEinsteinHilbertBasisWitness
    "conditional-einstein-hilbert-basis"
    Spec.metricDiffeomorphismTwoJetSpec
    Geometry.canonicalConditionalLorentzianWitness
    true true true true true true true true true
    "given the full Lovelock hypotheses and classification, the leading basis is constant plus Ricci scalar up to boundary terms"

canonicalConditionalEHBasisReceipt :
  EinsteinHilbertBasisReceipt canonicalConditionalEHBasis
canonicalConditionalEHBasisReceipt =
  mkEinsteinHilbertBasisReceipt refl refl refl refl refl refl refl refl

canonicalConditionalEHVariation :
  EinsteinHilbertVariationWitness canonicalConditionalEHBasis
canonicalConditionalEHVariation =
  mkEinsteinHilbertVariationWitness
    "conditional-einstein-hilbert-variation"
    true true true true true
    "metric variation and normalization are supplied as checked obligations rather than inferred from the basis label"

canonicalConditionalEinsteinEquationReceipt :
  EinsteinEquationReceipt
    canonicalConditionalEHBasis
    canonicalConditionalEHBasisReceipt
    canonicalConditionalEHVariation
canonicalConditionalEinsteinEquationReceipt =
  assembleEinsteinEquationReceipt
    canonicalConditionalEHBasis
    canonicalConditionalEHBasisReceipt
    canonicalConditionalEHVariation
    refl refl refl refl refl

record EHDerivationBoundary : Set where
  constructor mkEHDerivationBoundary
  field
    conditionalReceiptAvailable : Bool
    valuationAloneForcesEHBasis : Bool
    repoContainsInternalLovelockProof : Bool
    repoContainsInternalVariationCalculation : Bool
    boundaryStatement : String

open EHDerivationBoundary public

canonicalEHDerivationBoundary : EHDerivationBoundary
canonicalEHDerivationBoundary =
  mkEHDerivationBoundary
    true
    false
    false
    false
    "the conditional chain is typed, while valuation-only uniqueness, Lovelock, and variational calculus remain external proof obligations"

canonicalValuationAloneDoesNotForceEH :
  valuationAloneForcesEHBasis canonicalEHDerivationBoundary ≡ false
canonicalValuationAloneDoesNotForceEH = refl
