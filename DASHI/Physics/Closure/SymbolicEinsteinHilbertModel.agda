module DASHI.Physics.Closure.SymbolicEinsteinHilbertModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Base369 using (TriTruth; tri-mid)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.EinsteinHilbertVariationConditional as Conditional

------------------------------------------------------------------------
-- Internal symbolic normal form for the supplied Lovelock conclusion.
--
-- This module does not prove Lovelock classification.  It makes the output of
-- that classification executable: at the metric+diffeomorphism+two-jet depth,
-- the leading bulk basis contains the vacuum-density and Ricci-scalar terms;
-- total divergences have no bulk Euler-Lagrange term; higher-curvature terms
-- are outside the selected leading basis.


data GeometricInvariant : Set where
  vacuumDensity : GeometricInvariant
  ricciScalarDensity : GeometricInvariant
  boundaryDivergence : GeometricInvariant
  higherCurvatureDensity : GeometricInvariant


data LeadingBulkInvariant : GeometricInvariant → Set where
  admitVacuumDensity : LeadingBulkInvariant vacuumDensity
  admitRicciScalar : LeadingBulkInvariant ricciScalarDensity

vacuumDensityIsLeading : LeadingBulkInvariant vacuumDensity
vacuumDensityIsLeading = admitVacuumDensity

ricciScalarIsLeading : LeadingBulkInvariant ricciScalarDensity
ricciScalarIsLeading = admitRicciScalar

boundaryIsNotLeadingBulk : LeadingBulkInvariant boundaryDivergence → ⊥
boundaryIsNotLeadingBulk ()

higherCurvatureIsNotLeadingBulk :
  LeadingBulkInvariant higherCurvatureDensity → ⊥
higherCurvatureIsNotLeadingBulk ()

record EHLeadingBasisReceipt : Set where
  constructor mkEHLeadingBasisReceipt
  field
    vacuumTermReceipt : LeadingBulkInvariant vacuumDensity
    ricciTermReceipt : LeadingBulkInvariant ricciScalarDensity
    basisScope : String

open EHLeadingBasisReceipt public

symbolicEHLeadingBasisReceipt : EHLeadingBasisReceipt
symbolicEHLeadingBasisReceipt =
  mkEHLeadingBasisReceipt
    admitVacuumDensity
    admitRicciScalar
    "symbolic normal form conditional on the supplied Lovelock classification"

------------------------------------------------------------------------
-- Symbolic metric variation.


data BulkVariation : Set where
  cosmologicalTensorTerm : BulkVariation
  EinsteinTensorTerm : BulkVariation
  zeroBulkBoundaryTerm : BulkVariation
  higherVariationBlocked : BulkVariation

varyInvariant : GeometricInvariant → BulkVariation
varyInvariant vacuumDensity = cosmologicalTensorTerm
varyInvariant ricciScalarDensity = EinsteinTensorTerm
varyInvariant boundaryDivergence = zeroBulkBoundaryTerm
varyInvariant higherCurvatureDensity = higherVariationBlocked

vacuumVariationIsCosmological :
  varyInvariant vacuumDensity ≡ cosmologicalTensorTerm
vacuumVariationIsCosmological = refl

ricciVariationIsEinstein :
  varyInvariant ricciScalarDensity ≡ EinsteinTensorTerm
ricciVariationIsEinstein = refl

boundaryVariationHasNoBulkTerm :
  varyInvariant boundaryDivergence ≡ zeroBulkBoundaryTerm
boundaryVariationHasNoBulkTerm = refl

higherCurvatureVariationRemainsBlocked :
  varyInvariant higherCurvatureDensity ≡ higherVariationBlocked
higherCurvatureVariationRemainsBlocked = refl

record SymbolicEHVariationReceipt : Set where
  constructor mkSymbolicEHVariationReceipt
  field
    vacuumVariationReceipt :
      varyInvariant vacuumDensity ≡ cosmologicalTensorTerm
    ricciVariationReceipt :
      varyInvariant ricciScalarDensity ≡ EinsteinTensorTerm
    boundaryVariationReceipt :
      varyInvariant boundaryDivergence ≡ zeroBulkBoundaryTerm
    higherVariationBoundary :
      varyInvariant higherCurvatureDensity ≡ higherVariationBlocked
    variationScope : String

open SymbolicEHVariationReceipt public

symbolicEHVariationReceipt : SymbolicEHVariationReceipt
symbolicEHVariationReceipt =
  mkSymbolicEHVariationReceipt
    refl refl refl refl
    "symbolic Euler-Lagrange target; not an internal tensor-calculus derivation"

------------------------------------------------------------------------
-- Concrete flat-vacuum realization.

flatRicciTensor : Flat.Axis4 → Flat.Axis4 → TriTruth
flatRicciTensor _ _ = tri-mid

flatEinsteinTensor : Flat.Axis4 → Flat.Axis4 → TriTruth
flatEinsteinTensor _ _ = tri-mid

flatCosmologicalTensorAtZeroLambda :
  Flat.Axis4 → Flat.Axis4 → TriTruth
flatCosmologicalTensorAtZeroLambda _ _ = tri-mid

flatVacuumEquationLeft : Flat.Axis4 → Flat.Axis4 → TriTruth
flatVacuumEquationLeft _ _ = tri-mid

flatRicciIsZero :
  (a b : Flat.Axis4) → flatRicciTensor a b ≡ tri-mid
flatRicciIsZero _ _ = refl

flatEinsteinIsZero :
  (a b : Flat.Axis4) → flatEinsteinTensor a b ≡ tri-mid
flatEinsteinIsZero _ _ = refl

flatZeroLambdaTermIsZero :
  (a b : Flat.Axis4) →
  flatCosmologicalTensorAtZeroLambda a b ≡ tri-mid
flatZeroLambdaTermIsZero _ _ = refl

flatVacuumEquationHolds :
  (a b : Flat.Axis4) → flatVacuumEquationLeft a b ≡ tri-mid
flatVacuumEquationHolds _ _ = refl

record FlatVacuumEinsteinReceipt : Set where
  constructor mkFlatVacuumEinsteinReceipt
  field
    metricReceipt : Flat.FlatLorentzianMetricReceipt
    connectionReceipt : Flat.FlatLeviCivitaReceipt
    RicciZeroReceipt :
      (a b : Flat.Axis4) → flatRicciTensor a b ≡ tri-mid
    EinsteinZeroReceipt :
      (a b : Flat.Axis4) → flatEinsteinTensor a b ≡ tri-mid
    zeroLambdaReceipt :
      (a b : Flat.Axis4) →
      flatCosmologicalTensorAtZeroLambda a b ≡ tri-mid
    vacuumEquationReceipt :
      (a b : Flat.Axis4) → flatVacuumEquationLeft a b ≡ tri-mid
    modelScope : String

open FlatVacuumEinsteinReceipt public

flatVacuumEinsteinReceipt : FlatVacuumEinsteinReceipt
flatVacuumEinsteinReceipt =
  mkFlatVacuumEinsteinReceipt
    Flat.flatLorentzianMetricReceipt
    Flat.flatLeviCivitaReceipt
    flatRicciIsZero
    flatEinsteinIsZero
    flatZeroLambdaTermIsZero
    flatVacuumEquationHolds
    "exact finite flat-vacuum model at zero cosmological term"

------------------------------------------------------------------------
-- Adapter to the conditional action ladder.

conditionalBasisReceipt :
  Conditional.EinsteinHilbertBasisReceipt
    Conditional.canonicalConditionalEHBasis
conditionalBasisReceipt =
  Conditional.canonicalConditionalEHBasisReceipt

conditionalEinsteinEquationReceipt :
  Conditional.EinsteinEquationReceipt
    Conditional.canonicalConditionalEHBasis
    Conditional.canonicalConditionalEHBasisReceipt
    Conditional.canonicalConditionalEHVariation
conditionalEinsteinEquationReceipt =
  Conditional.canonicalConditionalEinsteinEquationReceipt
