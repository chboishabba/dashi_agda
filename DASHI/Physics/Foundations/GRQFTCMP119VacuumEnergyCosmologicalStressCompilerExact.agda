{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119VacuumEnergyCosmologicalStressCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Source
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119

------------------------------------------------------------------------
-- SOURCE-NATIVE VACUUM ENERGY -> COSMOLOGICAL STRESS COMPILER
--
-- Existing owners provide the two halves:
--
--   CMP119 source-native state:
--     vacuumEnergy : Nat -> Vacuum
--
--   symbolic Einstein-Hilbert variation:
--     vacuumDensity -> cosmologicalTensorTerm.
--
-- Once a rational readout supplies the coefficient, the normalized rational
-- GRQFT convention represents that cosmological source by
--
--     T_mu_nu(lambda) = -lambda g_mu_nu.
--
-- This module transports the SOURCE-NATIVE vacuum coefficients into that
-- already-constructed stress ray.  It does not claim the symbolic-EH module
-- internally proves continuum metric variation.
------------------------------------------------------------------------

symbolicVacuumVariationShape :
  EH.varyInvariant EH.vacuumDensity ≡ EH.cosmologicalTensorTerm
symbolicVacuumVariationShape =
  EH.vacuumVariationIsCosmological

sourceVacuumStress :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier} →
  Source.SourceNativeNambuVacuumAmplitudeReceipt source →
  Nat →
  Stress.RationalTensor4
sourceVacuumStress {source = source} receipt scale =
  Vacuum.vacuumStressAt
    (Source.vacuumToRat (Source.readout receipt)
      (CMP119.vacuumEnergy source scale))

sourceInteriorVacuumStress :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier} →
  Source.SourceNativeNambuVacuumAmplitudeReceipt source →
  Stress.RationalTensor4
sourceInteriorVacuumStress receipt =
  sourceVacuumStress receipt (Source.interiorScale receipt)

sourceExteriorVacuumStress :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier} →
  Source.SourceNativeNambuVacuumAmplitudeReceipt source →
  Stress.RationalTensor4
sourceExteriorVacuumStress receipt =
  sourceVacuumStress receipt (Source.exteriorScale receipt)

sourceInteriorStressIsSelectedAmplitude :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier}
    (receipt : Source.SourceNativeNambuVacuumAmplitudeReceipt source) →
  (a b : Flat.Axis4) →
  sourceInteriorVacuumStress receipt a b
    ≡ Vacuum.vacuumStressAt (Int.+ 21 / 64) a b
sourceInteriorStressIsSelectedAmplitude receipt a b =
  cong
    (λ amplitude → Vacuum.vacuumStressAt amplitude a b)
    (Source.interiorAmplitude receipt)

sourceExteriorStressIsSelectedAmplitude :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier}
    (receipt : Source.SourceNativeNambuVacuumAmplitudeReceipt source) →
  (a b : Flat.Axis4) →
  sourceExteriorVacuumStress receipt a b
    ≡ Vacuum.vacuumStressAt (Int.+ 19 / 48) a b
sourceExteriorStressIsSelectedAmplitude receipt a b =
  cong
    (λ amplitude → Vacuum.vacuumStressAt amplitude a b)
    (Source.exteriorAmplitude receipt)

record SourceNativeVacuumCosmologicalStressCompiler
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier}
    (receipt : Source.SourceNativeNambuVacuumAmplitudeReceipt source) : Set where
  constructor source-native-vacuum-cosmological-stress-compiler
  field
    symbolicVariationShape :
      EH.varyInvariant EH.vacuumDensity ≡ EH.cosmologicalTensorTerm

    interiorStress :
      (a b : Flat.Axis4) →
      sourceInteriorVacuumStress receipt a b
        ≡ Vacuum.vacuumStressAt (Int.+ 21 / 64) a b

    exteriorStress :
      (a b : Flat.Axis4) →
      sourceExteriorVacuumStress receipt a b
        ≡ Vacuum.vacuumStressAt (Int.+ 19 / 48) a b

open SourceNativeVacuumCosmologicalStressCompiler public

sourceNativeVacuumCosmologicalStressCompiler :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier} →
  (receipt : Source.SourceNativeNambuVacuumAmplitudeReceipt source) →
  SourceNativeVacuumCosmologicalStressCompiler receipt
sourceNativeVacuumCosmologicalStressCompiler receipt =
  source-native-vacuum-cosmological-stress-compiler
    EH.vacuumVariationIsCosmological
    (sourceInteriorStressIsSelectedAmplitude receipt)
    (sourceExteriorStressIsSelectedAmplitude receipt)

record SourceNativeVacuumCosmologicalStressBoundary : Set where
  constructor source-native-vacuum-cosmological-stress-boundary
  field
    vacuumVariationShapeAlreadyOwned : Bool
    coefficientTransportToStressRayConstructed : Bool
    independentCosmologicalTensorShapeTheoremRequired : Bool
    sourceNativeVacuumReadoutStillRequired : Bool
    sourceNativeTwoScaleValuesStillRequired : Bool
    continuumTensorVariationInternallyDerived : Bool

canonicalSourceNativeVacuumCosmologicalStressBoundary :
  SourceNativeVacuumCosmologicalStressBoundary
canonicalSourceNativeVacuumCosmologicalStressBoundary =
  source-native-vacuum-cosmological-stress-boundary
    true true false true true false
