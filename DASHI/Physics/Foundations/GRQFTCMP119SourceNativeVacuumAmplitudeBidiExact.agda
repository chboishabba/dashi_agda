{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119

------------------------------------------------------------------------
-- SOURCE-NATIVE VACUUM-AMPLITUDE BIDI SURFACE
--
-- The literal CMP119 source state already owns
--
--   vacuumEnergy : Nat -> Vacuum
--   effectiveAction : Nat -> Action
--   equation223
--
-- on ONE scale-indexed state.
--
-- The missing GRQFT datum is therefore not a new effective action.  It is a
-- rational readout of the existing vacuum-energy object plus two scales on the
-- same state with the required amplitudes.
------------------------------------------------------------------------

record VacuumEnergyRationalReadout
    (Vacuum : Set) : Set₁ where
  field
    vacuumToRat : Vacuum → ℚ

open VacuumEnergyRationalReadout public

record SourceNativeNambuVacuumAmplitudeReceipt
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) : Set₁ where
  constructor source-native-nambu-vacuum-amplitude-receipt
  field
    readout :
      VacuumEnergyRationalReadout Vacuum

    interiorScale : Nat
    exteriorScale : Nat

    interiorAmplitude :
      vacuumToRat readout
        (CMP119.vacuumEnergy source interiorScale)
      ≡ Int.+ 21 / 64

    exteriorAmplitude :
      vacuumToRat readout
        (CMP119.vacuumEnergy source exteriorScale)
      ≡ Int.+ 19 / 48

open SourceNativeNambuVacuumAmplitudeReceipt public

------------------------------------------------------------------------
-- The effective-action attachment at each selected scale is compiler-owned
-- from the same source state through equation223.
------------------------------------------------------------------------

interiorEffectiveActionEquation223 :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  SourceNativeNambuVacuumAmplitudeReceipt source →
  CMP119.effectiveAction source
    (interiorScale _)
  ≡ CMP119.assemble (CMP119.actionAlgebra source)
      (CMP119.wilsonCoefficient source (interiorScale _))
      (CMP119.wilsonActionTerm source (interiorScale _))
      (CMP119.regularSmallFieldTerm source (interiorScale _))
      (CMP119.rOperationTerm source (interiorScale _))
      (CMP119.boundaryTerm source (interiorScale _))
      (CMP119.vacuumEnergy source (interiorScale _))
interiorEffectiveActionEquation223 {source = source} receipt =
  CMP119.equation223 source (interiorScale receipt)

exteriorEffectiveActionEquation223 :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source :
      CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  SourceNativeNambuVacuumAmplitudeReceipt source →
  CMP119.effectiveAction source
    (exteriorScale _)
  ≡ CMP119.assemble (CMP119.actionAlgebra source)
      (CMP119.wilsonCoefficient source (exteriorScale _))
      (CMP119.wilsonActionTerm source (exteriorScale _))
      (CMP119.regularSmallFieldTerm source (exteriorScale _))
      (CMP119.rOperationTerm source (exteriorScale _))
      (CMP119.boundaryTerm source (exteriorScale _))
      (CMP119.vacuumEnergy source (exteriorScale _))
exteriorEffectiveActionEquation223 {source = source} receipt =
  CMP119.equation223 source (exteriorScale receipt)

------------------------------------------------------------------------
-- MAX-CUT BOUNDARY
------------------------------------------------------------------------

record SourceNativeVacuumAmplitudeBoundary : Set where
  constructor source-native-vacuum-amplitude-boundary
  field
    sourceAlreadyOwnsScaleIndexedVacuumEnergy : Bool
    sourceAlreadyOwnsEffectiveActionEquation223 : Bool
    independentEffectiveActionWeldRequired : Bool
    rationalVacuumEnergyReadoutExistsInRepo : Bool
    twoRequiredSourceNativeVacuumValuesProved : Bool
    remainingLeafIsReadoutPlusTwoScaleValues : Bool

canonicalSourceNativeVacuumAmplitudeBoundary :
  SourceNativeVacuumAmplitudeBoundary
canonicalSourceNativeVacuumAmplitudeBoundary =
  source-native-vacuum-amplitude-boundary
    true true false false false true
