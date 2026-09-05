module DASHI.Physics.Plasma.MHDHelicalElsasserTriadHypervoxelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMBINED HELICAL / ELSASSER TRIAD HYPERVOXEL
--
-- The helical sign and Elsasser orientation are independent coordinates.
-- This owner keeps them distinct on each wavevector slot and separates
-- momentum from induction channels rather than flattening the MHD nonlinearity.
------------------------------------------------------------------------

data BinarySign : Set where
  plus minus : BinarySign

data InteractionChannel : Set where
  velocityVelocity
  magneticMagnetic
  velocityMagnetic
  magneticVelocity
  : InteractionChannel

data EquationSector : Set where
  momentumSector inductionSector : EquationSector

record WaveSlot : Set₁ where
  constructor wave-slot
  field
    Wavevector Radius Amplitude : Set
    helicitySign : BinarySign
    elsasserOrientation : BinarySign
    slotReference : String

open WaveSlot public

record MHDHelicalElsasserTriadHypervoxel : Set₁ where
  constructor mhd-helical-elsasser-triad-hypervoxel
  field
    kSlot pSlot qSlot : WaveSlot
    triadClosure : Set
    geometricTripleProduct : Set
    channel : InteractionChannel
    equationSector : EquationSector
    coefficient : Set
    amplitudeProduct : Set
    sameTriadObject : Set
    hypervoxelReference : String

open MHDHelicalElsasserTriadHypervoxel public

record CombinedAxisBoundary : Set where
  constructor combined-axis-boundary
  field
    helicitySignDeterminesElsasserOrientation : Bool
    helicitySignDeterminesElsasserOrientationIsFalse :
      helicitySignDeterminesElsasserOrientation ≡ false

    elsasserOrientationDeterminesHelicitySign : Bool
    elsasserOrientationDeterminesHelicitySignIsFalse :
      elsasserOrientationDeterminesHelicitySign ≡ false

    momentumSectorIsInductionSector : Bool
    momentumSectorIsInductionSectorIsFalse :
      momentumSectorIsInductionSector ≡ false

canonicalCombinedAxisBoundary : CombinedAxisBoundary
canonicalCombinedAxisBoundary =
  combined-axis-boundary false refl false refl false refl
