module DASHI.Physics.Materials.FangDainingInverseDesignSourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as F

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY COORDINATES
-- Ren et al., Journal of the Mechanics and Physics of Solids (2025),
-- DOI 10.1016/j.jmps.2025.106144.
-- Public publisher metadata/highlights pay the design objective and the
-- experimentally verified negative-group-velocity result, but not the complete
-- numerical energy functional, unit-cell geometry or band-structure arrays.
------------------------------------------------------------------------

record FangInverseDesignSourceReplay : Set where
  constructor fang-inverse-design-source-replay
  field
    sourceReference : String
    designMethod : String
    prescribedObjects : String
    wavevectorRegimes : String
    experimentalValidation : String
    negativeGroupVelocityVerified : Bool
    exactEnergyFunctionalPaid : Bool
    exactGeometryPaid : Bool
    exactBandStructureArrayPaid : Bool

open FangInverseDesignSourceReplay public

sourceExactFangInverseDesignReplay : FangInverseDesignSourceReplay
sourceExactFangInverseDesignReplay = fang-inverse-design-source-replay
  "DOI 10.1016/j.jmps.2025.106144"
  "force-field-induced energy-based design method for elastic metamaterials"
  "arbitrary prescribed eigenmodes and dispersions"
  "source reports design at both small and large wave vectors"
  "customized dispersion with negative group velocity verified by phonon-band-structure experiments"
  true
  false
  false
  false

existingFangScience : F.ActiveMechanicalMetamaterialScience
existingFangScience = F.fangActiveMechanicalMetamaterials

sourceReplayPaysNegativeGroupVelocityClaim : Bool
sourceReplayPaysNegativeGroupVelocityClaim = true

sourceReplayPaysExactEnergyMap : Bool
sourceReplayPaysExactEnergyMap = false

sourceReplayPaysUnknownMaterialProvenance : Bool
sourceReplayPaysUnknownMaterialProvenance = false
