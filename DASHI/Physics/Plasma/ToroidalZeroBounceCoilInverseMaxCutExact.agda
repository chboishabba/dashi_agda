module DASHI.Physics.Plasma.ToroidalZeroBounceCoilInverseMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceArchitectureForkExact as Fork
import DASHI.Physics.Plasma.ToroidalZeroBounceCoilInverseBoundaryExact as Coil
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

record CoilInverseMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor coil-inverse-max-cut
  field
    architectureFork : Fork.ArchitectureForkReceipt population
    target : Coil.CoilInverseTarget population
    currentPotential : Coil.WindingSurfaceCurrentPotentialReceipt population target
    sparseSupportPassedToCoilStageReceipt : Set
    c3ExternalTransformBranchReceipt : Set
    normalFieldReductionReceipt : Set
    filamentExtractionReceipt : Set
    freeBoundaryEquilibriumStillRequiredReceipt : Set
    fullGuidingCentreOrbitReplayStillRequiredReceipt : Set
    kineticStabilityStillRequiredReceipt : Set
    bestKnownReferenceReplayStillRequiredReceipt : Set
    maxCutReference : String

open CoilInverseMaxCut public

record CoilInverseMaxCutBoundary : Set where
  constructor coil-inverse-max-cut-boundary
  field
    toyCurrentSheetResidualProvesEngineeringCoils : Bool
    toyCurrentSheetResidualProvesEngineeringCoilsIsFalse :
      toyCurrentSheetResidualProvesEngineeringCoils ≡ false
    filamentContoursAreFinalWindingPack : Bool
    filamentContoursAreFinalWindingPackIsFalse :
      filamentContoursAreFinalWindingPack ≡ false
    stageTwoInverseIsUsefulBeforeFullFreeBoundaryReplay : Bool
    stageTwoInverseIsUsefulBeforeFullFreeBoundaryReplayIsTrue :
      stageTwoInverseIsUsefulBeforeFullFreeBoundaryReplay ≡ true
    fullFreeBoundaryAndOrbitReplayRemainHardGate : Bool
    fullFreeBoundaryAndOrbitReplayRemainHardGateIsTrue :
      fullFreeBoundaryAndOrbitReplayRemainHardGate ≡ true

canonicalCoilInverseMaxCutBoundary : CoilInverseMaxCutBoundary
canonicalCoilInverseMaxCutBoundary =
  coil-inverse-max-cut-boundary false refl false refl true refl true refl

localProbeReference : String
localProbeReference =
  "2026-10-07 local normalized winding-surface current-potential probe: regularized C3 Fourier current sheet reduced target normal-field RMS to about 9.4 percent of uncorrected leakage and yielded 27 contour segments; exploratory only."
