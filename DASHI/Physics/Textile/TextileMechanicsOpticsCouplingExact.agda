module DASHI.Physics.Textile.TextileMechanicsOpticsCouplingExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Textile.StitchPhysicalFibreBridgeExact as Physical
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Mechanics/optics same-object weld.
--
-- The optical model is indexed by the exact same stitch topology carried by
-- the physical stitch state.  A consumer that wants deformation-dependent
-- appearance must additionally supply an explicit map from the mechanical
-- fibre into the optical transport state.
------------------------------------------------------------------------

record MechanicsConditionedOpticalRealisation
    {Scalar OpticalState Illumination OpticalObserver Radiance : Set}
    (physical : Physical.PhysicalStitchState Scalar)
    (model : Optical.TextileOpticalModel
      OpticalState
      Illumination
      OpticalObserver
      Radiance
      (Physical.topology physical)) : Set₁ where
  constructor mechanics-conditioned-optical-realisation
  field
    mechanicsToOpticalState :
      Physical.StitchMechanicalFibre Scalar → OpticalState

    currentOpticalState : OpticalState

    opticalStateRealisesCurrentMechanics :
      currentOpticalState
      ≡ mechanicsToOpticalState (Physical.mechanics physical)

open MechanicsConditionedOpticalRealisation public

record MechanicsAppearanceTransition
    {Scalar OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    (before after : Physical.PhysicalStitchState Scalar)
    (sameTopology : Physical.topology before ≡ topology)
    (afterSameTopology : Physical.topology after ≡ topology)
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor mechanics-appearance-transition
  field
    beforeRealisation :
      MechanicsConditionedOpticalRealisation
        before
        (subst
          (λ t → Optical.TextileOpticalModel
            OpticalState Illumination OpticalObserver Radiance t)
          (sym sameTopology)
          model)

    afterRealisation :
      MechanicsConditionedOpticalRealisation
        after
        (subst
          (λ t → Optical.TextileOpticalModel
            OpticalState Illumination OpticalObserver Radiance t)
          (sym afterSameTopology)
          model)

open MechanicsAppearanceTransition public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SameTopologyImpliesSameMechanicalOpticalState : Set where

sameTopologyDoesNotImplySameMechanicalOpticalState :
  SameTopologyImpliesSameMechanicalOpticalState → ⊥
sameTopologyDoesNotImplySameMechanicalOpticalState ()

data MechanicalStateDeterminesAppearanceWithoutOpticalCalibration : Set where

mechanicalStateDoesNotDetermineAppearanceWithoutOpticalCalibration :
  MechanicalStateDeterminesAppearanceWithoutOpticalCalibration → ⊥
mechanicalStateDoesNotDetermineAppearanceWithoutOpticalCalibration ()

data DrapeCoefficientDeterminesRadianceField : Set where

drapeCoefficientDoesNotDetermineRadianceField :
  DrapeCoefficientDeterminesRadianceField → ⊥
drapeCoefficientDoesNotDetermineRadianceField ()
