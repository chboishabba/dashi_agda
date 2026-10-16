module DASHI.Physics.QuantumVacuum.CasimirSetoidFullStressSameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact as BrownMaclay
import DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact as Normalized
import DASHI.Physics.QuantumVacuum.CasimirSetoidAnalyticScalarExact as Setoid
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress3
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- SETOID-NATIVE FULL CASIMIR STRESS SAME-OBJECT MAX-CUT
--
-- The existing Casimir analytic route already owns a concrete imported Bishop
-- setoid real backend, while the older CasimirScalarModel remains an abstract
-- propositional-equality carrier.  Do not force the QFT stress back through
-- that still-open quotient seam.
--
-- Instead, this owner lifts the already source-bounded Brown-Maclay normalized
-- fingerprint to a full 4 x 4 diagonal stress object on the SAME setoid scalar
-- model used by the analytic Casimir lane.  Its spatial block literally uses
-- the existing SO(3)-style 3 x 3 operator sheet.
--
-- The only scalar payment needed to make the lift physical on a given model
-- and plate separation is the positive Casimir scale C on that same carrier,
-- together with the two observable identities
--
--   E/A = (-C) d
--   pressure = -3 C.
--
-- These are stronger and less ambiguous than an arbitrary rational scale map.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Full normalized 4 x 4 Brown-Maclay carrier.
------------------------------------------------------------------------

data CasimirFrameDirection : Set where
  time : CasimirFrameDirection
  space : Stress3.PlateDirection → CasimirFrameDirection

normalizedSpatialComponent :
  Stress3.PlateDirection →
  Stress3.PlateDirection →
  ℚ
normalizedSpatialComponent output input =
  Normalized.brownMaclayNormalizedSpatialStress
    (Stress3.plateDirectionToAxis output , Stress3.plateDirectionToAxis input)

normalizedSpacetimeStress :
  CasimirFrameDirection →
  CasimirFrameDirection →
  ℚ
normalizedSpacetimeStress time time = Normalized.normalizedEnergyDensity
normalizedSpacetimeStress time (space direction) = 0ℚ
normalizedSpacetimeStress (space direction) time = 0ℚ
normalizedSpacetimeStress (space output) (space input) =
  normalizedSpatialComponent output input

------------------------------------------------------------------------
-- 2. Minimal same-carrier scale payment.
------------------------------------------------------------------------

triple :
  ∀ {model : Setoid.CasimirSetoidScalarModel} →
  Spine.Carrier (Setoid.real model) →
  Spine.Carrier (Setoid.real model)
triple {model} value =
  Spine._+_ (Setoid.real model)
    value
    (Spine._+_ (Setoid.real model) value value)

record CasimirSetoidScaleWitness
    (model : Setoid.CasimirSetoidScalarModel)
    (d : Q.Length) : Set₁ where
  field
    casimirScale : Spine.Carrier (Setoid.real model)

    scalePositive :
      Spine._<_ (Setoid.real model)
        (Spine.zero (Setoid.real model))
        casimirScale

    energyPerAreaIsNegativeDensityTimesSeparation :
      Spine._≈_ (Setoid.real model)
        (Setoid.energyPerArea model d)
        (Spine._*_ (Setoid.real model)
          (Spine.neg (Setoid.real model) casimirScale)
          (Setoid.lengthValue model d))

    pressureIsMinusThreeScale :
      Spine._≈_ (Setoid.real model)
        (Setoid.pressure model d)
        (Spine.neg (Setoid.real model) (triple casimirScale))

    scaleReading : String

open CasimirSetoidScaleWitness public

------------------------------------------------------------------------
-- 3. Full stress on that same setoid scalar object.
------------------------------------------------------------------------

setoidSpatialComponent :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  CasimirSetoidScaleWitness model d →
  Stress3.PlateDirection →
  Stress3.PlateDirection →
  Spine.Carrier (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.tangentOne Stress3.tangentOne =
  casimirScale scale
setoidSpatialComponent {model} scale Stress3.tangentOne Stress3.tangentTwo =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.tangentOne Stress3.normal =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.tangentTwo Stress3.tangentOne =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.tangentTwo Stress3.tangentTwo =
  casimirScale scale
setoidSpatialComponent {model} scale Stress3.tangentTwo Stress3.normal =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.normal Stress3.tangentOne =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.normal Stress3.tangentTwo =
  Spine.zero (Setoid.real model)
setoidSpatialComponent {model} scale Stress3.normal Stress3.normal =
  Spine.neg (Setoid.real model) (triple (casimirScale scale))

setoidSpatialStress :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  CasimirSetoidScaleWitness model d →
  Stress3.SpatialStressSheet (Spine.Carrier (Setoid.real model))
setoidSpatialStress scale (output , input) =
  setoidSpatialComponent scale
    (Stress3.axisToPlateDirection output)
    (Stress3.axisToPlateDirection input)

setoidEnergyDensity :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  CasimirSetoidScaleWitness model d →
  Spine.Carrier (Setoid.real model)
setoidEnergyDensity {model} scale =
  Spine.neg (Setoid.real model) (casimirScale scale)

setoidSpacetimeStress :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  CasimirSetoidScaleWitness model d →
  CasimirFrameDirection →
  CasimirFrameDirection →
  Spine.Carrier (Setoid.real model)
setoidSpacetimeStress scale time time = setoidEnergyDensity scale
setoidSpacetimeStress {model} scale time (space direction) =
  Spine.zero (Setoid.real model)
setoidSpacetimeStress {model} scale (space direction) time =
  Spine.zero (Setoid.real model)
setoidSpacetimeStress scale (space output) (space input) =
  setoidSpatialComponent scale output input

setoidNormalPressure :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  CasimirSetoidScaleWitness model d →
  Spine.Carrier (Setoid.real model)
setoidNormalPressure scale =
  Stress3.normalPressure (setoidSpatialStress scale)

setoidNormalPressureIsMinusThreeScale :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  (scale : CasimirSetoidScaleWitness model d) →
  setoidNormalPressure scale
  ≡ Spine.neg (Setoid.real model) (triple (casimirScale scale))
setoidNormalPressureIsMinusThreeScale scale = refl

setoidNormalPressureAgreesWithModel :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  (scale : CasimirSetoidScaleWitness model d) →
  Spine._≈_ (Setoid.real model)
    (setoidNormalPressure scale)
    (Setoid.pressure model d)
setoidNormalPressureAgreesWithModel {model} scale =
  Spine.≈-sym (Setoid.real model)
    (pressureIsMinusThreeScale scale)

------------------------------------------------------------------------
-- 4. Source-bounded theory-level full-stress reconstruction.
------------------------------------------------------------------------

record CasimirSetoidFullStressReconstruction
    (model : Setoid.CasimirSetoidScalarModel)
    (d : Q.Length) : Set₁ where
  field
    scaleWitness : CasimirSetoidScaleWitness model d
    sourceAuthority : BrownMaclay.BrownMaclayParallelPlateAuthority

    sourceIsIdealConductingPlateSystem :
      BrownMaclay.perfectConductingParallelPlates sourceAuthority
    sourcePaysFiniteVacuumStress :
      BrownMaclay.zeroTemperatureFiniteStress sourceAuthority

    sameIdealPlateObjectAsAnalyticModel : Set
    sameSeparationParameterAsAnalyticModel : Set
    sameRenormalizedExpectationObject : Set

    reconstructionReading : String

open CasimirSetoidFullStressReconstruction public

fullStress :
  ∀ {model d} →
  CasimirSetoidFullStressReconstruction model d →
  CasimirFrameDirection →
  CasimirFrameDirection →
  Spine.Carrier (Setoid.real model)
fullStress reconstruction =
  setoidSpacetimeStress (scaleWitness reconstruction)

fullStressNormalPressureAgreesWithAnalyticPressure :
  ∀ {model d} →
  (reconstruction : CasimirSetoidFullStressReconstruction model d) →
  Spine._≈_ (Setoid.real model)
    (fullStress reconstruction
      (space Stress3.normal)
      (space Stress3.normal))
    (Setoid.pressure model d)
fullStressNormalPressureAgreesWithAnalyticPressure reconstruction =
  setoidNormalPressureAgreesWithModel (scaleWitness reconstruction)

------------------------------------------------------------------------
-- 5. This pays theory-object construction, not experiment or GR.
------------------------------------------------------------------------

data SourceBackedStressAutomaticallyIsMeasuredStress : Set where
data SetoidQFTStressAutomaticallySolvesSemiclassicalGR : Set where
data SetoidStressAutomaticallySuppliesLegacyQuotient : Set where

sourceBackedStressIsNotMeasuredStress :
  SourceBackedStressAutomaticallyIsMeasuredStress → ⊥
sourceBackedStressIsNotMeasuredStress ()

setoidQFTStressDoesNotSolveGR :
  SetoidQFTStressAutomaticallySolvesSemiclassicalGR → ⊥
setoidQFTStressDoesNotSolveGR ()

setoidStressDoesNotCreateLegacyQuotient :
  SetoidStressAutomaticallySuppliesLegacyQuotient → ⊥
setoidStressDoesNotCreateLegacyQuotient ()

------------------------------------------------------------------------
-- 6. Machine-readable max-cut status.
------------------------------------------------------------------------

record CasimirSetoidFullStressBoundary : Set where
  constructor casimir-setoid-full-stress-boundary
  field
    normalizedFull4x4CarrierOwned : Bool
    spatialBlockUsesSO3NineSheet : Bool
    setoidSameCarrierScaleInterfaceOwned : Bool
    energyPerAreaDensitySameObjectEqualityRequired : Bool
    normalPressureSameObjectEqualityRequired : Bool
    fullSetoidStressReconstructionOwned : Bool

    concreteScaleWitnessForCanonicalBishopCasimirModelPaid : Bool
    propositionalLegacyQuotientPaid : Bool
    directStressMeasurementPaid : Bool
    semiclassicalGRBackreactionPaid : Bool

open CasimirSetoidFullStressBoundary public

canonicalCasimirSetoidFullStressBoundary : CasimirSetoidFullStressBoundary
canonicalCasimirSetoidFullStressBoundary =
  casimir-setoid-full-stress-boundary
    true true true true true true
    false false false false

casimirSetoidFullStressReading : String
casimirSetoidFullStressReading =
  "The Brown-Maclay ideal-plate fingerprint is now represented as a full 4x4 QFT stress object on the same setoid scalar carrier as the Casimir analytic model. Its spatial block is the existing SO(3) 3x3 operator sheet. A concrete positive scale witness at the same plate separation ties E/A=(-C)d and T_nn=-3C to the analytic model pressure. No propositional quotient, direct stress measurement, or semiclassical gravitational backreaction is inferred."
