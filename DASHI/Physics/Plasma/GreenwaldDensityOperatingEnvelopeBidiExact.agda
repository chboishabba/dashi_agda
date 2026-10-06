module DASHI.Physics.Plasma.GreenwaldDensityOperatingEnvelopeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement

------------------------------------------------------------------------
-- GREENWALD / DENSITY-LIMIT OPERATING ENVELOPE
--
-- The Greenwald fraction is represented as an empirical operating coordinate,
-- not a universal theorem.  Modern high-density results motivate carrying
-- profile, edge-collisionality, beta, wall and feedback coordinates separately.
------------------------------------------------------------------------

data DensityLimitModel : Set where
  greenwaldEmpiricalScaling : DensityLimitModel
  profileResolvedHighBetaScaling : DensityLimitModel
  collisionalityBetaScaling : DensityLimitModel
  wallFeedbackExtendedScaling : DensityLimitModel
  sourceSpecificDensityEnvelope : DensityLimitModel

record DensityOperatingEnvelope
    (state : Confinement.MagneticConfinementState) : Set₁ where
  constructor density-operating-envelope
  field
    model : DensityLimitModel
    lineAveragedDensity : SI.Measurement SI.Density SI.unitScale
    greenwaldFraction : SI.Measurement SI.Dimensionless SI.unitScale
    coreGreenwaldFraction : SI.Measurement SI.Dimensionless SI.unitScale
    pedestalGreenwaldFraction : SI.Measurement SI.Dimensionless SI.unitScale
    edgeCollisionality : SI.Measurement SI.Dimensionless SI.unitScale
    toroidalBeta : SI.Measurement SI.Dimensionless SI.unitScale

    currentProfileReceipt : Set
    pressureProfileReceipt : Set
    wallStabilizationReceipt : Set
    feedbackControlReceipt : Set
    edgeRadiationReceipt : Set
    divertorCompatibilityReceipt : Set
    disruptionAvoidanceReceipt : Set

    empiricalAuthority : Authority.ArtifactAuthorityBoundary
    sourceReference : String

open DensityOperatingEnvelope public

record ReactorDensityAdmissibility
    {state : Confinement.MagneticConfinementState}
    (envelope : DensityOperatingEnvelope state) : Set₁ where
  constructor reactor-density-admissibility
  field
    stableHighDensityReceipt : Set
    confinementAtDensityReceipt : Set
    impurityAndRadiationReceipt : Set
    exhaustAtDensityReceipt : Set
    fusionPowerAtDensityReceipt : Set
    sameRegimeTransferReceipt : Set
    reactorReference : String

open ReactorDensityAdmissibility public

record DensityLimitBoundary : Set where
  constructor density-limit-boundary
  field
    greenwaldScalingIsUniversalHardTheorem : Bool
    greenwaldScalingIsUniversalHardTheoremIsFalse :
      greenwaldScalingIsUniversalHardTheorem ≡ false

    lineAverageAboveGreenwaldAloneProvesReactorAdmissibility : Bool
    lineAverageAboveGreenwaldAloneProvesReactorAdmissibilityIsFalse :
      lineAverageAboveGreenwaldAloneProvesReactorAdmissibility ≡ false

    highDensityInOneDeviceTransfersWithoutRegimeReceipt : Bool
    highDensityInOneDeviceTransfersWithoutRegimeReceiptIsFalse :
      highDensityInOneDeviceTransfersWithoutRegimeReceipt ≡ false

    coreAndPedestalDensityShouldRemainDistinct : Bool
    coreAndPedestalDensityShouldRemainDistinctIsTrue :
      coreAndPedestalDensityShouldRemainDistinct ≡ true

    densityLimitSearchMayUseCollisionalityBetaWallAndFeedback : Bool
    densityLimitSearchMayUseCollisionalityBetaWallAndFeedbackIsTrue :
      densityLimitSearchMayUseCollisionalityBetaWallAndFeedback ≡ true

canonicalDensityLimitBoundary : DensityLimitBoundary
canonicalDensityLimitBoundary =
  density-limit-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
