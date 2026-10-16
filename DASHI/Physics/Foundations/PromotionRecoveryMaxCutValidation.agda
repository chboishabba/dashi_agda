module DASHI.Physics.Foundations.PromotionRecoveryMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1SU2
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as BalabanC3
import DASHI.Physics.Foundations.ContinuousSO3Torque369BridgeExact as Continuous

------------------------------------------------------------------------
-- RED-first contract for the promotion/recovery max-cut.
------------------------------------------------------------------------

u1LieRestrictionActuallyAbelian : U1SU2.u1EmbeddedBracketVanishes ≡ true
u1LieRestrictionActuallyAbelian = refl

u1RestrictionLivesInsideSU2YangMillsGeometry :
  U1SU2.u1IsSU2LieSubalgebra ≡ true
u1RestrictionLivesInsideSU2YangMillsGeometry = refl

nonAbelianClayMassGapStillNotMaxwellPhenomenology :
  U1SU2.clayMassGapAutomaticallyProvesMaxwell ≡ false
nonAbelianClayMassGapStillNotMaxwellPhenomenology = refl

balabanCMP109HasLiteralSpatialC3 :
  BalabanC3.cmp109LiteralSpatialC3Recovered ≡ true
balabanCMP109HasLiteralSpatialC3 = refl

balabanC3ComesFromSourceCoordinateCovariance :
  BalabanC3.cmp109C3SourceBacked ≡ true
balabanC3ComesFromSourceCoordinateCovariance = refl

unifiedBalabanRecoveryStillNeedsTransport :
  BalabanC3.unifiedRecoveryC3TransportClosed ≡ false
unifiedBalabanRecoveryStillNeedsTransport = refl

continuousSO3ConventionAlreadyReused :
  Continuous.existingSO3ContinuousConventionReused ≡ true
continuousSO3ConventionAlreadyReused = refl

finite369OrientationNotMistakenForContinuousSO3 :
  Continuous.finiteOrientationIsContinuousRotation ≡ false
finite369OrientationNotMistakenForContinuousSO3 = refl
