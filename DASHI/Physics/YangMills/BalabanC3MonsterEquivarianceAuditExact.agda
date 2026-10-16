module DASHI.Physics.YangMills.BalabanC3MonsterEquivarianceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Monster369
import DASHI.Physics.YangMills.BalabanActiveSourceDiscriminator2026Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as CMP109C3

------------------------------------------------------------------------
-- YM / BASE369-MONSTER C3 AUDIT
--
-- Updated after recovering a literal source-backed order-three action from
-- Balaban CMP109 coordinate-permutation covariance.  The old categorical
-- statement "Balaban has no literal C3 action" is no longer correct.
--
-- What is now paid:
--   * an exact order-three spatial action on the literal generated CMP109 grid;
--   * same-grid scalar-projection equivariance under the source symmetry.
--
-- What remains unpaid:
--   * transport of that action through the later density -> repository state ->
--     BC1/BC2 action -> localized D1 -> stress -> Schwinger recovery spine;
--   * a C3 action on the full physical gauge-field variables of that compiler;
--   * dexp/stress equivariance on those same objects.
------------------------------------------------------------------------

monster369ExactC3TemplateAvailable : Bool
monster369ExactC3TemplateAvailable = true

balabanLiteralC3ActionRecovered : Bool
balabanLiteralC3ActionRecovered = CMP109C3.cmp109LiteralSpatialC3Recovered

balabanCMP109SpatialSourceC3Recovered : Bool
balabanCMP109SpatialSourceC3Recovered = CMP109C3.cmp109LiteralSpatialC3Recovered

balabanC3ActionOnSourceSeamsRecovered : Bool
balabanC3ActionOnSourceSeamsRecovered = false

balabanC3ActionOnPhysicalFieldsRecovered : Bool
balabanC3ActionOnPhysicalFieldsRecovered = false

balabanC3EquivarianceOfDexpOrStressRecovered : Bool
balabanC3EquivarianceOfDexpOrStressRecovered = false

balabanLiteralC3ActionRecoveredIsTrue : balabanLiteralC3ActionRecovered ≡ true
balabanLiteralC3ActionRecoveredIsTrue = refl

balabanUnifiedRecoveryC3TransportStillOpen :
  CMP109C3.unifiedRecoveryC3TransportClosed ≡ false
balabanUnifiedRecoveryC3TransportStillOpen = refl

record BalabanLiteralC3Realisation : Set₁ where
  field
    PhysicalCarrier : Set
    SourceCarrier : Set
    RecoveryCarrier : Set

    physicalAction : C3.OrderThreeAction PhysicalCarrier
    sourceAction : C3.OrderThreeAction SourceCarrier
    recoveryAction : C3.OrderThreeAction RecoveryCarrier

    sourceFromPhysical : PhysicalCarrier → SourceCarrier
    recover : SourceCarrier → RecoveryCarrier

    sourceEquivariant :
      C3.EquivariantMap physicalAction sourceAction sourceFromPhysical
    recoveryEquivariant :
      C3.EquivariantMap sourceAction recoveryAction recover

    sourceLocator : String
    exactBalabanSourceWitnessForAction : Set

open BalabanLiteralC3Realisation public

------------------------------------------------------------------------
-- Source discrimination remains necessary for the still-unpaid transport
-- seams.  The recovered CMP109 action removes one blocker; it does not let an
-- analogy substitute for proving the remaining intertwiners.
------------------------------------------------------------------------

sourceDiscriminationAlreadyAvailable : Bool
sourceDiscriminationAlreadyAvailable = true

c3AnalogyMayReplaceSourceDiscrimination : Bool
c3AnalogyMayReplaceSourceDiscrimination = false

c3AnalogyMayReplaceSourceDiscriminationIsFalse :
  c3AnalogyMayReplaceSourceDiscrimination ≡ false
c3AnalogyMayReplaceSourceDiscriminationIsFalse = refl

highestAlphaYM369Question : String
highestAlphaYM369Question =
  "Transport the now-recovered CMP109 source-backed spatial C3 action along the literal same-object density/action/stress/Schwinger recovery compiler. Prove each recovery map intertwines that action; separately recover the action on the physical gauge-field variables and dexp/stress before importing Fourier/C3 decomposition there."
