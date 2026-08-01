module DASHI.Physics.YangMills.BalabanClayGate4HRBetaDimockLocalizationAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4DimockConnectedActivityStabilityExact as Dimock

------------------------------------------------------------------------
-- Connected localized activities discharge the H-R_beta half-budget.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - III. Convergence",
-- arXiv:1304.0705v1 [math-ph]. No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- The existing five-channel theorem controls a finite sum of local cell
-- remainders.  Dimock's convergence architecture instead produces connected
-- localized activities H(X).  This adapter identifies the two total remainders,
-- transports the scalar order convention, and spends the connected-activity
-- coupling-times-volume estimate inside the selected Delta/2 budget.
------------------------------------------------------------------------

record HRBetaDimockLocalizationInputs
    (Cell Polymer Scalar : Set) : Set₁ where
  field
    normalization : Five.PhysicalFiveChannelHRBetaNormalization Cell Scalar
    connected : Dimock.ConnectedActivityStabilityData Polymer Scalar

    absoluteTotalMeaning :
      HRBase.absolute
        (Five.algebra (Five.channels normalization))
        (Five.totalRemainder (Five.channels normalization))
      ≡
      Dimock.absolute (Dimock.algebra connected)
        (Dimock.totalActivity connected)

    orderTransport : ∀ {left right} →
      Dimock.LessEqual (Dimock.algebra connected) left right →
      HRBase.LessEqual
        (Five.algebra (Five.channels normalization)) left right

    couplingVolumeBelowHalfIncrement :
      HRBase.LessEqual
        (Five.algebra (Five.channels normalization))
        (Dimock.multiply (Dimock.algebra connected)
          (Dimock.coupling connected)
          (Dimock.volume connected))
        (Five.totalHalfIncrement (Five.channels normalization))

open HRBetaDimockLocalizationInputs public

localizedConnectedActivitiesGiveHalfIncrement :
  ∀ {Cell Polymer Scalar}
    (inputs : HRBetaDimockLocalizationInputs Cell Polymer Scalar) →
  HRBase.LessEqual
    (Five.algebra (Five.channels (normalization inputs)))
    (HRBase.absolute
      (Five.algebra (Five.channels (normalization inputs)))
      (Five.totalRemainder
        (Five.channels (normalization inputs))))
    (Five.totalHalfIncrement
      (Five.channels (normalization inputs)))
localizedConnectedActivitiesGiveHalfIncrement inputs =
  subst
    (λ lower →
      HRBase.LessEqual
        (Five.algebra (Five.channels (normalization inputs)))
        lower
        (Five.totalHalfIncrement
          (Five.channels (normalization inputs))))
    (sym (absoluteTotalMeaning inputs))
    (HRBase.transitive
      (Five.algebra (Five.channels (normalization inputs)))
      (orderTransport inputs
        (Dimock.connectedActivityBelowCouplingVolume
          (connected inputs)))
      (couplingVolumeBelowHalfIncrement inputs))

localizedConnectedActivitiesGivePhysicalHalf :
  ∀ {Cell Polymer Scalar}
    (inputs : HRBetaDimockLocalizationInputs Cell Polymer Scalar) →
  HRBase.LessEqual
    (Five.algebra (Five.channels (normalization inputs)))
    (HRBase.absolute
      (Five.algebra (Five.channels (normalization inputs)))
      (Five.totalRemainder
        (Five.channels (normalization inputs))))
    (Five.PhysicalHalf (normalization inputs)
      (Five.Delta (normalization inputs)))
localizedConnectedActivitiesGivePhysicalHalf inputs =
  subst
    (λ upper →
      HRBase.LessEqual
        (Five.algebra (Five.channels (normalization inputs)))
        (HRBase.absolute
          (Five.algebra (Five.channels (normalization inputs)))
          (Five.totalRemainder
            (Five.channels (normalization inputs))))
        upper)
    (sym
      (trans
        (Five.physicalHalfMeaning (normalization inputs))
        (Five.halfDeltaMeaning (normalization inputs))))
    (localizedConnectedActivitiesGiveHalfIncrement inputs)

hrBetaConnectedActivityLocalizationAdapterLevel : ProofLevel
hrBetaConnectedActivityLocalizationAdapterLevel = machineChecked

hrBetaConnectedActivityPhysicalHalfLevel : ProofLevel
hrBetaConnectedActivityPhysicalHalfLevel = machineChecked

physicalHRBetaActivityIdentificationInputsLevel : ProofLevel
physicalHRBetaActivityIdentificationInputsLevel = conditional

physicalHRBetaCouplingVolumeAllocationInputsLevel : ProofLevel
physicalHRBetaCouplingVolumeAllocationInputsLevel = conditional
