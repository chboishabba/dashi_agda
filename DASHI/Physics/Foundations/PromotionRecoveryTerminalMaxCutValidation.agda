module DASHI.Physics.Foundations.PromotionRecoveryTerminalMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1Group
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge3
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as R144C3
import DASHI.Physics.Foundations.BalabanA1InvariantPathSourceReductionExact as A1Cut
import DASHI.Physics.YangMills.BalabanUnifiedRecoveryC3TransportExact as BalabanTransport

------------------------------------------------------------------------
-- Terminal promotion contract.
------------------------------------------------------------------------

groupLevelU1InsideSU2 : U1Group.groupLevelU1SubgroupConstructed ≡ true
groupLevelU1InsideSU2 = refl

u1InclusionPreservesSU2Multiplication :
  U1Group.inclusionPreservesMultiplication ≡ true
u1InclusionPreservesSU2Multiplication = refl

r3HodgeWedgeCrossPaid : Hodge3.r3HodgeWedgeCrossClosed ≡ true
r3HodgeWedgeCrossPaid = refl

r3HodgeUsesExistingSU2CrossMinors :
  Hodge3.reusesExistingSU2EuclideanMinors ≡ true
r3HodgeUsesExistingSU2CrossMinors = refl

cmp109ReachableC3FibreClosed :
  BalabanTransport.cmp109ReachableFibreC3TransportClosed ≡ true
cmp109ReachableC3FibreClosed = refl

r144SpatialStressActionClosed :
  BalabanTransport.r144SpatialStressTensorActionAlreadyLiteral ≡ true
r144SpatialStressActionClosed = refl

r144SameB4SourceFamilyReused :
  BalabanTransport.r144UsesSameB4GeneratorFamilyAsCMP109 ≡ true
r144SameB4SourceFamilyReused = refl

oldAmbientR140SocketNoLongerRequiredForStress :
  BalabanTransport.ambientR140IntertwinerRequiredForCurrentStressConsumer ≡ false
oldAmbientR140SocketNoLongerRequiredForStress = refl

terminalPhysicalPaymentIsR144Covariance :
  BalabanTransport.terminalPhysicalPaymentIsExistingR144CovarianceWitness ≡ true
terminalPhysicalPaymentIsR144Covariance = refl

fullAmbientR140ActionNotInvented :
  BalabanTransport.fullAmbientUnifiedRecoveryC3ActionRecovered ≡ false
fullAmbientR140ActionNotInvented = refl

r144TensorActionUsesNoNewAmbientCarrier :
  R144C3.r144SpatialC3NeedsNoNewAmbientCarrier ≡ true
r144TensorActionUsesNoNewAmbientCarrier = refl

p1InvariantPathCompilesSignedB4Covariance :
  A1Cut.p1InvariantPathPaysSignedTensorCovariance ≡ true
p1InvariantPathCompilesSignedB4Covariance = refl

genericFirstVariationNaturalityIsNotTerminalA1 :
  A1Cut.generalFirstVariationNaturalityIsNotMinimalA1Leaf ≡ true
genericFirstVariationNaturalityIsNotTerminalA1 = refl

rationalR144ReadoutStillNeedsSameObjectPathDerivativeIdentification :
  A1Cut.rationalFiniteD1ToRealPathDerivativeIdentificationStillSeparate ≡ true
rationalR144ReadoutStillNeedsSameObjectPathDerivativeIdentification = refl
