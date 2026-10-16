module DASHI.Physics.Foundations.PromotionRecoveryTerminalMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1Group
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge3
import DASHI.Physics.YangMills.BalabanUnifiedRecoveryC3TransportExact as BalabanTransport

------------------------------------------------------------------------
-- RED-first terminal promotion contract.
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
r3HodgeUsesExistingSU2EuclideanMinors = refl

cmp109ReachableC3FibreClosed :
  BalabanTransport.cmp109ReachableFibreC3TransportClosed ≡ true
cmp109ReachableC3FibreClosed = refl

fullAmbientR140ActionNotInvented :
  BalabanTransport.fullAmbientUnifiedRecoveryC3ActionRecovered ≡ false
fullAmbientR140ActionNotInvented = refl

minimalR140IntertwinerObligationExposed :
  BalabanTransport.minimalSameObjectR140IntertwinerObligationExposed ≡ true
minimalR140IntertwinerObligationExposed = refl
