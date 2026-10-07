module DASHI.Physics.Closure.NSABCDMaxCut20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSABCDMaxCut20261007Exact as X

bRepresentationFrozen : X.bRepresentationProgrammeFrozen ≡ true
bRepresentationFrozen = X.bRepresentationProgrammeFrozenIsTrue

cdAuditNotReconstruction : X.cdIndependentReconstructionGatesAudit ≡ false
cdAuditNotReconstruction = X.cdIndependentReconstructionGatesAuditIsFalse

noClayPromotion : X.clayPromotion ≡ false
noClayPromotion = X.clayPromotionIsFalse
