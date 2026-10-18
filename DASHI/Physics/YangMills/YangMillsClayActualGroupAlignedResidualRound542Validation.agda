{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayActualGroupAlignedResidualRound542Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayActualGroupAlignedResidualRound542Exact as R542
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualCountIsTwentyEight :
  R542.residualLeafCount ≡ 28
residualCountIsTwentyEight = refl

tagAloneNotEnough :
  R542.classificationTagAloneIdentifiesActualGaugeGroup ≡ false
tagAloneNotEnough = refl

actualOperationsMustAlign :
  R542.actualCarrierAndLieOperationsMustAlign ≡ true
actualOperationsMustAlign = refl

su2CannotPayAlignment :
  R542.su2ValidationCanPayActualGroupAlignment ≡ false
su2CannotPayAlignment = refl
