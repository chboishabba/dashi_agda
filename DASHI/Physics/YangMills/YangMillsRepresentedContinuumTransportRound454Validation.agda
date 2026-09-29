{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedContinuumTransportRound454Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsRepresentedContinuumTransportRound454Exact as R454
open import DASHI.Physics.YangMills.CompactLieProofLevel

pointwiseTransportMachineChecked :
  R454.round454PointwiseExpectationTransportCompilerLevel ≡ machineChecked
pointwiseTransportMachineChecked = refl

wholeMeasureEqualityPruned :
  R454.round454WholeMeasureRecordEqualityRequired ≡ false
wholeMeasureEqualityPruned = refl

transportUsesPointwiseExpectationOnly :
  R454.round454UnaffectedReceiptTransportUsesOnlyPointwiseExpectationEquality ≡ true
transportUsesPointwiseExpectationOnly = refl
