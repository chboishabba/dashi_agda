{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact as R541
open import DASHI.Physics.YangMills.CompactLieProofLevel

alignmentInterfaceMachineChecked :
  R541.round541ActualGroupAlignmentInterfaceLevel ≡ machineChecked
alignmentInterfaceMachineChecked = refl
