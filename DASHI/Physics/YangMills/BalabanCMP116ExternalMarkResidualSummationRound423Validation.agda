{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ExternalMarkResidualSummationRound423Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116ExternalMarkResidualSummationRound423Exact as R423
open import DASHI.Physics.YangMills.CompactLieProofLevel

externalMarkResidualSummationMachineChecked :
  R423.round423ExternalMarkResidualSummationCompilerLevel ≡ machineChecked
externalMarkResidualSummationMachineChecked = refl

freshOuterFiniteSumTheoremPruned :
  R423.round423FreshOuterFiniteSumTheoremRequired ≡ false
freshOuterFiniteSumTheoremPruned = refl
