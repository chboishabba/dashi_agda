{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Exact as R446
open import DASHI.Physics.YangMills.CompactLieProofLevel

markedMomentOS05CompilerMachineChecked :
  R446.round446MarkedMomentOS05CompilerLevel ≡ machineChecked
markedMomentOS05CompilerMachineChecked = refl

realMomentProducerPruned :
  R446.round446RealT5MomentProducerRequired ≡ false
realMomentProducerPruned = refl

independentContinuumOS05Pruned :
  R446.round446IndependentContinuumOS05TheoremRequired ≡ false
independentContinuumOS05Pruned = refl
