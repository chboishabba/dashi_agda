{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMassGapSemanticMaxCutRound503Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayMassGapSemanticMaxCutRound503Exact as R503
open import DASHI.Physics.YangMills.CompactLieProofLevel

semanticCompilerMachineChecked :
  R503.round503T2SemanticCompilerLevel ≡ machineChecked
semanticCompilerMachineChecked = refl
