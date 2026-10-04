{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralToGapRound479Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralToGapRound479Exact as R479
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R479.round479PublishedLiteralToGapCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

legacyCompatibilityRoutePruned :
  R479.olderR454R455CompatibilityRouteMandatory ≡ false
legacyCompatibilityRoutePruned = refl

postHocMagnitudeEqualityPruned :
  R479.postHocCMP116MagnitudeEqualityRequired ≡ false
postHocMagnitudeEqualityPruned = refl
