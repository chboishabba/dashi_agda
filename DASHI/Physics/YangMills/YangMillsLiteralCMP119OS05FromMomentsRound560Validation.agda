{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as R560
open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteOS05CompilerMachineChecked :
  R560.round560FiniteOS05FromLiteralMomentsLevel ≡ machineChecked
finiteOS05CompilerMachineChecked = refl

sameFamilyExpectationWeldPruned :
  R560.round560SameFamilyExpectationAttachmentRequired ≡ false
sameFamilyExpectationWeldPruned = refl

closureAuthorityStandard :
  R560.round560CanonicalClosureAuthorityLevel ≡ standardImported
closureAuthorityStandard = refl
