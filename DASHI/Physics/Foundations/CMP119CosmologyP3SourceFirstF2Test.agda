{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SourceFirstF2Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3SourceFirstF2Exact as P3

postHocF2EqualityRetired : P3.postHocCompletedF2EqualityRequired ≡ false
postHocF2EqualityRetired = refl

markedFamilyConstructionRemains : P3.physicalMarkedCurvatureFamilyStillRequired ≡ true
markedFamilyConstructionRemains = refl

sourceFirstSelectionClosesSemantics : P3.sourceFirstF2SelectionMakesLiteralEqualityDefinitional ≡ true
sourceFirstSelectionClosesSemantics = refl
