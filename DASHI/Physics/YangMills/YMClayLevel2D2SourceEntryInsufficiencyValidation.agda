{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2SourceEntryInsufficiencyValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayLevel2D2SourceEntryInsufficiencyExact as D2

publishedEntryDoesNotDetermineCompositeInsertion :
  D2.publishedSourceEntryDeterminesCompositeInsertionValue ≡ false
publishedEntryDoesNotDetermineCompositeInsertion =
  D2.publishedSourceEntryDeterminesCompositeInsertionValueIsFalse

publishedEntryDoesNotPayD2aNaturality :
  D2.publishedSourceEntryPaysD2aInsertionNaturality ≡ false
publishedEntryDoesNotPayD2aNaturality =
  D2.publishedSourceEntryPaysD2aInsertionNaturalityIsFalse

sourceEntryInsufficiencyIsMachineChecked :
  D2.sourceEntryInsufficiencyCompilerLevel ≡ machineChecked
sourceEntryInsufficiencyIsMachineChecked = refl

clayPromotionRemainsFalse :
  D2.clayPromotion ≡ false
clayPromotionRemainsFalse =
  D2.clayPromotionIsFalse
