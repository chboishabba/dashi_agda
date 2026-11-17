{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2SourceEntryInsufficiencyExact where

------------------------------------------------------------------------
-- D2 SOUNDNESS / PUBLISHED SOURCE ENTRY DOES NOT DETERMINE COMPOSITE MIXING
--
-- The source-native strong state stores its composite insertion as an extra
-- consumer coordinate.  The published CMP119/CMP122 entry theorem depends on
-- the common source density and differentiated E2/Pi coordinates.  It does not
-- inspect the value of the composite insertion.
--
-- Therefore published-flow membership cannot by itself establish D2a
-- insertion/blocking naturality.  The result below is constructive: replace the
-- composite insertion while preserving every other strong-state coordinate.
-- The exact published-flow entry still recompiles.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Native
import DASHI.Physics.YangMills.BalabanSourceNativePublishedFlowEntryExact as Entry

replaceCompositeInsertion :
  ∀ {base : Native.SourceNativeBalabanBaseline}
    (state : Native.SourceNativeUnifiedState base) →
  Native.CompositeInsertion state →
  Native.SourceNativeUnifiedState base
replaceCompositeInsertion state replacement = record
  { Native.SourceNativeUnifiedState.CompositeInsertion =
      Native.CompositeInsertion state
  ; Native.SourceNativeUnifiedState.WeightedConnectedCorrelation =
      Native.WeightedConnectedCorrelation state
  ; Native.SourceNativeUnifiedState.Characteristic =
      Native.Characteristic state
  ; Native.SourceNativeUnifiedState.compositeInsertion =
      replacement
  ; Native.SourceNativeUnifiedState.weightedConnectedCorrelation =
      Native.weightedConnectedCorrelation state
  ; Native.SourceNativeUnifiedState.characteristic =
      Native.characteristic state
  }

replacePublishedCompositeInsertionAt :
  ∀ (published : Entry.SourceNativePublishedFlow)
    (scale : Nat)
    (state : Entry.SourceNativeStrongStateAt published scale) →
  Native.CompositeInsertion (Entry.strongState state) →
  Entry.SourceNativeStrongStateAt published scale
replacePublishedCompositeInsertionAt published scale state replacement = record
  { Entry.SourceNativeStrongStateAt.strongState =
      replaceCompositeInsertion (Entry.strongState state) replacement
  }

publishedEntryAfterCompositeReplacement :
  ∀ (published : Entry.SourceNativePublishedFlow)
    (scale : Nat)
    (state : Entry.SourceNativeStrongStateAt published scale)
    (replacement : Native.CompositeInsertion (Entry.strongState state)) →
  Entry.LiteralStateEntersPublishedBalabanRG
    published scale
    (replacePublishedCompositeInsertionAt published scale state replacement)
publishedEntryAfterCompositeReplacement published scale state replacement =
  Entry.literalStateEntersPublishedBalabanRG
    published scale
    (replacePublishedCompositeInsertionAt published scale state replacement)

publishedSourceEntryDeterminesCompositeInsertionValue : Bool
publishedSourceEntryDeterminesCompositeInsertionValue = false

publishedSourceEntryDeterminesCompositeInsertionValueIsFalse :
  publishedSourceEntryDeterminesCompositeInsertionValue ≡ false
publishedSourceEntryDeterminesCompositeInsertionValueIsFalse = refl

publishedSourceEntryPaysD2aInsertionNaturality : Bool
publishedSourceEntryPaysD2aInsertionNaturality = false

publishedSourceEntryPaysD2aInsertionNaturalityIsFalse :
  publishedSourceEntryPaysD2aInsertionNaturality ≡ false
publishedSourceEntryPaysD2aInsertionNaturalityIsFalse = refl

sourceEntryInsufficiencyCompilerLevel : ProofLevel
sourceEntryInsufficiencyCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
