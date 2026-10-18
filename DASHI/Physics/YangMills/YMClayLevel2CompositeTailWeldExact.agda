{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2CompositeTailWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact as Tail
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

------------------------------------------------------------------------
-- LEVEL-2 D1: SAME-FAMILY COMPOSITE PRODUCT-TAIL WELD
--
-- The physical OPE remainder must not be an arbitrary function that merely
-- happens to satisfy the same numerical bound as the composite marked tail.
-- It must be the remainder of the ACTUAL completed composite projection already
-- carried by SameFamilyMarkedSourceData.
--
-- Existing machinery already owns:
--
--   Shared.compositeInsertionTail
--     and its dyadic vanishing modulus;
--
--   Marked.SameFamilyMarkedSourceData
--     and therefore the actual completed composite projection;
--
--   Tail.sharedCompositeAsDyadicOPERemainder
--     which packages the marked tail as the repository's literal dyadic OPE
--     remainder majorant.
--
-- The only D1 physical field below is the same-object equality identifying the
-- literal product-expansion remainder, evaluated on that actual completed
-- composite, with the selected composite marked tail.
------------------------------------------------------------------------

record CompositeProductTailWeld
    {C : Nuclear.ContinuityScale}
    {CompletedState Composite Scale Volume Root : Set}
    (compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite)
    (shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    (scale : Scale) (volume : Volume) (root : Root)
    : Set₁ where
  field
    literalProductRemainder : Composite → Nat → ℚ
    remaining : Nat → Nat

    literalProductRemainderIsCompositeTail :
      ∀ depth →
      literalProductRemainder
        (Marked.compositeProjection compositeData
          (Marked.completedState compositeData))
        depth
      ≡ Shared.compositeInsertionTail
          shared scale volume root depth (remaining depth)

open CompositeProductTailWeld public

literalCompletedComposite :
  ∀ {C CompletedState Composite Scale Volume Root}
    {compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root} →
  CompositeProductTailWeld compositeData shared scale volume root →
  Composite
literalCompletedComposite {compositeData = compositeData} weld =
  Marked.compositeProjection compositeData (Marked.completedState compositeData)

literalOPERemainderMagnitude :
  ∀ {C CompletedState Composite Scale Volume Root}
    {compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root} →
  CompositeProductTailWeld compositeData shared scale volume root →
  Nat → ℚ
literalOPERemainderMagnitude weld depth =
  literalProductRemainder weld (literalCompletedComposite weld) depth

literalOPERemainderIsSelectedCompositeTail :
  ∀ {C CompletedState Composite Scale Volume Root}
    {compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root}
    (weld : CompositeProductTailWeld compositeData shared scale volume root) →
  ∀ depth →
  literalOPERemainderMagnitude weld depth
  ≡ Shared.compositeInsertionTail
      shared scale volume root depth (remaining weld depth)
literalOPERemainderIsSelectedCompositeTail =
  literalProductRemainderIsCompositeTail

literalCompletedCompositeOPERemainderMajorant :
  ∀ {C CompletedState Composite Scale Volume Root}
    {compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root}
    (weld : CompositeProductTailWeld compositeData shared scale volume root) →
  Local.DyadicOPERemainderMajorant
literalCompletedCompositeOPERemainderMajorant
    {shared = shared} {scale = scale} {volume = volume} {root = root} weld =
  let
    marked = Tail.sharedCompositeAsDyadicOPERemainder
      shared scale volume root (remaining weld)
  in record
    { Local.DyadicOPERemainderMajorant.coefficient =
        Local.coefficient marked
    ; Local.DyadicOPERemainderMajorant.coefficientNonnegative =
        Local.coefficientNonnegative marked
    ; Local.DyadicOPERemainderMajorant.remainderMagnitude =
        literalOPERemainderMagnitude weld
    ; Local.DyadicOPERemainderMajorant.remainderNonnegative =
        λ depth →
          subst
            (λ selected → 0ℚ ≤ selected)
            (sym (literalOPERemainderIsSelectedCompositeTail weld depth))
            (Local.remainderNonnegative marked depth)
    ; Local.DyadicOPERemainderMajorant.remainderBelowDyadic =
        λ depth →
          subst
            (λ selected →
              selected ≤ Local.coefficient marked * Geo.halfPower depth)
            (sym (literalOPERemainderIsSelectedCompositeTail weld depth))
            (Local.remainderBelowDyadic marked depth)
    }

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

newCompositeTailDecayTheoremRequiredByD1 : Bool
newCompositeTailDecayTheoremRequiredByD1 = false

newCompositeTailDecayTheoremRequiredByD1IsFalse :
  newCompositeTailDecayTheoremRequiredByD1 ≡ false
newCompositeTailDecayTheoremRequiredByD1IsFalse = refl

newContinuumCompositeCompletionTheoremRequiredByD1 : Bool
newContinuumCompositeCompletionTheoremRequiredByD1 = false

newContinuumCompositeCompletionTheoremRequiredByD1IsFalse :
  newContinuumCompositeCompletionTheoremRequiredByD1 ≡ false
newContinuumCompositeCompletionTheoremRequiredByD1IsFalse = refl

sameCompletedCompositeTailAttachmentStillPhysical : Bool
sameCompletedCompositeTailAttachmentStillPhysical = true

sameCompletedCompositeTailAttachmentStillPhysicalIsTrue :
  sameCompletedCompositeTailAttachmentStillPhysical ≡ true
sameCompletedCompositeTailAttachmentStillPhysicalIsTrue = refl

compositeTailWeldCompilerLevel : ProofLevel
compositeTailWeldCompilerLevel = machineChecked

physicalCompositeTailAttachmentLevel : ProofLevel
physicalCompositeTailAttachmentLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
