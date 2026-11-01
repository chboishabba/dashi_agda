{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeFourFactorNormalFormAuditExact where

------------------------------------------------------------------------
-- DYADIC/PRINTED-MAP AUDIT: CMP98 RELATIVE HOLONOMY FOUR-FACTOR NORMAL FORM
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
import Data.List.Base as List

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact as R150
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155

appendAgreesWithInverseAppend :
  ∀ {A : Set} (left right : List A) →
  List._++_ left right ≡ Inverse._++_ left right
appendAgreesWithInverseAppend [] right = refl
appendAgreesWithInverseAppend (value ∷ values) right =
  cong (value ∷_) (appendAgreesWithInverseAppend values right)

holonomyAppend :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site left right →
  Bond.pathHolonomy realization site (List._++_ left right)
  ≡ Bond.multiply group
      (Bond.pathHolonomy realization site left)
      (Bond.pathHolonomy realization (Bond.walk site left) right)
holonomyAppend {group = group} realization site left right =
  subst
    (λ appended →
      Bond.pathHolonomy realization site appended
      ≡ Bond.multiply group
          (Bond.pathHolonomy realization site left)
          (Bond.pathHolonomy realization (Bond.walk site left) right))
    (sym (appendAgreesWithInverseAppend left right))
    (Inverse.holonomyAppend realization site left right)

asTranslatedNeighbourBlockSegment :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step → R150.TranslatedNeighbourBlockSegment n 6
asTranslatedNeighbourBlockSegment source step = record
  { R150.TranslatedNeighbourBlockSegment.commutation = R152.translationCommutation source
  ; R150.TranslatedNeighbourBlockSegment.minusEmbedding = R152.minusEmbedding source step
  ; R150.TranslatedNeighbourBlockSegment.plusEmbedding = R152.plusEmbedding source step
  ; R150.TranslatedNeighbourBlockSegment.coarseSegment = R152.coarseSegment source step
  ; R150.TranslatedNeighbourBlockSegment.plusCentreIsCoarseSegment =
      R152.coarseSegmentEndsAtPlusCentre source step
  }

sourceContourHolonomy :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point → Value
sourceContourHolonomy source step point =
  Bond.pathHolonomy (R152.realization source step)
    (Embed.embeddingCentre (R152.minusEmbedding source step))
    (Embed.canonicalCenteredContourWord point)

crossingHolonomy :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point → Value
crossingHolonomy source step point =
  Bond.pathHolonomy (R152.realization source step)
    (Embed.embed (R152.minusEmbedding source step) point)
    (Periodic.segmentWord (R152.coarseSegment source step))

targetReverseHolonomy :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point → Value
targetReverseHolonomy source step point =
  Bond.pathHolonomy (R152.realization source step)
    (Embed.embed (R152.plusEmbedding source step) point)
    (R155.reverseWord (Embed.canonicalCenteredContourWord point))

coarseReverseHolonomy :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step → Value
coarseReverseHolonomy {group = group} source step =
  Bond.inverse group (R155.coarseBackgroundHolonomy source step)

literalGammaHolonomyThreeFactor :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point →
  R155.literalGammaHolonomy source step point
  ≡ Bond.multiply group
      (sourceContourHolonomy source step point)
      (Bond.multiply group
        (crossingHolonomy source step point)
        (targetReverseHolonomy source step point))
literalGammaHolonomyThreeFactor {group = group} source step point =
  let
    realization = R152.realization source step
    minus = R152.minusEmbedding source step
    plus = R152.plusEmbedding source step
    sourceWord = Embed.canonicalCenteredContourWord point
    crossingWord = Periodic.segmentWord (R152.coarseSegment source step)
    targetWord = R155.reverseWord sourceWord
    sourceEndpoint :
      Bond.walk (Embed.embeddingCentre minus) sourceWord ≡ Embed.embed minus point
    sourceEndpoint = sym (Embed.embedMeaning minus point)
    crossingEndpoint :
      Bond.walk (Embed.embed minus point) crossingWord ≡ Embed.embed plus point
    crossingEndpoint =
      R150.translatedSegmentHitsSameOffset
        (asTranslatedNeighbourBlockSegment source step) point
    firstSplit = holonomyAppend realization (Embed.embeddingCentre minus)
      sourceWord (List._++_ crossingWord targetWord)
    secondSplit :
      Bond.pathHolonomy realization
        (Bond.walk (Embed.embeddingCentre minus) sourceWord)
        (List._++_ crossingWord targetWord)
      ≡ Bond.multiply group
          (crossingHolonomy source step point)
          (targetReverseHolonomy source step point)
    secondSplit =
      trans
        (cong (λ start → Bond.pathHolonomy realization start
          (List._++_ crossingWord targetWord)) sourceEndpoint)
        (trans
          (holonomyAppend realization (Embed.embed minus point) crossingWord targetWord)
          (cong (Bond.multiply group (crossingHolonomy source step point))
            (cong (λ start → Bond.pathHolonomy realization start targetWord)
              crossingEndpoint)))
  in
  trans firstSplit
    (cong (Bond.multiply group (sourceContourHolonomy source step point)) secondSplit)

relativeContourElementFourFactorNormalForm :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point →
  R155.relativeContourElement source step point
  ≡ Bond.multiply group
      (sourceContourHolonomy source step point)
      (Bond.multiply group
        (crossingHolonomy source step point)
        (Bond.multiply group
          (targetReverseHolonomy source step point)
          (coarseReverseHolonomy source step)))
relativeContourElementFourFactorNormalForm {group = group} source step point =
  let
    sourceValue = sourceContourHolonomy source step point
    crossingValue = crossingHolonomy source step point
    targetValue = targetReverseHolonomy source step point
    coarseValue = coarseReverseHolonomy source step
  in
  trans
    (cong (λ gamma → Bond.multiply group gamma coarseValue)
      (literalGammaHolonomyThreeFactor source step point))
    (trans
      (Bond.multiplyAssociative group sourceValue
        (Bond.multiply group crossingValue targetValue) coarseValue)
      (cong (Bond.multiply group sourceValue)
        (Bond.multiplyAssociative group crossingValue targetValue coarseValue)))

cmp98Equation119GammaThreeFactorAuditLevel : ProofLevel
cmp98Equation119GammaThreeFactorAuditLevel = machineChecked

cmp98Equation119RelativeFourFactorNormalFormAuditLevel : ProofLevel
cmp98Equation119RelativeFourFactorNormalFormAuditLevel = machineChecked
