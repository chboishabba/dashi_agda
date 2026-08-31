{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119ClosedPathSameObjectRound165Exact where

------------------------------------------------------------------------
-- ROUND165 A1 BIDI: THE 74-LINK CLOSED PATH IS EXACTLY ROUND155'S RELATIVE
-- CONTOUR ELEMENT
--
-- Round164 put the quantitative defect telescope on the literal closed word
--
--   Gamma_{c,x} ++ reverse(c).
--
-- This file discharges the remaining same-object seam.  The Gamma endpoint is
-- the derived plus centre, because the point contour reaches x, the canonical
-- L=13 translate reaches x(c), and the reverse plus contour returns to c+.
-- The existing inverse-path theorem then identifies the final reverse(c)
-- holonomy with U(c)^-1.  Consequently
--
--   Hol(Gamma ++ reverse(c))
--     = Hol(Gamma) Hol(c)^-1
--     = Round155.relativeContourElement.
--
-- Hence the Round164 defect estimate is literally an estimate on the Y_x
-- argument used by Eq. (119), not on a proxy carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic

literalGammaEndpointIsPlusCentre :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    step (point : Centered.CenteredBlockPoint4 6) →
  Bond.walk
    (Embed.embeddingCentre
      (R152.minusEmbedding (R158.asRound152Source source) step))
    (R155.literalGammaWord (R158.asRound152Source source) step point)
  ≡ Embed.embeddingCentre
      (R152.plusEmbedding (R158.asRound152Source source) step)
literalGammaEndpointIsPlusCentre {n = n} source step point =
  let
    src = R158.asRound152Source source
    minus = R152.minusEmbedding src step
    plus = R152.plusEmbedding src step
    contour = Embed.canonicalCenteredContourWord point
    coarse = Periodic.segmentWord (R152.coarseSegment src step)

    afterMinusContour :
      Bond.walk (Embed.embeddingCentre minus) contour
      ≡ Embed.embed minus point
    afterMinusContour = sym (Embed.embedMeaning minus point)

    afterCoarse :
      Bond.walk (Embed.embed minus point) coarse
      ≡ Embed.embed plus point
    afterCoarse = sym (R163.translatedPointExact
      (R158.minusEmbedding source step)
      (R158.coarseSegmentAt source step)
      point)

    plusPointIsWalk :
      Embed.embed plus point
      ≡ Bond.walk (Embed.embeddingCentre plus) contour
    plusPointIsWalk = Embed.embedMeaning plus point

    returnToPlusCentre :
      Bond.walk (Embed.embed plus point) (R155.reverseWord contour)
      ≡ Embed.embeddingCentre plus
    returnToPlusCentre =
      trans
        (cong
          (λ start → Bond.walk start (R155.reverseWord contour))
          plusPointIsWalk)
        (InversePath.walkReverseOpposite
          (Closure.periodicStepInverseLaws n)
          (Embed.embeddingCentre plus)
          contour)
  in
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre minus)
      contour
      (coarse ++ R155.reverseWord contour))
    (trans
      (cong
        (λ start → Bond.walk start (coarse ++ R155.reverseWord contour))
        afterMinusContour)
      (trans
        (Embed.walkAppend
          (Embed.embed minus point)
          coarse
          (R155.reverseWord contour))
        (trans
          (cong
            (λ start → Bond.walk start (R155.reverseWord contour))
            afterCoarse)
          returnToPlusCentre)))
  where
    open import Data.List.Base using (_++_)

closedPathHolonomyIsRelativeContourElement :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    step (point : Centered.CenteredBlockPoint4 6) →
  Bond.pathHolonomy
    (R152.realization (R158.asRound152Source source) step)
    (Embed.embeddingCentre
      (R152.minusEmbedding (R158.asRound152Source source) step))
    (R164.relativeClosedWord source step point)
  ≡ R155.relativeContourElement
      (R158.asRound152Source source) step point
closedPathHolonomyIsRelativeContourElement {n = n} {group = group}
    source step point =
  let
    src = R158.asRound152Source source
    realization = R152.realization src step
    minusCentre = Embed.embeddingCentre (R152.minusEmbedding src step)
    plusCentre = Embed.embeddingCentre (R152.plusEmbedding src step)
    gamma = R155.literalGammaWord src step point
    coarse = Periodic.segmentWord (R152.coarseSegment src step)

    appendHolonomy =
      InversePath.holonomyAppend realization minusCentre
        gamma (R155.reverseWord coarse)

    gammaEndpoint = literalGammaEndpointIsPlusCentre source step point

    reverseCoarseAtPlus :
      Bond.pathHolonomy realization plusCentre (R155.reverseWord coarse)
      ≡ Bond.inverse group
          (Bond.pathHolonomy realization minusCentre coarse)
    reverseCoarseAtPlus =
      trans
        (cong
          (λ start → Bond.pathHolonomy realization start (R155.reverseWord coarse))
          (sym (R152.coarseSegmentEndsAtPlusCentre src step)))
        (InversePath.pathHolonomyReverseOpposite
          (Closure.periodicStepInverseLaws n)
          realization minusCentre coarse)

    transportedReverse :
      Bond.pathHolonomy realization
        (Bond.walk minusCentre gamma)
        (R155.reverseWord coarse)
      ≡ Bond.inverse group
          (Bond.pathHolonomy realization minusCentre coarse)
    transportedReverse =
      trans
        (cong
          (λ start → Bond.pathHolonomy realization start (R155.reverseWord coarse))
          gammaEndpoint)
        reverseCoarseAtPlus
  in
  trans
    appendHolonomy
    (trans
      (cong
        (Bond.multiply group (Bond.pathHolonomy realization minusCentre gamma))
        transportedReverse)
      refl)

literalRelativeElementDefectBelowSourceThreshold :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source)
    step point →
  DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact.defect
    (R164.kernel inputs)
    (R155.relativeContourElement (R158.asRound152Source source) step point)
  DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact.≤
    DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact.sourceDefectThreshold
literalRelativeElementDefectBelowSourceThreshold source inputs step point =
  let
    import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
    import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
  in
  subst
    (λ selected → Telescope.defect (R164.kernel inputs) selected
      Chart.≤ Chart.sourceDefectThreshold)
    (closedPathHolonomyIsRelativeContourElement source step point)
    (R164.literalRelativeClosedPathDefectBelowSourceThreshold
      source inputs step point)
  where
    open import Relation.Binary.PropositionalEquality using (subst)

cmp98Equation119ClosedPathSameObjectRound165Level : ProofLevel
cmp98Equation119ClosedPathSameObjectRound165Level = machineChecked

cmp98Equation119LiteralRelativeDefectRound165Level : ProofLevel
cmp98Equation119LiteralRelativeDefectRound165Level = machineChecked
