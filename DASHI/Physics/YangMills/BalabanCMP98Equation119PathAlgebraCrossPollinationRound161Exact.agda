{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PathAlgebraCrossPollinationRound161Exact where

------------------------------------------------------------------------
-- ROUND161 A1 BIDI / CROSS-POLLINATION:
-- REUSE THE CANONICAL PERIODIC PATH-INVERSE AND P33 HOLONOMY OWNERS
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Round155 correctly built the literal Eq. (14) contour and Eq. (15)/(114)
-- relative element, but it introduced a local path-reversal helper.  The repo
-- already owns the stronger periodic inverse-path theorem, including the exact
-- inverse holonomy of a reverse/opposite traversal.  Separately, the P33 lane
-- already proves that its orientation-sensitive occurrence holonomy is the SAME
-- repository `pathHolonomy` recursion.
--
-- BIDI says these conventions must be welded, not duplicated.  This round:
--   * proves Round155 reversal is exactly the canonical reverse/opposite word;
--   * proves the final plus-block contour has inverse holonomy;
--   * proves the literal Gamma_{c,x} holonomy is the same holonomy consumed by
--     the P33 occurrence-sensitive derivative kernel.
-- No new path convention survives.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicContourEdgeKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicPathHolonomyBridgeExact as P33

------------------------------------------------------------------------
-- Round155's helper is not a second reversal convention.
------------------------------------------------------------------------

reverseWordIsCanonicalReverseOpposite :
  (directions : List Word.SignedAxis4) →
  R155.reverseWord directions ≡ InversePath.reverseOpposite directions
reverseWordIsCanonicalReverseOpposite directions = refl

------------------------------------------------------------------------
-- The printed final leg Gamma_{x(c),c+} is literally inverse transport.
------------------------------------------------------------------------

plusContourReverseHolonomyIsInverse :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    step (point : Centered.CenteredBlockPoint4 6) →
  Bond.pathHolonomy
    (R152.realization source step)
    (Embed.embed (R152.plusEmbedding source step) point)
    (R155.reverseWord (Embed.canonicalCenteredContourWord point))
  ≡ Bond.inverse group
      (Bond.pathHolonomy
        (R152.realization source step)
        (Embed.embeddingCentre (R152.plusEmbedding source step))
        (Embed.canonicalCenteredContourWord point))
plusContourReverseHolonomyIsInverse source stepLaws step point =
  trans
    (cong
      (λ start →
        Bond.pathHolonomy
          (R152.realization source step)
          start
          (R155.reverseWord (Embed.canonicalCenteredContourWord point)))
      (Embed.embedMeaning (R152.plusEmbedding source step) point))
    (InversePath.pathHolonomyReverseOpposite
      stepLaws
      (R152.realization source step)
      (Embed.embeddingCentre (R152.plusEmbedding source step))
      (Embed.canonicalCenteredContourWord point))

------------------------------------------------------------------------
-- Cross-pollination with the P33 occurrence-sensitive derivative kernel.
-- Its literal occurrence holonomy and Eq. (119)'s Gamma holonomy are one object.
------------------------------------------------------------------------

literalGammaOccurrenceHolonomyEqualsEq119Holonomy :
  ∀ {C n Group Lie group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (algebra : Kernel.OrientedDifferentialAlgebra Group Lie)
    (groupExact : Kernel.group algebra ≡ group)
    (agreement : Kernel.GroupOperationsAgree Group Lie algebra)
    step point →
  Kernel.literalOccurrenceHolonomy algebra
    (Bond.bondField (R152.realization source step))
    (Kernel.contourOccurrences
      (Embed.embeddingCentre (R152.minusEmbedding source step))
      (R155.literalGammaWord source step point))
  ≡ R155.literalGammaHolonomy source step point
literalGammaOccurrenceHolonomyEqualsEq119Holonomy
    source algebra refl agreement step point =
  P33.occurrenceHolonomyEqualsRepositoryPathHolonomy
    algebra agreement
    (R152.realization source step)
    (Embed.embeddingCentre (R152.minusEmbedding source step))
    (R155.literalGammaWord source step point)

cmp98Equation119CanonicalPathInverseReuseRound161Level : ProofLevel
cmp98Equation119CanonicalPathInverseReuseRound161Level = machineChecked

cmp98Equation119P33PathHolonomySameObjectRound161Level : ProofLevel
cmp98Equation119P33PathHolonomySameObjectRound161Level = machineChecked

-- Remaining path-side physical inputs are now genuinely source-facing:
--   * periodic step inverse laws for the chosen torus carrier;
--   * the same background/group realization used by the P33 differential lane.
-- There is no second reversal or holonomy convention to identify.
