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
-- relative element, but introduced a local path-reversal helper.  The repo
-- already owns the stronger periodic inverse-path theorem, including exact
-- inverse holonomy of reverse/opposite traversal.  The periodic coordinate
-- closure owner also proves the required step inverse laws from literal torus
-- arithmetic, so those laws are not input here.  Separately, the P33 lane proves
-- that its orientation-sensitive occurrence holonomy is the SAME repository
-- `pathHolonomy` recursion.
--
-- BIDI says these conventions must be welded, not duplicated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicContourEdgeKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicPathHolonomyBridgeExact as P33

reverseWordIsCanonicalReverseOpposite :
  (directions : List Word.SignedAxis4) →
  R155.reverseWord directions ≡ InversePath.reverseOpposite directions
reverseWordIsCanonicalReverseOpposite directions = refl

-- The printed final leg Gamma_{x(c),c+} is literally inverse transport.
-- No step-law receipt is accepted: the repository finite-torus theorem supplies it.
plusContourReverseHolonomyIsInverse :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
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
plusContourReverseHolonomyIsInverse {n = n} source step point =
  trans
    (cong
      (λ start →
        Bond.pathHolonomy
          (R152.realization source step)
          start
          (R155.reverseWord (Embed.canonicalCenteredContourWord point)))
      (Embed.embedMeaning (R152.plusEmbedding source step) point))
    (InversePath.pathHolonomyReverseOpposite
      (Closure.periodicStepInverseLaws n)
      (R152.realization source step)
      (Embed.embeddingCentre (R152.plusEmbedding source step))
      (Embed.canonicalCenteredContourWord point))

-- Cross-pollination with the P33 occurrence-sensitive derivative kernel.
-- Its literal occurrence holonomy and Eq. (119)'s Gamma holonomy are one object.
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

cmp98Equation119PeriodicStepInverseDerivedRound161Level : ProofLevel
cmp98Equation119PeriodicStepInverseDerivedRound161Level = machineChecked

cmp98Equation119P33PathHolonomySameObjectRound161Level : ProofLevel
cmp98Equation119P33PathHolonomySameObjectRound161Level = machineChecked

-- Remaining path-side physical seam is only SAME background/group realization
-- across the Eq. (119) and P33 differential lanes.  Reversal, inverse traversal,
-- and path-holonomy convention are repository theorems.
