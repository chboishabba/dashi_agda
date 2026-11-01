{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact where

------------------------------------------------------------------------
-- ROUND168 A1 BIDI: ORIENTED-LINK SMALLNESS IS NOT AN INDEPENDENT RECEIPT
--
-- Round164 asked for a defect bound on every signed/oriented link.  But the
-- repository gauge field stores only positive bonds; negative traversal is
-- literally the group inverse of the predecessor positive bond.  The selected
-- background radius machinery likewise controls positive physical links and
-- their inverses.
--
-- Therefore the correct quantitative seam is:
--
--   positive selected bond defect <= 1/2048
--   + defect(U^-1) = defect(U)
--   ---------------------------------------
--   every oriented traversal <= 1/2048.
--
-- This removes another doubled source obligation before the actual selected
-- background is welded into the Eq. (119) realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget

record PositiveLinkDefectInputs
    {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Value

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel ≡ Bond.identity group

    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right ≡ Bond.multiply group left right

    defectInverseInvariant : ∀ value →
      Telescope.defect kernel (Bond.inverse group value)
      ≡ Telescope.defect kernel value

    positiveBondDefectSmall : ∀ step site axis →
      Telescope.defect kernel
        (Bond.bondField
          (R158.CanonicalL13Equation119Source.realization source step)
          (pair site axis))
      ≤ Budget.perLinkDefectMajorant

    canonicalContourLengthAtMost24 : ∀ point →
      R164.listLength (Embed.canonicalCenteredContourWord point) ≤ 24

open PositiveLinkDefectInputs public

orientedLinkDefectFromPositive :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : PositiveLinkDefectInputs source)
    step site direction →
  Telescope.defect (kernel inputs)
    (Bond.orientedLink
      (R158.CanonicalL13Equation119Source.realization source step)
      site direction)
  ≤ Budget.perLinkDefectMajorant
orientedLinkDefectFromPositive source inputs step site (pair axis true) =
  positiveBondDefectSmall inputs step site axis
orientedLinkDefectFromPositive source inputs step site (pair axis false) =
  subst
    (λ selected → selected ≤ Budget.perLinkDefectMajorant)
    (defectInverseInvariant inputs
      (Bond.bondField
        (R158.CanonicalL13Equation119Source.realization source step)
        (pair (Bond.negativeStep site axis) axis)))
    (positiveBondDefectSmall inputs step (Bond.negativeStep site axis) axis)

asLiteralRelativeDefectInputs :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group) →
  PositiveLinkDefectInputs source →
  R164.LiteralRelativeDefectInputs source
asLiteralRelativeDefectInputs source inputs = record
  { R164.LiteralRelativeDefectInputs.kernel = kernel inputs
  ; R164.LiteralRelativeDefectInputs.kernelIdentityIsGroupIdentity =
      kernelIdentityIsGroupIdentity inputs
  ; R164.LiteralRelativeDefectInputs.kernelMultiplyIsGroupMultiply =
      kernelMultiplyIsGroupMultiply inputs
  ; R164.LiteralRelativeDefectInputs.orientedLinkDefectSmall =
      orientedLinkDefectFromPositive source inputs
  ; R164.LiteralRelativeDefectInputs.canonicalContourLengthAtMost24 =
      canonicalContourLengthAtMost24 inputs
  }

cmp98Equation119PositiveToOrientedDefectRound168Level : ProofLevel
cmp98Equation119PositiveToOrientedDefectRound168Level = machineChecked

-- The remaining physical smallness seam is now exactly the one already owned by
-- the selected-background lane: prove the positive bonds in this Eq. (119)
-- realization are those selected background links, then reuse their physical
-- radius -> quaternion l1 -> operator-defect bound.  Negative links are free.
literalCMP98PositiveSelectedBondSameObjectRound168Level : ProofLevel
literalCMP98PositiveSelectedBondSameObjectRound168Level = conditional
