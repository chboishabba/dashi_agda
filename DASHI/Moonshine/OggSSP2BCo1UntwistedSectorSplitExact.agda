module DASHI.Moonshine.OggSSP2BCo1UntwistedSectorSplitExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE Co1 SPLIT OF THE 2B PLUS / UNTWINSTED WEIGHT-TWO SECTOR
--
-- In the FLM Leech-lattice realization, the untwisted invariant weight-two
-- space is the direct sum of two geometrically distinct pieces:
--
--   Sym^2(h),                       dim 300,
--   span{ e^lambda + e^-lambda },   dim 196560 / 2 = 98280,
--
-- where h is the 24-dimensional Leech space and lambda runs over norm-four
-- Leech vectors modulo +/-.
--
-- Both pieces are preserved by the Leech automorphism group.  The central
-- lattice involution -1 acts trivially on Sym^2(h) and on the paired
-- {+/-lambda} labels, so the action factors through Co1.  Thus the plus-space
-- decomposition used in the Tate cokernel max-cut is a genuine Co1-stable
-- sector split, not merely the numerical character identity 98580=98280+300.
--
-- This owner records the source geometry and dimensions.  It does NOT identify
-- the image of the integral Tate norm map inside these two sectors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

heisenbergDimension : Nat
heisenbergDimension = 24

symmetricSquareDimension : Nat
symmetricSquareDimension = 300

normFourVectorCount : Nat
normFourVectorCount = 196560

pairedNormFourOrbitDimension : Nat
pairedNormFourOrbitDimension = 98280

untwistedPlusDimension : Nat
untwistedPlusDimension = pairedNormFourOrbitDimension + symmetricSquareDimension

pairedOrbitDoubleCount : 2 * pairedNormFourOrbitDimension ≡ normFourVectorCount
pairedOrbitDoubleCount = refl

untwistedPlusDimensionIs98580 : untwistedPlusDimension ≡ 98580
untwistedPlusDimensionIs98580 = refl

record Co1UntwistedSectorSplitBoundary : Set where
  constructor co1-untwisted-sector-split-boundary
  field
    flmUntwistedSectorSourcePaid : Bool
    pairedNormFourSectorDimensionPaid : Bool
    symmetricSquareSectorDimensionPaid : Bool
    pairedNormFourSectorCo1Stable : Bool
    symmetricSquareSectorCo1Stable : Bool
    directSectorSplitPaid : Bool
    actualNormImagePlacementPaid : Bool

canonicalCo1UntwistedSectorSplitBoundary : Co1UntwistedSectorSplitBoundary
canonicalCo1UntwistedSectorSplitBoundary =
  co1-untwisted-sector-split-boundary
    true true true true true true false

actualNormImagePlacementStillOpen :
  Co1UntwistedSectorSplitBoundary.actualNormImagePlacementPaid
    canonicalCo1UntwistedSectorSplitBoundary
  ≡ false
actualNormImagePlacementStillOpen = refl
