{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98CanonicalContourLength24Round172Exact where

------------------------------------------------------------------------
-- ROUND172 A1 BIDI: THE CANONICAL ROUND155 CONTOUR LENGTH IS CONSTRUCTION
--
-- The length-24 theorem was already proved on the literal centred radius-six
-- carrier.  Round164/R168 still accepted `canonicalContourLengthAtMost24` as a
-- field only because they use a locally defined list-length function.
--
-- This round proves the two length functions agree and identifies the two
-- independently named centred-displacement functions definitionally.  Hence
--
--   length(canonicalCenteredContourWord x) <= 24
--
-- is generated for every Round155 point.  It is not physical input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (suc)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourLengthExact as Length
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalContourLength24Exact as Length24
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours

r164ListLengthIsPeriodicLength : ∀ {A : Set} (values : List A) →
  R164.listLength values ≡ Periodic.listLength values
r164ListLengthIsPeriodicLength [] = refl
r164ListLengthIsPeriodicLength (_ ∷ values) =
  cong suc (r164ListLengthIsPeriodicLength values)

centeredDisplacementNamesAgree :
  ∀ {radius} (point : Centered.CenteredBlockPoint4 radius) →
  Embed.centeredDisplacement4 point
  ≡ Length24.centeredPointDisplacement point
centeredDisplacementNamesAgree
  (Carrier.pair (Carrier.pair x0 x1) (Carrier.pair x2 x3)) = refl

canonicalContourPeriodicLengthAtMost24 :
  (point : Centered.CenteredBlockPoint4 6) →
  Periodic.listLength (Embed.canonicalCenteredContourWord point) ≤ 24
canonicalContourPeriodicLengthAtMost24 point =
  let
    displacement = Embed.centeredDisplacement4 point
    lengthExact :
      Periodic.listLength (Embed.canonicalCenteredContourWord point)
      ≡ Length.segmentCountSum (Contours.activeSegments displacement)
    lengthExact = Length.contourWordLengthEqualsSegmentCountSum
      (Contours.activeSegments displacement)

    countBound :
      Length.segmentCountSum (Contours.activeSegments displacement) ≤ 24
    countBound =
      subst
        (λ selected →
          Length.segmentCountSum (Contours.activeSegments selected) ≤ 24)
        (sym (centeredDisplacementNamesAgree point))
        (subst
          (λ upper →
            Length.segmentCountSum
              (Contours.activeSegments (Length24.centeredPointDisplacement point))
            ≤ upper)
          Length24.minimalFourRadiusIsTwentyFour
          (Length24.centeredPointCountSumBound point))
  in
  subst (λ selected → selected ≤ 24) (sym lengthExact) countBound

canonicalContourLengthAtMost24 :
  (point : Centered.CenteredBlockPoint4 6) →
  R164.listLength (Embed.canonicalCenteredContourWord point) ≤ 24
canonicalContourLengthAtMost24 point =
  subst
    (λ selected → selected ≤ 24)
    (sym (r164ListLengthIsPeriodicLength
      (Embed.canonicalCenteredContourWord point)))
    (canonicalContourPeriodicLengthAtMost24 point)

cmp98CanonicalContourLength24Round172Level : ProofLevel
cmp98CanonicalContourLength24Round172Level = machineChecked
