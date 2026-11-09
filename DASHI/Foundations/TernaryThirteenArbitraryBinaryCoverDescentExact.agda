module DASHI.Foundations.TernaryThirteenArbitraryBinaryCoverDescentExact where

------------------------------------------------------------------------
-- ANY decidable binary covering of the ORIGINAL twelve-axis site:
-- overlap equality + common central trit suffice for constructive
-- gluing and exact local recovery on either chart.
--
-- This is stronger than the earlier specific {0..6}/{6..11}
-- two-chart example. It is still a binary covering *presheaf*
-- statement, NOT a Grothendieck topology over every sieve.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

Axis : Set
Axis = Atlas.StageAtlasZeroToEleven

record BinaryCover : Set where
  constructor binaryCover
  field
    leftMember : Axis → Bool
    rightMember : Axis → Bool
    covers : (axis : Axis) →
      (leftMember axis ≡ true) ⊎ (rightMember axis ≡ true)
open BinaryCover public

record BinaryLocalFamily (cover : BinaryCover) : Set where
  constructor binaryLocalFamily
  field
    leftValue : Axis → Base.TriTruth
    rightValue : Axis → Base.TriTruth
    leftCentre : Base.TriTruth
    rightCentre : Base.TriTruth
open BinaryLocalFamily public

record BinaryMatching (cover : BinaryCover)
    (family : BinaryLocalFamily cover) : Set where
  constructor binaryMatching
  field
    onOverlap :
      (axis : Axis) →
      leftMember cover axis ≡ true →
      rightMember cover axis ≡ true →
      leftValue family axis ≡ rightValue family axis
    commonCentre :
      leftCentre family ≡ rightCentre family
open BinaryMatching public

-- Choose a representative on the left whenever the left chart
-- contains the axis; otherwise the cover supplies the right chart.
-- The cover proof is used computationally, not assumed externally.
glueValue :
  (cover : BinaryCover) →
  BinaryLocalFamily cover →
  Axis → Base.TriTruth
glueValue cover family axis with covers cover axis
... | inj₁ leftYes = leftValue family axis
... | inj₂ rightYes = rightValue family axis

glueBinaryCentral :
  (cover : BinaryCover) (family : BinaryLocalFamily cover) →
  BinaryMatching cover family →
  Rel.SourceCentralCompletionCarrier
glueBinaryCentral cover family matching =
  glueValue cover family , leftCentre family

leftRecovers :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family)
  (axis : Axis) →
  leftMember cover axis ≡ true →
  glueValue cover family axis ≡ leftValue family axis
leftRecovers cover family matching axis leftYes
  with covers cover axis
... | inj₁ selectedLeft = refl
... | inj₂ selectedRight =
  sym (onOverlap matching axis leftYes selectedRight)

rightRecovers :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family)
  (axis : Axis) →
  rightMember cover axis ≡ true →
  glueValue cover family axis ≡ rightValue family axis
rightRecovers cover family matching axis rightYes
  with covers cover axis
... | inj₁ selectedLeft =
  onOverlap matching axis selectedLeft rightYes
... | inj₂ selectedRight = refl

leftGlobalRestriction :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family)
  (axis : Axis) →
  leftMember cover axis ≡ true →
  proj₁ (glueBinaryCentral cover family matching) axis
    ≡ leftValue family axis
leftGlobalRestriction cover family matching axis leftYes =
  leftRecovers cover family matching axis leftYes

rightGlobalRestriction :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family)
  (axis : Axis) →
  rightMember cover axis ≡ true →
  proj₁ (glueBinaryCentral cover family matching) axis
    ≡ rightValue family axis
rightGlobalRestriction cover family matching axis rightYes =
  rightRecovers cover family matching axis rightYes

leftCentralRestriction :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family) →
  proj₂ (glueBinaryCentral cover family matching)
    ≡ leftCentre family
leftCentralRestriction cover family matching = refl

rightCentralRestriction :
  (cover : BinaryCover) (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family) →
  proj₂ (glueBinaryCentral cover family matching)
    ≡ rightCentre family
rightCentralRestriction cover family matching =
  commonCentre matching

-- Every global source valuation generates matching local data on
-- every binary cover, no assumptions about its shape or overlap.
restrictBinaryCentral :
  (cover : BinaryCover) →
  Rel.SourceCentralCompletionCarrier →
  BinaryLocalFamily cover
restrictBinaryCentral cover (valuation , centre) =
  binaryLocalFamily valuation valuation centre centre

restrictedBinaryMatches :
  (cover : BinaryCover)
  (state : Rel.SourceCentralCompletionCarrier) →
  BinaryMatching cover (restrictBinaryCentral cover state)
restrictedBinaryMatches cover state =
  binaryMatching (λ axis _ _ → refl) refl

glueRestrictedPointwise :
  (cover : BinaryCover)
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Axis) →
  proj₁ (glueBinaryCentral cover
    (restrictBinaryCentral cover state)
    (restrictedBinaryMatches cover state)) axis
  ≡ proj₁ state axis
glueRestrictedPointwise cover state axis
  with covers cover axis
... | inj₁ _ = refl
... | inj₂ _ = refl

glueRestrictedCentre :
  (cover : BinaryCover)
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (glueBinaryCentral cover
    (restrictBinaryCentral cover state)
    (restrictedBinaryMatches cover state))
  ≡ proj₂ state
glueRestrictedCentre cover state = refl

-- Nonneutral centre is preserved by arbitrary binary-cover gluing
-- precisely because the matching law forces a common centre.
binaryCoverPuncturePreserved :
  (cover : BinaryCover)
  (family : BinaryLocalFamily cover)
  (matching : BinaryMatching cover family) →
  ¬ (leftCentre family ≡ Base.tri-mid) →
  ¬ (proj₂ (glueBinaryCentral cover family matching) ≡ Base.tri-mid)
binaryCoverPuncturePreserved cover family matching punctured = punctured
