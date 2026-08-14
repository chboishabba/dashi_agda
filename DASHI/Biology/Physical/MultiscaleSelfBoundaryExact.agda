module DASHI.Biology.Physical.MultiscaleSelfBoundaryExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Michael Levin,
-- "Darwin's agential materials: evolutionary implications of multiscale
-- competency in developmental biology", Cellular and Molecular Life Sciences
-- 80 (2023), 142.
-- DOI: 10.1007/s00018-023-04790-z.
--
-- Ownership is represented as membership in an effective multiscale self
-- boundary.  A generic hand-shaped object and this organism's hand therefore
-- differ by a relational identity coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data Scale : Set where
  cell tissue organism : Scale

data BodyPart : Set where
  hand heart skin : BodyPart

record SelfBoundary : Set where
  constructor selfBoundary
  field
    scale : Scale
    includesHand : Bool
    includesHeart : Bool
    includesSkin : Bool

open SelfBoundary public

cellSelf tissueSelf organismSelf : SelfBoundary
cellSelf = selfBoundary cell false false true
tissueSelf = selfBoundary tissue true false true
organismSelf = selfBoundary organism true true true

data ExpandsTo : SelfBoundary → SelfBoundary → Set where
  cellToTissue : ExpandsTo cellSelf tissueSelf
  tissueToOrganism : ExpandsTo tissueSelf organismSelf

inside : BodyPart → SelfBoundary → Bool
inside hand b = includesHand b
inside heart b = includesHeart b
inside skin b = includesSkin b

handOutsideCellSelf : inside hand cellSelf ≡ false
handOutsideCellSelf = refl

handInsideOrganismSelf : inside hand organismSelf ≡ true
handInsideOrganismSelf = refl

record HandCandidate : Set where
  constructor handCandidate
  field
    handShaped : Bool
    attached : Bool
    ownerBoundary : SelfBoundary

open HandCandidate public

genericHand ourHand : HandCandidate
genericHand = handCandidate true false cellSelf
ourHand = handCandidate true true organismSelf

genericAndOurHandShareShape : handShaped genericHand ≡ handShaped ourHand
genericAndOurHandShareShape = refl

genericAndOurHandDifferInAttachment : attached genericHand ≢ attached ourHand
genericAndOurHandDifferInAttachment ()

record IsOurHand (h : HandCandidate) : Set where
  constructor isOurHand
  field
    shapeRequired : handShaped h ≡ true
    attachmentRequired : attached h ≡ true
    selfIncludesHand : inside hand (ownerBoundary h) ≡ true

open IsOurHand public

ourHandWitness : IsOurHand ourHand
ourHandWitness = isOurHand refl refl refl

-- A generic hand predicate cannot reconstruct organism-relative ownership.
shapeAloneDoesNotDetermineOurHand :
  Σ HandCandidate (λ left →
    Σ HandCandidate (λ right →
      handShaped left ≡ handShaped right × attached left ≢ attached right))
shapeAloneDoesNotDetermineOurHand =
  genericHand , (ourHand , (refl , λ ()))
