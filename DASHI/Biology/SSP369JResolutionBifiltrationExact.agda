module DASHI.Biology.SSP369JResolutionBifiltrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Stephane G. Mallat,
-- "A Theory for Multiresolution Signal Decomposition: The Wavelet
-- Representation", IEEE TPAMI 11(7), 1989, 674-693.
-- DOI: 10.1109/34.192463.
--
-- DASHI CONTRIBUTION
--
-- Make the proposed separation
--
--   3/6/9  = cumulative relational/coordinate horizon
--   r      = independent resolution depth
--
-- literal.  H3 carries one three-coordinate block, H6 carries two, and H9
-- carries three.  Every coordinate is itself an r-indexed decimal address.
-- Resolution coarsening acts pointwise on all coordinates; depth projection
-- forgets the newest three-coordinate block.  The two operations commute
-- definitionally.
--
-- Chosen all-zero blocks also give split inclusions H3 -> H6 -> H9, and those
-- inclusions commute with resolution coarsening.  This is a concrete finite
-- bifiltration witness, not a claim that 3/6/9 must have this semantics in
-- every DASHI model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IndexedJStratifiedMultiresolutionExact as J

------------------------------------------------------------------------
-- Three-coordinate block and pointwise maps.
------------------------------------------------------------------------

record Triple (A : Set) : Set where
  constructor triple
  field
    first second third : A

open Triple public

mapTriple :
  ∀ {A B : Set} →
  (A → B) →
  Triple A →
  Triple B
mapTriple f (triple a b c) = triple (f a) (f b) (f c)

mapTripleIdentity :
  ∀ {A : Set} (x : Triple A) →
  mapTriple (λ a → a) x ≡ x
mapTripleIdentity (triple a b c) = refl

------------------------------------------------------------------------
-- Cumulative 3/6/9 carriers at fixed resolution r.
------------------------------------------------------------------------

H3 : Nat → Set
H3 r = Triple (J.DecimalAddress r)

record H6 (r : Nat) : Set where
  constructor h6
  field
    firstThree : H3 r
    secondThree : Triple (J.DecimalAddress r)

open H6 public

record H9 (r : Nat) : Set where
  constructor h9
  field
    firstSix : H6 r
    thirdThree : Triple (J.DecimalAddress r)

open H9 public

------------------------------------------------------------------------
-- Depth projections: forgetting the newest horizon.
------------------------------------------------------------------------

project6to3 :
  ∀ {r} →
  H6 r →
  H3 r
project6to3 (h6 firstBlock secondBlock) = firstBlock

project9to6 :
  ∀ {r} →
  H9 r →
  H6 r
project9to6 (h9 firstBlocks thirdBlock) = firstBlocks

------------------------------------------------------------------------
-- Resolution coarsening at each fixed 3/6/9 horizon.
------------------------------------------------------------------------

coarsen3 :
  ∀ {r} →
  H3 (suc r) →
  H3 r
coarsen3 = mapTriple J.prefix

coarsen6 :
  ∀ {r} →
  H6 (suc r) →
  H6 r
coarsen6 (h6 firstBlock secondBlock) =
  h6
    (coarsen3 firstBlock)
    (mapTriple J.prefix secondBlock)

coarsen9 :
  ∀ {r} →
  H9 (suc r) →
  H9 r
coarsen9 (h9 firstBlocks thirdBlock) =
  h9
    (coarsen6 firstBlocks)
    (mapTriple J.prefix thirdBlock)

------------------------------------------------------------------------
-- The two fundamental commuting squares.
------------------------------------------------------------------------

coarsenDepthCommutes63 :
  ∀ {r} (x : H6 (suc r)) →
  project6to3 (coarsen6 x)
  ≡ coarsen3 (project6to3 x)
coarsenDepthCommutes63 (h6 firstBlock secondBlock) = refl

coarsenDepthCommutes96 :
  ∀ {r} (x : H9 (suc r)) →
  project9to6 (coarsen9 x)
  ≡ coarsen6 (project9to6 x)
coarsenDepthCommutes96 (h9 firstBlocks thirdBlock) = refl

------------------------------------------------------------------------
-- Chosen split inclusions using the all-zero address at the same resolution.
------------------------------------------------------------------------

zeroTriple :
  (r : Nat) →
  Triple (J.DecimalAddress r)
zeroTriple r =
  triple
    (J.allZeroAddress r)
    (J.allZeroAddress r)
    (J.allZeroAddress r)

include3to6 :
  ∀ {r} →
  H3 r →
  H6 r
include3to6 {r} firstBlock =
  h6 firstBlock (zeroTriple r)

include6to9 :
  ∀ {r} →
  H6 r →
  H9 r
include6to9 {r} firstBlocks =
  h9 firstBlocks (zeroTriple r)

projectInclude63 :
  ∀ {r} (x : H3 r) →
  project6to3 (include3to6 x) ≡ x
projectInclude63 x = refl

projectInclude96 :
  ∀ {r} (x : H6 r) →
  project9to6 (include6to9 x) ≡ x
projectInclude96 x = refl

coarsenZeroTriple :
  (r : Nat) →
  mapTriple J.prefix (zeroTriple (suc r))
  ≡ zeroTriple r
coarsenZeroTriple r = refl

coarsenInclude36Commutes :
  ∀ {r} (x : H3 (suc r)) →
  coarsen6 (include3to6 x)
  ≡ include3to6 (coarsen3 x)
coarsenInclude36Commutes x = refl

coarsenInclude69Commutes :
  ∀ {r} (x : H6 (suc r)) →
  coarsen9 (include6to9 x)
  ≡ include6to9 (coarsen6 x)
coarsenInclude69Commutes x = refl

------------------------------------------------------------------------
-- Package the two-index object.  This is the finite commuting-diagram core
-- of X_{d,r}; d is represented by the 3/6/9 horizon and r by resolution.
------------------------------------------------------------------------

record J369Bifiltration : Set₁ where
  field
    Carrier3 : Nat → Set
    Carrier6 : Nat → Set
    Carrier9 : Nat → Set

    resolution3 : ∀ {r} → Carrier3 (suc r) → Carrier3 r
    resolution6 : ∀ {r} → Carrier6 (suc r) → Carrier6 r
    resolution9 : ∀ {r} → Carrier9 (suc r) → Carrier9 r

    depth6to3 : ∀ {r} → Carrier6 r → Carrier3 r
    depth9to6 : ∀ {r} → Carrier9 r → Carrier6 r

    include3to6At : ∀ {r} → Carrier3 r → Carrier6 r
    include6to9At : ∀ {r} → Carrier6 r → Carrier9 r

    depthInclude63 :
      ∀ {r} (x : Carrier3 r) →
      depth6to3 (include3to6At x) ≡ x

    depthInclude96 :
      ∀ {r} (x : Carrier6 r) →
      depth9to6 (include6to9At x) ≡ x

    resolutionDepth63 :
      ∀ {r} (x : Carrier6 (suc r)) →
      depth6to3 (resolution6 x)
      ≡ resolution3 (depth6to3 x)

    resolutionDepth96 :
      ∀ {r} (x : Carrier9 (suc r)) →
      depth9to6 (resolution9 x)
      ≡ resolution6 (depth9to6 x)

    resolutionInclude36 :
      ∀ {r} (x : Carrier3 (suc r)) →
      resolution6 (include3to6At x)
      ≡ include3to6At (resolution3 x)

    resolutionInclude69 :
      ∀ {r} (x : Carrier6 (suc r)) →
      resolution9 (include6to9At x)
      ≡ include6to9At (resolution6 x)

open J369Bifiltration public

canonicalJ369Bifiltration : J369Bifiltration
canonicalJ369Bifiltration = record
  { Carrier3 = H3
  ; Carrier6 = H6
  ; Carrier9 = H9
  ; resolution3 = coarsen3
  ; resolution6 = coarsen6
  ; resolution9 = coarsen9
  ; depth6to3 = project6to3
  ; depth9to6 = project9to6
  ; include3to6At = include3to6
  ; include6to9At = include6to9
  ; depthInclude63 = projectInclude63
  ; depthInclude96 = projectInclude96
  ; resolutionDepth63 = coarsenDepthCommutes63
  ; resolutionDepth96 = coarsenDepthCommutes96
  ; resolutionInclude36 = coarsenInclude36Commutes
  ; resolutionInclude69 = coarsenInclude69Commutes
  }

------------------------------------------------------------------------
-- Concrete coordinates showing that depth and resolution are independent.
------------------------------------------------------------------------

exampleResolutionOneAddress : J.DecimalAddress 1
exampleResolutionOneAddress = J.extend J.root J.d7

exampleH3AtResolutionOne : H3 1
exampleH3AtResolutionOne =
  triple
    exampleResolutionOneAddress
    (J.extend J.root J.d3)
    (J.extend J.root J.d9)

exampleH6AtResolutionOne : H6 1
exampleH6AtResolutionOne = include3to6 exampleH3AtResolutionOne

exampleH9AtResolutionOne : H9 1
exampleH9AtResolutionOne = include6to9 exampleH6AtResolutionOne

exampleHorizonProjection96 :
  project9to6 exampleH9AtResolutionOne ≡ exampleH6AtResolutionOne
exampleHorizonProjection96 = refl

------------------------------------------------------------------------
-- Boundary: this layer deliberately refuses to collapse the two axes.
------------------------------------------------------------------------

record J369BifiltrationBoundary : Set where
  constructor j369BifiltrationBoundary
  field
    threeSixNineIsSameAxisAsDecimalResolution : Bool
    threeSixNineIsSameAxisAsDecimalResolutionIsFalse :
      threeSixNineIsSameAxisAsDecimalResolution ≡ false

    increasingResolutionAutomaticallyAddsRelationalCoordinates : Bool
    increasingResolutionAutomaticallyAddsRelationalCoordinatesIsFalse :
      increasingResolutionAutomaticallyAddsRelationalCoordinates ≡ false

    increasingRelationalDepthAutomaticallyRefinesDecimalAddress : Bool
    increasingRelationalDepthAutomaticallyRefinesDecimalAddressIsFalse :
      increasingRelationalDepthAutomaticallyRefinesDecimalAddress ≡ false

    canonicalZeroBlockMakesEveryPhysicalDepthExtensionCanonical : Bool
    canonicalZeroBlockMakesEveryPhysicalDepthExtensionCanonicalIsFalse :
      canonicalZeroBlockMakesEveryPhysicalDepthExtensionCanonical ≡ false

    commutingFiniteBifiltrationProvesTwoInfiniteLimitsCommute : Bool
    commutingFiniteBifiltrationProvesTwoInfiniteLimitsCommuteIsFalse :
      commutingFiniteBifiltrationProvesTwoInfiniteLimitsCommute ≡ false

canonicalJ369BifiltrationBoundary : J369BifiltrationBoundary
canonicalJ369BifiltrationBoundary =
  j369BifiltrationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
