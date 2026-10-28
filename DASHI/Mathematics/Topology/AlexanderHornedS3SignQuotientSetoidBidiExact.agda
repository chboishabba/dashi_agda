module DASHI.Mathematics.Topology.AlexanderHornedS3SignQuotientSetoidBidiExact where

------------------------------------------------------------------------
-- ALL-DEPTH QUOTIENT-RELATION EQUIVALENCE, SOURCE WRITTEN
--
-- ORIGINAL OWNERS (imported, not copied):
--   #1244 AlexanderHornedS3WordSignOrbitTransportExact:
--     signedOrbitToGlobalS3, globalS3ToSignedOrbit and all
--     translation/reflection witness operations.
--   #1244 AlexanderHornedNativeBalancedTernaryEndTowerExact:
--     native Vec-map.
--   DASHI.Core.FiniteC3OrbitStabilizerExact: C3 and its group laws.
--
-- Historic finite permutation and partition mathematics: Cauchy,
-- Frobenius, Burnside, Pólya. Statistics/RGS specialization is the
-- independent #1275 source owner.
--
-- This file actually supplies: an equivalence relation for sign
-- orbits, one for the affine S3 word action, an explicit quotient
-- relation BIDI, a surjective normalisation section and the
-- invariant-consumer factorisation law.
--
-- No quotient HIT, function-extensionality assumption, postulate,
-- or identification of wild topology with word labels is used.
-- This is a setoid-level orbit equivalence, not an isomorphism of
-- the raw word and difference carriers. Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedS3WordSignOrbitTransportExact as Original

negateDifferences : ∀ {n} → Vec C3.C3 n → Vec C3.C3 n
negateDifferences = End.mapVec C3.inverse

c3NegationInvolutive : (x : C3.C3) →
  C3.inverse (C3.inverse x) ≡ x
c3NegationInvolutive C3.c0 = refl
c3NegationInvolutive C3.c1 = refl
c3NegationInvolutive C3.c2 = refl

negationInvolutive : ∀ {n} (xs : Vec C3.C3 n) →
  negateDifferences (negateDifferences xs) ≡ xs
negationInvolutive [] = refl
negationInvolutive (x ∷ xs) =
  cong₂ _∷_ (c3NegationInvolutive x) (negationInvolutive xs)

-- This is the actual equivalence relation on the relative words.
data SameC2Orbit {n} (xs ys : Vec C3.C3 n) : Set where
  same : xs ≡ ys → SameC2Orbit xs ys
  flipped : negateDifferences xs ≡ ys → SameC2Orbit xs ys

c2Reflexive : ∀ {n} (xs : Vec C3.C3 n) →
  SameC2Orbit xs xs
c2Reflexive xs = same refl

c2Symmetric : ∀ {n} (xs ys : Vec C3.C3 n) →
  SameC2Orbit xs ys → SameC2Orbit ys xs
c2Symmetric xs ys (same eq) = same (sym eq)
c2Symmetric xs ys (flipped eq) =
  flipped
    (trans (sym (cong negateDifferences eq))
           (negationInvolutive xs))

c2Transitive : ∀ {n} (xs ys zs : Vec C3.C3 n) →
  SameC2Orbit xs ys → SameC2Orbit ys zs →
  SameC2Orbit xs zs
c2Transitive xs ys zs (same ab) (same bc) =
  same (trans ab bc)
c2Transitive xs ys zs (same ab) (flipped bc) =
  flipped (trans (cong negateDifferences ab) bc)
c2Transitive xs ys zs (flipped ab) (same bc) =
  flipped (trans ab bc)
c2Transitive xs ys zs (flipped ab) (flipped bc) =
  same
    (trans (sym (negationInvolutive xs))
      (trans (cong negateDifferences ab) bc))

-- #1244 already proves both directions for the FULL affine S3
-- orbit witness: translation b, or translation after reflection.
-- Do not redefine the original action or call a C2 sign an S3
-- action without these two explicit witnesses.
s3ToC2 : ∀ {n} (w z : Original.AnchoredWord n) →
  Original.GlobalS3Related w z →
  SameC2Orbit (Original.normalise w) (Original.normalise z)
s3ToC2 w z relation
  with Original.globalS3ToSignedOrbit w z relation
... | Original.sameRelative eq = same eq
... | Original.reflectedRelative eq = flipped eq

c2ToS3 : ∀ {n} (w z : Original.AnchoredWord n) →
  SameC2Orbit (Original.normalise w) (Original.normalise z) →
  Original.GlobalS3Related w z
c2ToS3 w z (same eq) =
  Original.signedOrbitToGlobalS3 w z (Original.sameRelative eq)
c2ToS3 w z (flipped eq) =
  Original.signedOrbitToGlobalS3 w z (Original.reflectedRelative eq)

s3Reflexive : ∀ {n} (w : Original.AnchoredWord n) →
  Original.GlobalS3Related w w
s3Reflexive w = c2ToS3 w w (c2Reflexive (Original.normalise w))

s3Symmetric : ∀ {n} (w z : Original.AnchoredWord n) →
  Original.GlobalS3Related w z →
  Original.GlobalS3Related z w
s3Symmetric w z eq =
  c2ToS3 z w
    (c2Symmetric (Original.normalise w) (Original.normalise z)
      (s3ToC2 w z eq))

s3Transitive : ∀ {n} (w z v : Original.AnchoredWord n) →
  Original.GlobalS3Related w z →
  Original.GlobalS3Related z v →
  Original.GlobalS3Related w v
s3Transitive w z v a b =
  c2ToS3 w v
    (c2Transitive
      (Original.normalise w) (Original.normalise z)
      (Original.normalise v)
      (s3ToC2 w z a) (s3ToC2 z v b))

-- Every difference vector has an actual word representative, with
-- anchor C3.c0. This is not a numerical cardinality argument.
relativeZeroAnchor : ∀ {n} (xs : Vec C3.C3 n) →
  Original.normalise (Original.normalisedWord xs) ≡ xs
relativeZeroAnchor [] = refl
relativeZeroAnchor (x ∷ xs) =
  cong₂ _∷_ (C3.rightIdentity x) (relativeZeroAnchor xs)

normalisationSurjective : ∀ {n} (xs : Vec C3.C3 n) →
  Σ (Original.AnchoredWord n)
    (λ w → Original.normalise w ≡ xs)
normalisationSurjective xs =
  Original.normalisedWord xs , relativeZeroAnchor xs

-- The carrier section is not a left inverse on raw anchored words:
-- only the affine S3 *orbit* is recovered.
normalisationSectionUpToS3 :
  ∀ {n} (w : Original.AnchoredWord n) →
  Original.GlobalS3Related w
    (Original.normalisedWord (Original.normalise w))
normalisationSectionUpToS3 w =
  c2ToS3 w (Original.normalisedWord (Original.normalise w))
    (same (sym (relativeZeroAnchor (Original.normalise w))))

-- Every C2-invariant observation of relative words is an S3
-- invariant observation of original named words, for ALL depths.
observeRelative : ∀ {n} {A : Set} →
  (Vec C3.C3 n → A) → Original.AnchoredWord n → A
observeRelative consumer w = consumer (Original.normalise w)

relativeConsumerRespectsC2 : ∀ {n} {A : Set} →
  (consumer : Vec C3.C3 n → A) →
  ((xs : Vec C3.C3 n) →
    consumer (negateDifferences xs) ≡ consumer xs) →
  (xs ys : Vec C3.C3 n) →
  SameC2Orbit xs ys → consumer xs ≡ consumer ys
relativeConsumerRespectsC2 consumer invariant xs ys (same eq) =
  cong consumer eq
relativeConsumerRespectsC2 consumer invariant xs ys (flipped eq) =
  trans (sym (invariant xs)) (cong consumer eq)

relativeConsumerRespectsS3 : ∀ {n} {A : Set} →
  (consumer : Vec C3.C3 n → A) →
  ((xs : Vec C3.C3 n) →
    consumer (negateDifferences xs) ≡ consumer xs) →
  (w z : Original.AnchoredWord n) →
  Original.GlobalS3Related w z →
  observeRelative consumer w ≡ observeRelative consumer z
relativeConsumerRespectsS3 consumer invariant w z related =
  relativeConsumerRespectsC2 consumer invariant
    (Original.normalise w) (Original.normalise z)
    (s3ToC2 w z related)

-- Explicit source-reuse summary of the actual equivalence.
record WordDifferenceOrbitBidi (n : Nat) : Set₁ where
  field
    forward : Original.AnchoredWord n → Vec C3.C3 n
    section : Vec C3.C3 n → Original.AnchoredWord n
    forwardSection : (xs : Vec C3.C3 n) → forward (section xs) ≡ xs
    sectionForward :
      (w : Original.AnchoredWord n) →
      Original.GlobalS3Related w (section (forward w))
    preserveOrbit :
      (w z : Original.AnchoredWord n) →
      Original.GlobalS3Related w z →
      SameC2Orbit (forward w) (forward z)
    reflectOrbit :
      (w z : Original.AnchoredWord n) →
      SameC2Orbit (forward w) (forward z) →
      Original.GlobalS3Related w z

actualWordDifferenceOrbitBidi : (n : Nat) → WordDifferenceOrbitBidi n
actualWordDifferenceOrbitBidi n = record
  { forward = Original.normalise
  ; section = Original.normalisedWord
  ; forwardSection = relativeZeroAnchor
  ; sectionForward = normalisationSectionUpToS3
  ; preserveOrbit = s3ToC2
  ; reflectOrbit = c2ToS3
  }

------------------------------------------------------------------------
-- CONCRETE ALL-DEPTH QUOTIENT NORMAL FORM.
--
-- Class representative: the zero vector, or a vector whose FIRST
-- nonzero trit is c1. A c2 first nonzero trit is reflected to c1;
-- all later coordinates are then simultaneously negated.
-- This is a canonical finite DATA type, not a postulated quotient.
------------------------------------------------------------------------

data CanonicalRelative : Nat → Set where
  empty : CanonicalRelative 0
  zeroPrefix : ∀ {n} →
    CanonicalRelative n → CanonicalRelative (suc n)
  firstPositive : ∀ {n} →
    Vec C3.C3 n → CanonicalRelative (suc n)

canonicalRepresentative : ∀ {n} →
  CanonicalRelative n → Vec C3.C3 n
canonicalRepresentative empty = []
canonicalRepresentative (zeroPrefix cs) =
  C3.c0 ∷ canonicalRepresentative cs
canonicalRepresentative (firstPositive xs) = C3.c1 ∷ xs

canonicaliseRelative : ∀ {n} →
  Vec C3.C3 n → CanonicalRelative n
canonicaliseRelative [] = empty
canonicaliseRelative (C3.c0 ∷ xs) =
  zeroPrefix (canonicaliseRelative xs)
canonicaliseRelative (C3.c1 ∷ xs) = firstPositive xs
canonicaliseRelative (C3.c2 ∷ xs) =
  firstPositive (negateDifferences xs)

canonicalSection : ∀ {n} (c : CanonicalRelative n) →
  canonicaliseRelative (canonicalRepresentative c) ≡ c
canonicalSection empty = refl
canonicalSection (zeroPrefix c) = cong zeroPrefix (canonicalSection c)
canonicalSection (firstPositive xs) = refl

canonicaliseNegationInvariant :
  ∀ {n} (xs : Vec C3.C3 n) →
  canonicaliseRelative (negateDifferences xs)
    ≡ canonicaliseRelative xs
canonicaliseNegationInvariant [] = refl
canonicaliseNegationInvariant (C3.c0 ∷ xs) =
  cong zeroPrefix (canonicaliseNegationInvariant xs)
canonicaliseNegationInvariant (C3.c1 ∷ xs) =
  cong firstPositive (negationInvolutive xs)
canonicaliseNegationInvariant (C3.c2 ∷ xs) = refl

canonicaliseRespectsSign : ∀ {n} (xs ys : Vec C3.C3 n) →
  SameC2Orbit xs ys →
  canonicaliseRelative xs ≡ canonicaliseRelative ys
canonicaliseRespectsSign xs ys (same eq) =
  cong canonicaliseRelative eq
canonicaliseRespectsSign xs ys (flipped eq) =
  trans (sym (canonicaliseNegationInvariant xs))
        (cong canonicaliseRelative eq)

canonicalCover : ∀ {n} (xs : Vec C3.C3 n) →
  SameC2Orbit xs (canonicalRepresentative (canonicaliseRelative xs))
canonicalCover [] = same refl
canonicalCover (C3.c0 ∷ xs) with canonicalCover xs
... | same eq = same (cong (C3.c0 ∷_) eq)
... | flipped eq = flipped (cong (C3.c0 ∷_) eq)
canonicalCover (C3.c1 ∷ xs) = same refl
canonicalCover (C3.c2 ∷ xs) = flipped refl

canonicaliseComplete : ∀ {n} (xs ys : Vec C3.C3 n) →
  canonicaliseRelative xs ≡ canonicaliseRelative ys →
  SameC2Orbit xs ys
canonicaliseComplete xs ys equal =
  c2Transitive xs
    (canonicalRepresentative (canonicaliseRelative xs)) ys
    (canonicalCover xs)
    (c2Transitive
      (canonicalRepresentative (canonicaliseRelative xs))
      (canonicalRepresentative (canonicaliseRelative ys)) ys
      (same (cong canonicalRepresentative equal))
      (c2Symmetric ys
        (canonicalRepresentative (canonicaliseRelative ys))
        (canonicalCover ys)))

-- Constructive *untruncated* classification:
-- original S3-orbit relation iff equality of canonical relative codes.
canonicalWordClass : ∀ {n} →
  Original.AnchoredWord n → CanonicalRelative n
canonicalWordClass w =
  canonicaliseRelative (Original.normalise w)

wordOrbitGivesCanonicalEquality : ∀ {n}
  (w z : Original.AnchoredWord n) →
  Original.GlobalS3Related w z →
  canonicalWordClass w ≡ canonicalWordClass z
wordOrbitGivesCanonicalEquality w z related =
  canonicaliseRespectsSign (Original.normalise w)
    (Original.normalise z) (s3ToC2 w z related)

canonicalEqualityGivesWordOrbit : ∀ {n}
  (w z : Original.AnchoredWord n) →
  canonicalWordClass w ≡ canonicalWordClass z →
  Original.GlobalS3Related w z
canonicalEqualityGivesWordOrbit w z equal =
  c2ToS3 w z
    (canonicaliseComplete
      (Original.normalise w)
      (Original.normalise z) equal)

wordForCanonicalClass : ∀ {n} →
  CanonicalRelative n → Original.AnchoredWord n
wordForCanonicalClass c =
  Original.normalisedWord (canonicalRepresentative c)

canonicalWordSection : ∀ {n} (c : CanonicalRelative n) →
  canonicalWordClass (wordForCanonicalClass c) ≡ c
canonicalWordSection c =
  trans
    (cong canonicaliseRelative
      (relativeZeroAnchor (canonicalRepresentative c)))
    (canonicalSection c)

canonicalWordRepresentative : ∀ {n}
  (w : Original.AnchoredWord n) →
  Original.GlobalS3Related w
    (wordForCanonicalClass (canonicalWordClass w))
canonicalWordRepresentative w =
  canonicalEqualityGivesWordOrbit w
    (wordForCanonicalClass (canonicalWordClass w))
    (sym (canonicalWordSection (canonicalWordClass w)))

-- The canonical type has ONE empty code at level zero. Each added
-- position permits either a leading zero followed by an older code,
-- or a leading positive digit followed by n free trits.
-- This *structural* normal form is the source of the orbit ranks
-- 1,2,5,14,41,122,365. A general cardinality proof still needs a
-- list/vector enumeration and is not pretended here.
