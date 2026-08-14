module DASHI.Crypto.MLKEMNTTActualCBD2FullTripleListProfileExact where

------------------------------------------------------------------------
-- EXHAUSTIVE 5^3 CBD2 TRIPLE LIST PROFILE UNDER TWO ACTUAL FIPS SCALARS
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- We exhaust the complete three-coefficient CBD2 slice
--
--   (a,b,c) in {-2,-1,0,1,2}^3
--
-- at source degrees 0,8,12. The first two constant-component scalar maps use
-- the actual FIPS weights already derived in Round 17:
--
--   scalar0 = a + 296 b + 2319 c   mod 3329,
--   scalar2 = a + 296 b + 1010 c   mod 3329.
--
-- Rather than selecting one known collision, this module enumerates all 125
-- source triples and counts unordered scalar-collision pairs definitionally.
--
-- Result:
--   * scalar0 has exactly 16 colliding unordered candidate pairs;
--   * the joint pair (scalar0,scalar2) has zero colliding unordered pairs.
--
-- Thus, on this complete source-faithful 5^3 slice, the second actual FIPS
-- scalar resolves every collision left by the first. This is a finite local
-- decoding theorem, not an ML-KEM key-recovery result: the full scheme has a
-- much larger secret/error carrier and many additional equations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _==_)
open import DASHI.Foundations.Base369Nat using (_%_)

q : Nat
q = 3329

data D5 : Set where
  d0 d1 d2 d3 d4 : D5

residue : D5 → Nat
residue d0 = 3327
residue d1 = 3328
residue d2 = 0
residue d3 = 1
residue d4 = 2

record Triple : Set where
  constructor triple
  field
    a b c : D5
open Triple public

scalar0 : Triple → Nat
scalar0 x =
  (residue (a x) + 296 * residue (b x) + 2319 * residue (c x)) % q

scalar2 : Triple → Nat
scalar2 x =
  (residue (a x) + 296 * residue (b x) + 1010 * residue (c x)) % q

allTriples : List Triple
allTriples =
  triple d0 d0 d0 ∷ triple d0 d0 d1 ∷ triple d0 d0 d2 ∷ triple d0 d0 d3 ∷ triple d0 d0 d4 ∷
  triple d0 d1 d0 ∷ triple d0 d1 d1 ∷ triple d0 d1 d2 ∷ triple d0 d1 d3 ∷ triple d0 d1 d4 ∷
  triple d0 d2 d0 ∷ triple d0 d2 d1 ∷ triple d0 d2 d2 ∷ triple d0 d2 d3 ∷ triple d0 d2 d4 ∷
  triple d0 d3 d0 ∷ triple d0 d3 d1 ∷ triple d0 d3 d2 ∷ triple d0 d3 d3 ∷ triple d0 d3 d4 ∷
  triple d0 d4 d0 ∷ triple d0 d4 d1 ∷ triple d0 d4 d2 ∷ triple d0 d4 d3 ∷ triple d0 d4 d4 ∷
  triple d1 d0 d0 ∷ triple d1 d0 d1 ∷ triple d1 d0 d2 ∷ triple d1 d0 d3 ∷ triple d1 d0 d4 ∷
  triple d1 d1 d0 ∷ triple d1 d1 d1 ∷ triple d1 d1 d2 ∷ triple d1 d1 d3 ∷ triple d1 d1 d4 ∷
  triple d1 d2 d0 ∷ triple d1 d2 d1 ∷ triple d1 d2 d2 ∷ triple d1 d2 d3 ∷ triple d1 d2 d4 ∷
  triple d1 d3 d0 ∷ triple d1 d3 d1 ∷ triple d1 d3 d2 ∷ triple d1 d3 d3 ∷ triple d1 d3 d4 ∷
  triple d1 d4 d0 ∷ triple d1 d4 d1 ∷ triple d1 d4 d2 ∷ triple d1 d4 d3 ∷ triple d1 d4 d4 ∷
  triple d2 d0 d0 ∷ triple d2 d0 d1 ∷ triple d2 d0 d2 ∷ triple d2 d0 d3 ∷ triple d2 d0 d4 ∷
  triple d2 d1 d0 ∷ triple d2 d1 d1 ∷ triple d2 d1 d2 ∷ triple d2 d1 d3 ∷ triple d2 d1 d4 ∷
  triple d2 d2 d0 ∷ triple d2 d2 d1 ∷ triple d2 d2 d2 ∷ triple d2 d2 d3 ∷ triple d2 d2 d4 ∷
  triple d2 d3 d0 ∷ triple d2 d3 d1 ∷ triple d2 d3 d2 ∷ triple d2 d3 d3 ∷ triple d2 d3 d4 ∷
  triple d2 d4 d0 ∷ triple d2 d4 d1 ∷ triple d2 d4 d2 ∷ triple d2 d4 d3 ∷ triple d2 d4 d4 ∷
  triple d3 d0 d0 ∷ triple d3 d0 d1 ∷ triple d3 d0 d2 ∷ triple d3 d0 d3 ∷ triple d3 d0 d4 ∷
  triple d3 d1 d0 ∷ triple d3 d1 d1 ∷ triple d3 d1 d2 ∷ triple d3 d1 d3 ∷ triple d3 d1 d4 ∷
  triple d3 d2 d0 ∷ triple d3 d2 d1 ∷ triple d3 d2 d2 ∷ triple d3 d2 d3 ∷ triple d3 d2 d4 ∷
  triple d3 d3 d0 ∷ triple d3 d3 d1 ∷ triple d3 d3 d2 ∷ triple d3 d3 d3 ∷ triple d3 d3 d4 ∷
  triple d3 d4 d0 ∷ triple d3 d4 d1 ∷ triple d3 d4 d2 ∷ triple d3 d4 d3 ∷ triple d3 d4 d4 ∷
  triple d4 d0 d0 ∷ triple d4 d0 d1 ∷ triple d4 d0 d2 ∷ triple d4 d0 d3 ∷ triple d4 d0 d4 ∷
  triple d4 d1 d0 ∷ triple d4 d1 d1 ∷ triple d4 d1 d2 ∷ triple d4 d1 d3 ∷ triple d4 d1 d4 ∷
  triple d4 d2 d0 ∷ triple d4 d2 d1 ∷ triple d4 d2 d2 ∷ triple d4 d2 d3 ∷ triple d4 d2 d4 ∷
  triple d4 d3 d0 ∷ triple d4 d3 d1 ∷ triple d4 d3 d2 ∷ triple d4 d3 d3 ∷ triple d4 d3 d4 ∷
  triple d4 d4 d0 ∷ triple d4 d4 d1 ∷ triple d4 d4 d2 ∷ triple d4 d4 d3 ∷ triple d4 d4 d4 ∷ []

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

allTriplesCountIs125 : length allTriples ≡ 125
allTriplesCountIs125 = refl

and : Bool → Bool → Bool
and true true = true
and _ _ = false

sameFirst : Triple → Triple → Bool
sameFirst x y = scalar0 x == scalar0 y

sameTwo : Triple → Triple → Bool
sameTwo x y = and (scalar0 x == scalar0 y) (scalar2 x == scalar2 y)

countMatches : (Triple → Triple → Bool) → Triple → List Triple → Nat
countMatches eq x [] = 0
countMatches eq x (y ∷ ys) with eq x y
... | false = countMatches eq x ys
... | true = suc (countMatches eq x ys)

unorderedCollisionPairs :
  (Triple → Triple → Bool) → List Triple → Nat
unorderedCollisionPairs eq [] = 0
unorderedCollisionPairs eq (x ∷ xs) =
  countMatches eq x xs + unorderedCollisionPairs eq xs

firstScalarCollisionPairCount : Nat
firstScalarCollisionPairCount = unorderedCollisionPairs sameFirst allTriples

twoScalarCollisionPairCount : Nat
twoScalarCollisionPairCount = unorderedCollisionPairs sameTwo allTriples

firstScalarHasExactly16CollisionPairs :
  firstScalarCollisionPairCount ≡ 16
firstScalarHasExactly16CollisionPairs = refl

twoActualScalarsHaveNoCollisionPair :
  twoScalarCollisionPairCount ≡ 0
twoActualScalarsHaveNoCollisionPair = refl

record ExhaustiveTripleSliceProfile : Set where
  constructor exhaustiveTripleSliceProfile
  field
    candidateCount firstCollisionPairs twoScalarCollisionPairs : Nat
    candidateCountIs125 : candidateCount ≡ 125
    firstPairsIs16 : firstCollisionPairs ≡ 16
    twoPairsIs0 : twoScalarCollisionPairs ≡ 0

open ExhaustiveTripleSliceProfile public

actualCBD2TripleSliceProfile : ExhaustiveTripleSliceProfile
actualCBD2TripleSliceProfile =
  exhaustiveTripleSliceProfile 125 16 0 refl refl refl

------------------------------------------------------------------------
-- Zero collision pairs is exhaustive for this selected 3-coefficient slice.
-- It does not say two NTT coordinates identify an entire ML-KEM secret.
------------------------------------------------------------------------
