module DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact where

------------------------------------------------------------------------
-- EXTERNAL EXCEPTIONAL-ALGEBRA REFERENCE SHAPE
--
-- Standard representation-theoretic dimensions used here:
--
--   dim Albert J                 = 27
--   J under F4                   = 1 + 26
--   dim F4                       = 52
--   dim E6                       = 78 = 52 + 26
--   Freudenthal Q(J)             = 1 + 1 + 27 + 27 = 56
--   non-singlet Albert pair      = 27 + 27 = 54
--   one-scalar reduced candidate = 1 + 26 + 26 = 53
--
-- The arithmetic consequences are theorem-level.  The 53-dimensional object
-- is deliberately typed as a REDUCED CANDIDATE carrier, not as a named
-- irreducible representation of F4/E6/E7.  Promotion to an actual action
-- requires a quotient/restriction/intertwining receipt elsewhere.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. Dimension ledger.
------------------------------------------------------------------------

albertDimension : Nat
albertDimension = 27

tracelessAlbertDimension : Nat
tracelessAlbertDimension = 26

fFourDimension : Nat
fFourDimension = 52

eSixDimension : Nat
eSixDimension = 78

freudenthalDimension : Nat
freudenthalDimension = 56

albertPairDimension : Nat
albertPairDimension = 54

reducedAlbertPairDimension : Nat
reducedAlbertPairDimension = 53

albertSplitsScalarPlusTraceless : 27 ≡ 1 + 26
albertSplitsScalarPlusTraceless = refl

fFourIsTwoTracelessAlbertDimensions : 52 ≡ 2 * 26
fFourIsTwoTracelessAlbertDimensions = refl

eSixIsF4PlusTracelessAlbert : 78 ≡ 52 + 26
eSixIsF4PlusTracelessAlbert = refl

albertPairIsTwoAlbert : 54 ≡ 27 + 27
albertPairIsTwoAlbert = refl

albertPairAsTwoScalarPlusTwoTraceless : 54 ≡ 2 + (26 + 26)
albertPairAsTwoScalarPlusTwoTraceless = refl

reducedAlbertPairIsOnePlusTwoTraceless : 53 ≡ 1 + (26 + 26)
reducedAlbertPairIsOnePlusTwoTraceless = refl

freudenthalIsTwoScalarPlusAlbertPair : 56 ≡ 1 + 1 + 27 + 27
freudenthalIsTwoScalarPlusAlbertPair = refl

freudenthalIsTwoPlusFiftyFour : 56 ≡ 2 + 54
freudenthalIsTwoPlusFiftyFour = refl

------------------------------------------------------------------------
-- 2. Minimal typed skeleton for J = 1 + J0 and a dual/conjugate pair.
------------------------------------------------------------------------

data ScalarLine : Set where
  scalarLine : ScalarLine

-- Abstract carrier: this file records the representation SHAPE, not an
-- implementation of octonionic multiplication.
record AlbertCarrier : Set₁ where
  field
    J0 : Set

open AlbertCarrier public

Albert27 : AlbertCarrier → Set
Albert27 A = ScalarLine ⊎ J0 A

record AlbertPairCarrier : Set₁ where
  field
    leftAlbert rightAlbert : AlbertCarrier

open AlbertPairCarrier public

AlbertPair54 : AlbertPairCarrier → Set
AlbertPair54 pair = Albert27 (leftAlbert pair) ⊎ Albert27 (rightAlbert pair)

-- Remove one distinguished scalar line from the pair, leaving the other
-- scalar plus both traceless sectors.  This is the 53-candidate anatomy.
ReducedAlbertPair53 : AlbertPairCarrier → Set
ReducedAlbertPair53 pair =
  J0 (leftAlbert pair) ⊎ Albert27 (rightAlbert pair)

------------------------------------------------------------------------
-- 3. Promotion contract: an actual exceptional action must respect the same
--    54 carrier, the removed scalar, and the 53 residual inclusion.
------------------------------------------------------------------------

record ExceptionalFiftyFourToFiftyThreeRecognition : Set₁ where
  field
    Actor Actual54 Actual53 : Set
    act54 : Actor → Actual54 → Actual54
    act53 : Actor → Actual53 → Actual53

    invariantScalar54 : Actual54
    invariantScalarFixed :
      (actor : Actor) → act54 actor invariantScalar54 ≡ invariantScalar54

    include53 : Actual53 → Actual54
    sameActionRestriction :
      (actor : Actor) → (state : Actual53) →
      include53 (act53 actor state) ≡ act54 actor (include53 state)

    AlbertPair : AlbertPairCarrier
    toAlbertPair54 : Actual54 → AlbertPair54 AlbertPair
    fromAlbertPair54 : AlbertPair54 AlbertPair → Actual54
    fromAfterTo54 : (state : Actual54) → fromAlbertPair54 (toAlbertPair54 state) ≡ state
    toAfterFrom54 : (state : AlbertPair54 AlbertPair) → toAlbertPair54 (fromAlbertPair54 state) ≡ state

    toReducedAlbert53 : Actual53 → ReducedAlbertPair53 AlbertPair
    fromReducedAlbert53 : ReducedAlbertPair53 AlbertPair → Actual53
    fromAfterTo53 : (state : Actual53) → fromReducedAlbert53 (toReducedAlbert53 state) ≡ state
    toAfterFrom53 : (state : ReducedAlbertPair53 AlbertPair) → toReducedAlbert53 (fromReducedAlbert53 state) ≡ state

------------------------------------------------------------------------
-- 4. Scientific boundary.
------------------------------------------------------------------------

record ExceptionalResidualBoundary : Set where
  constructor exceptionalResidualBoundary
  field
    albert27StandardDimensionRecorded : Bool
    traceless26StandardDimensionRecorded : Bool
    f4Dimension52Recorded : Bool
    e6Dimension78Recorded : Bool
    freudenthal56ShapeRecorded : Bool
    fiftyFourAsAlbertPairRecorded : Bool
    fiftyThreeAsOneScalarPlusTwo26CandidateRecorded : Bool
    fiftyThreeDeclaredNamedExceptionalIrrepHere : Bool
    monsterResidualIdentifiedWithAlbertResidualHere : Bool
    cardinalAgreementPromotesAction : Bool

canonicalExceptionalResidualBoundary : ExceptionalResidualBoundary
canonicalExceptionalResidualBoundary =
  exceptionalResidualBoundary
    true true true true true true true
    false false false
