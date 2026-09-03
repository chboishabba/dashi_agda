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
-- Arithmetic consequences are theorem-level.  The 53-dimensional object is a
-- REDUCED CANDIDATE carrier, not a claimed named F4/E6/E7 irreducible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

albertDimension tracelessAlbertDimension fFourDimension eSixDimension : Nat
albertDimension = 27
tracelessAlbertDimension = 26
fFourDimension = 52
eSixDimension = 78

freudenthalDimension albertPairDimension reducedAlbertPairDimension : Nat
freudenthalDimension = 56
albertPairDimension = 54
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

data ScalarLine : Set where
  scalarLine : ScalarLine

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

ReducedAlbertPair53 : AlbertPairCarrier → Set
ReducedAlbertPair53 pair = J0 (leftAlbert pair) ⊎ Albert27 (rightAlbert pair)

-- Typed Freudenthal carrier shape R + R + J + J.
Freudenthal56 : AlbertPairCarrier → Set
Freudenthal56 pair = ScalarLine ⊎ (ScalarLine ⊎ AlbertPair54 pair)

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

-- Ambient E7/Freudenthal-style promotion target.  It packages a single action
-- through 56 -> 54 -> 53; neither reduction is inferred from dimension.
record ExceptionalFreudenthalFiftySixReductionRecognition : Set₁ where
  field
    Actor Actual56 Actual54 Actual53 : Set
    act56 : Actor → Actual56 → Actual56
    act54 : Actor → Actual54 → Actual54
    act53 : Actor → Actual53 → Actual53

    AlbertPair : AlbertPairCarrier
    toFreudenthal56 : Actual56 → Freudenthal56 AlbertPair
    fromFreudenthal56 : Freudenthal56 AlbertPair → Actual56
    fromAfterTo56 : (state : Actual56) → fromFreudenthal56 (toFreudenthal56 state) ≡ state
    toAfterFrom56 : (state : Freudenthal56 AlbertPair) → toFreudenthal56 (fromFreudenthal56 state) ≡ state

    include54 : Actual54 → Actual56
    include53 : Actual53 → Actual54
    sameAction56To54 :
      (actor : Actor) → (state : Actual54) →
      include54 (act54 actor state) ≡ act56 actor (include54 state)
    sameAction54To53 :
      (actor : Actor) → (state : Actual53) →
      include53 (act53 actor state) ≡ act54 actor (include53 state)

    twoAmbientScalars : Set
    removedScalar54To53 : Set

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
    freudenthal56To54To53ActionInterfaceRecorded : Bool
    fiftyThreeDeclaredNamedExceptionalIrrepHere : Bool
    monsterResidualIdentifiedWithAlbertResidualHere : Bool
    cardinalAgreementPromotesAction : Bool

canonicalExceptionalResidualBoundary : ExceptionalResidualBoundary
canonicalExceptionalResidualBoundary =
  exceptionalResidualBoundary
    true true true true true true true true
    false false false
