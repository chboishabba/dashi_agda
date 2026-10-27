module DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact where

------------------------------------------------------------------------
-- MONSTER 3B MULTIPLICITY 78-BLOCK <-> EXCEPTIONAL E6 ADJOINT CANDIDATE
--
-- The existing same-action BIDI lane owns a 90 = 12 + 78 decomposition only
-- after the literal Fin 90 inertia action has been attached.  Independently,
-- the standard exceptional Lie algebra E6 has dimension 78 and under F4 its
-- Lie-algebra dimension splits as 52 + 26.
--
-- This owner cross-pollinates those facts without identifying representations
-- by cardinality.  The actual 78 block becomes E6-semantic only after an
-- explicit two-sided recognition and action intertwiner are supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact as Split

------------------------------------------------------------------------
-- 1. Exact exceptional dimension anatomy.
------------------------------------------------------------------------

seventyEightIsE6Dimension : 78 ≡ Exceptional.eSixDimension
seventyEightIsE6Dimension = refl

seventyEightAsF4PlusTracelessAlbert : 78 ≡ 52 + 26
seventyEightAsF4PlusTracelessAlbert = Exceptional.eSixIsF4PlusTracelessAlbert

------------------------------------------------------------------------
-- 2. Recognition interface on the SAME actual 78 block.
------------------------------------------------------------------------

record ActualSeventyEightE6Recognition
  {source}
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source)
  : Set₁ where
  field
    E6Carrier : Set
    e6Action : Actual.MultiplicityInertia attachment → E6Carrier → E6Carrier

    toE6 : Actual.SeventyEightCarrier attachment → E6Carrier
    fromE6 : E6Carrier → Actual.SeventyEightCarrier attachment
    fromAfterTo :
      (state : Actual.SeventyEightCarrier attachment) →
      fromE6 (toE6 state) ≡ state
    toAfterFrom : (state : E6Carrier) → toE6 (fromE6 state) ≡ state

    actual78IntertwinesE6 :
      (inertia : Actual.MultiplicityInertia attachment) →
      (state : Actual.SeventyEightCarrier attachment) →
      toE6
        (Split.seventyEightAct
          (Actual.blockRecognition attachment) inertia state)
      ≡ e6Action inertia (toE6 state)

    -- A further F4 + 26 semantic decomposition is separate data.  The equation
    -- 78=52+26 does not itself construct subrepresentations.
    F4Carrier TracelessAlbertCarrier : Set
    f4Plus26Recognition : Set

------------------------------------------------------------------------
-- 3. Boundary.
------------------------------------------------------------------------

record SeventyEightExceptionalBoundary : Set where
  constructor seventyEightExceptionalBoundary
  field
    e6Dimension78ExternallyMotivated : Bool
    f4Dimension52AndMinimal26Recorded : Bool
    existingMonsterLaneHasLiteral78Block : Bool
    sameActionRecognitionRequired : Bool
    seventyEightDimensionAloneIdentifiesE6 : Bool
    fiftyTwoPlusTwentySixAloneConstructsSubmodules : Bool
    actualE6RecognitionInhabitedHere : Bool

canonicalSeventyEightExceptionalBoundary : SeventyEightExceptionalBoundary
canonicalSeventyEightExceptionalBoundary =
  seventyEightExceptionalBoundary
    true true true true
    false false false


------------------------------------------------------------------------
-- 4. E6 ROOT / F3^5 QUADRATIC MAX-CUT.
--
-- This section records the exact finite anatomy discovered by the comparison
-- lane without identifying the 72 E6 roots with a five-trit norm class.
--
-- The existing 78-object above is the E6 adjoint-dimension candidate.
-- The 72-object below is the E6 ROOT count.  They are different typed roles.
--
-- The finite quadratic-space recognition still requires an explicit carrier
-- bijection and a same-action intertwiner.  Cardinality does not pay it.
------------------------------------------------------------------------

eSixRootCount : Nat
eSixRootCount = 72

fiveTritCarrierCount : Nat
fiveTritCarrierCount = 243

fiveTritZeroCount : Nat
fiveTritZeroCount = 1

fiveTritNonzeroIsotropicCount : Nat
fiveTritNonzeroIsotropicCount = 80

fiveTritNormOneCount : Nat
fiveTritNormOneCount = 90

fiveTritNormTwoCount : Nat
fiveTritNormTwoCount = 72

fiveTritQuadraticPartition :
  fiveTritCarrierCount
  ≡ fiveTritZeroCount
    + fiveTritNonzeroIsotropicCount
    + fiveTritNormOneCount
    + fiveTritNormTwoCount
fiveTritQuadraticPartition = refl

puncturedFourTritCount : Nat
puncturedFourTritCount = 80

nonzeroIsotropicCountMatchesPuncturedFourTritCount :
  fiveTritNonzeroIsotropicCount ≡ puncturedFourTritCount
nonzeroIsotropicCountMatchesPuncturedFourTritCount = refl

eSixRootCountMatchesNormTwoCount :
  eSixRootCount ≡ fiveTritNormTwoCount
eSixRootCountMatchesNormTwoCount = refl

projectiveFiveTritPointCount : Nat
projectiveFiveTritPointCount = 121

projectiveIsotropicCount : Nat
projectiveIsotropicCount = 40

projectiveNormOneCount : Nat
projectiveNormOneCount = 45

projectiveNormTwoCount : Nat
projectiveNormTwoCount = 36

projectiveQuadraticPartition :
  projectiveFiveTritPointCount
  ≡ projectiveIsotropicCount
    + projectiveNormOneCount
    + projectiveNormTwoCount
projectiveQuadraticPartition = refl

record E6RootF3FiveQuadraticRecognition : Set₁ where
  field
    Actor E6RootCarrier F3FiveNormTwoCarrier : Set
    e6RootAction : Actor → E6RootCarrier → E6RootCarrier
    f3FiveAction : Actor → F3FiveNormTwoCarrier → F3FiveNormTwoCarrier

    toF3Five : E6RootCarrier → F3FiveNormTwoCarrier
    fromF3Five : F3FiveNormTwoCarrier → E6RootCarrier
    fromAfterTo :
      (root : E6RootCarrier) →
      fromF3Five (toF3Five root) ≡ root
    toAfterFrom :
      (state : F3FiveNormTwoCarrier) →
      toF3Five (fromF3Five state) ≡ state
    sameActionIntertwiner :
      (actor : Actor) →
      (root : E6RootCarrier) →
      toF3Five (e6RootAction actor root)
      ≡ f3FiveAction actor (toF3Five root)

data F3FiveCardinalityCreatesE6RootRecognition : Set where

f3FiveCardinalityDoesNotCreateE6RootRecognition :
  F3FiveCardinalityCreatesE6RootRecognition → ⊥
f3FiveCardinalityDoesNotCreateE6RootRecognition ()

record E6F3FiveQuadraticBoundary : Set where
  constructor e6F3FiveQuadraticBoundary
  field
    fiveTrit243PartitionRecorded : Bool
    nonzeroIsotropic80Recorded : Bool
    normOne90Recorded : Bool
    normTwo72Recorded : Bool
    e6RootCount72Recorded : Bool
    projective121PartitionRecorded : Bool
    rootAndAdjointRolesSeparated : Bool
    explicitTwoSidedRecognitionRequired : Bool
    sameActionIntertwinerRequired : Bool
    cardinalityCreatesE6RootRecognition : Bool
    quotientIsometryPaidHere : Bool
    weylIntertwinerPaidHere : Bool

canonicalE6F3FiveQuadraticBoundary : E6F3FiveQuadraticBoundary
canonicalE6F3FiveQuadraticBoundary =
  e6F3FiveQuadraticBoundary
    true true true true true true true true true
    false false false
