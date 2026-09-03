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
open import Agda.Builtin.Nat using (Nat; _+_)

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
