module DASHI.Foundations.PolynomialC3S3ReflectionParityFourierExact where

------------------------------------------------------------------------
-- EXACT 11 = 7 (+) + 4 (-) REFLECTION CHARACTER CHART OVER F3
-- Source: the original finite C3 phase group, the original seven
-- S3-conjugacy shapes, and #1414's actual eleven C3-orbit classes.
--
-- An involution on eleven sites has 3 fixed sites and 4 swapped
-- pairs. Characteristic THREE DOES NOT DIVIDE TWO. Thus the
-- reflection (C2) has actual +/- eigen-coordinates:
-- e = (a+b)/2 = -(a+b), o = (a-b)/2 = -(a-b) in F3.
-- Reconstruction a=e+o, b=e-o is exactly invertible.
-- No 1/3 or C3 Reynolds averaging, no 11=7+4 "Monster" claim.
-- Classical mathematics: finite representations / idempotents of C2.
-- Repository contributions: this typed chosen-pair coordinate atlas.
-- SOURCE-WRITTEN; Agda kernel type-check NOT performed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as C3
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q

-- Reuse the existing Phase3 additive group; this chart ONLY names
-- the same three residues as the native TriTruth values.
toPhase : Base.TriTruth → Phase.Phase3
toPhase Base.tri-low = Phase.phase0
toPhase Base.tri-mid = Phase.phase1
toPhase Base.tri-high = Phase.phase2

fromPhase : Phase.Phase3 → Base.TriTruth
fromPhase Phase.phase0 = Base.tri-low
fromPhase Phase.phase1 = Base.tri-mid
fromPhase Phase.phase2 = Base.tri-high

phaseToTruthToPhase : (p : Phase.Phase3) → toPhase (fromPhase p) ≡ p
phaseToTruthToPhase Phase.phase0 = refl
phaseToTruthToPhase Phase.phase1 = refl
phaseToTruthToPhase Phase.phase2 = refl

truthToPhaseToTruth : (t : Base.TriTruth) → fromPhase (toPhase t) ≡ t
truthToPhaseToTruth Base.tri-low = refl
truthToPhaseToTruth Base.tri-mid = refl
truthToPhaseToTruth Base.tri-high = refl

-- 2^{-1}=2=-1 mod 3. No appeal to rational/complex scalars.
evenAverage : Base.TriTruth → Base.TriTruth → Base.TriTruth
evenAverage a b =
  fromPhase (C3.c3Inverse (C3._+₃_ (toPhase a) (toPhase b)))

oddHalfDifference : Base.TriTruth → Base.TriTruth → Phase.Phase3
oddHalfDifference a b =
  C3.c3Inverse (C3._+₃_ (toPhase a) (C3.c3Inverse (toPhase b)))

reconstructPositive : Base.TriTruth → Phase.Phase3 → Base.TriTruth
reconstructPositive e o = fromPhase (C3._+₃_ (toPhase e) o)

reconstructNegative : Base.TriTruth → Phase.Phase3 → Base.TriTruth
reconstructNegative e o =
  fromPhase (C3._+₃_ (toPhase e) (C3.c3Inverse o))

firstReconstructed :
  (a b : Base.TriTruth) →
  reconstructPositive (evenAverage a b) (oddHalfDifference a b) ≡ a
firstReconstructed Base.tri-low Base.tri-low = refl
firstReconstructed Base.tri-low Base.tri-mid = refl
firstReconstructed Base.tri-low Base.tri-high = refl
firstReconstructed Base.tri-mid Base.tri-low = refl
firstReconstructed Base.tri-mid Base.tri-mid = refl
firstReconstructed Base.tri-mid Base.tri-high = refl
firstReconstructed Base.tri-high Base.tri-low = refl
firstReconstructed Base.tri-high Base.tri-mid = refl
firstReconstructed Base.tri-high Base.tri-high = refl

secondReconstructed :
  (a b : Base.TriTruth) →
  reconstructNegative (evenAverage a b) (oddHalfDifference a b) ≡ b
secondReconstructed Base.tri-low Base.tri-low = refl
secondReconstructed Base.tri-low Base.tri-mid = refl
secondReconstructed Base.tri-low Base.tri-high = refl
secondReconstructed Base.tri-mid Base.tri-low = refl
secondReconstructed Base.tri-mid Base.tri-mid = refl
secondReconstructed Base.tri-mid Base.tri-high = refl
secondReconstructed Base.tri-high Base.tri-low = refl
secondReconstructed Base.tri-high Base.tri-mid = refl
secondReconstructed Base.tri-high Base.tri-high = refl

evenReconstructed :
  (e : Base.TriTruth) (o : Phase.Phase3) →
  evenAverage (reconstructPositive e o) (reconstructNegative e o) ≡ e
evenReconstructed Base.tri-low Phase.phase0 = refl
evenReconstructed Base.tri-low Phase.phase1 = refl
evenReconstructed Base.tri-low Phase.phase2 = refl
evenReconstructed Base.tri-mid Phase.phase0 = refl
evenReconstructed Base.tri-mid Phase.phase1 = refl
evenReconstructed Base.tri-mid Phase.phase2 = refl
evenReconstructed Base.tri-high Phase.phase0 = refl
evenReconstructed Base.tri-high Phase.phase1 = refl
evenReconstructed Base.tri-high Phase.phase2 = refl

oddReconstructed :
  (e : Base.TriTruth) (o : Phase.Phase3) →
  oddHalfDifference (reconstructPositive e o) (reconstructNegative e o) ≡ o
oddReconstructed Base.tri-low Phase.phase0 = refl
oddReconstructed Base.tri-low Phase.phase1 = refl
oddReconstructed Base.tri-low Phase.phase2 = refl
oddReconstructed Base.tri-mid Phase.phase0 = refl
oddReconstructed Base.tri-mid Phase.phase1 = refl
oddReconstructed Base.tri-mid Phase.phase2 = refl
oddReconstructed Base.tri-high Phase.phase0 = refl
oddReconstructed Base.tri-high Phase.phase1 = refl
oddReconstructed Base.tri-high Phase.phase2 = refl

evenSymmetric :
  (a b : Base.TriTruth) → evenAverage b a ≡ evenAverage a b
evenSymmetric Base.tri-low Base.tri-low = refl
evenSymmetric Base.tri-low Base.tri-mid = refl
evenSymmetric Base.tri-low Base.tri-high = refl
evenSymmetric Base.tri-mid Base.tri-low = refl
evenSymmetric Base.tri-mid Base.tri-mid = refl
evenSymmetric Base.tri-mid Base.tri-high = refl
evenSymmetric Base.tri-high Base.tri-low = refl
evenSymmetric Base.tri-high Base.tri-mid = refl
evenSymmetric Base.tri-high Base.tri-high = refl

oddAntisymmetric :
  (a b : Base.TriTruth) →
  oddHalfDifference b a ≡ C3.c3Inverse (oddHalfDifference a b)
oddAntisymmetric Base.tri-low Base.tri-low = refl
oddAntisymmetric Base.tri-low Base.tri-mid = refl
oddAntisymmetric Base.tri-low Base.tri-high = refl
oddAntisymmetric Base.tri-mid Base.tri-low = refl
oddAntisymmetric Base.tri-mid Base.tri-mid = refl
oddAntisymmetric Base.tri-mid Base.tri-high = refl
oddAntisymmetric Base.tri-high Base.tri-low = refl
oddAntisymmetric Base.tri-high Base.tri-mid = refl
oddAntisymmetric Base.tri-high Base.tri-high = refl

record Odd4 : Set where
  constructor odd4
  field
    cycleOdd : Phase.Phase3
    rank2OneFixedOdd : Phase.Phase3
    rank2TwoFixedOdd : Phase.Phase3
    rank2TwoCycleOdd : Phase.Phase3
open Odd4 public

record EvenOddCoordinates : Set where
  constructor evenOdd
  field
    even7 : Q.Field7
    odd4Coords : Odd4
open EvenOddCoordinates public

-- Seven even coordinates: 3 singletons, 4 pairwise averages.
encodeEven : Q.Field11 → Q.Field7
encodeEven f Shape.identityShape = f Q.identityOrbit
encodeEven f Shape.threeCycleShape =
  evenAverage (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
encodeEven f Shape.transpositionShape = f Q.transpositionOrbit
encodeEven f Shape.constantShape = f Q.constantOrbit
encodeEven f Shape.rank2OneFixedShape =
  evenAverage (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
encodeEven f Shape.rank2TwoFixedShape =
  evenAverage (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
encodeEven f Shape.rank2TwoCycleShape =
  evenAverage (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)

encodeOdd : Q.Field11 → Odd4
encodeOdd f =
  odd4
    (oddHalfDifference (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit))
    (oddHalfDifference (f Q.rank2OneFixedA) (f Q.rank2OneFixedB))
    (oddHalfDifference (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB))
    (oddHalfDifference (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB))

encodeEvenOdd : Q.Field11 → EvenOddCoordinates
encodeEvenOdd f = evenOdd (encodeEven f) (encodeOdd f)

decodeEvenOdd : EvenOddCoordinates → Q.Field11
decodeEvenOdd c Q.identityOrbit = even7 c Shape.identityShape
decodeEvenOdd c Q.cycleForwardOrbit =
  reconstructPositive (even7 c Shape.threeCycleShape) (cycleOdd (odd4Coords c))
decodeEvenOdd c Q.cycleBackwardOrbit =
  reconstructNegative (even7 c Shape.threeCycleShape) (cycleOdd (odd4Coords c))
decodeEvenOdd c Q.transpositionOrbit = even7 c Shape.transpositionShape
decodeEvenOdd c Q.constantOrbit = even7 c Shape.constantShape
decodeEvenOdd c Q.rank2OneFixedA =
  reconstructPositive (even7 c Shape.rank2OneFixedShape) (rank2OneFixedOdd (odd4Coords c))
decodeEvenOdd c Q.rank2OneFixedB =
  reconstructNegative (even7 c Shape.rank2OneFixedShape) (rank2OneFixedOdd (odd4Coords c))
decodeEvenOdd c Q.rank2TwoFixedA =
  reconstructPositive (even7 c Shape.rank2TwoFixedShape) (rank2TwoFixedOdd (odd4Coords c))
decodeEvenOdd c Q.rank2TwoFixedB =
  reconstructNegative (even7 c Shape.rank2TwoFixedShape) (rank2TwoFixedOdd (odd4Coords c))
decodeEvenOdd c Q.rank2TwoCycleA =
  reconstructPositive (even7 c Shape.rank2TwoCycleShape) (rank2TwoCycleOdd (odd4Coords c))
decodeEvenOdd c Q.rank2TwoCycleB =
  reconstructNegative (even7 c Shape.rank2TwoCycleShape) (rank2TwoCycleOdd (odd4Coords c))

decodeAfterEncodeAt :
  (f : Q.Field11) (o : Q.Orbit11) →
  decodeEvenOdd (encodeEvenOdd f) o ≡ f o
decodeAfterEncodeAt f Q.identityOrbit = refl
decodeAfterEncodeAt f Q.cycleForwardOrbit =
  firstReconstructed (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
decodeAfterEncodeAt f Q.cycleBackwardOrbit =
  secondReconstructed (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
decodeAfterEncodeAt f Q.transpositionOrbit = refl
decodeAfterEncodeAt f Q.constantOrbit = refl
decodeAfterEncodeAt f Q.rank2OneFixedA =
  firstReconstructed (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
decodeAfterEncodeAt f Q.rank2OneFixedB =
  secondReconstructed (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
decodeAfterEncodeAt f Q.rank2TwoFixedA =
  firstReconstructed (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
decodeAfterEncodeAt f Q.rank2TwoFixedB =
  secondReconstructed (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
decodeAfterEncodeAt f Q.rank2TwoCycleA =
  firstReconstructed (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)
decodeAfterEncodeAt f Q.rank2TwoCycleB =
  secondReconstructed (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)

encodeAfterDecodeEvenAt :
  (c : EvenOddCoordinates) (s : Shape.ShapeOrbit7) →
  encodeEven (decodeEvenOdd c) s ≡ even7 c s
encodeAfterDecodeEvenAt c Shape.identityShape = refl
encodeAfterDecodeEvenAt c Shape.threeCycleShape =
  evenReconstructed (even7 c Shape.threeCycleShape) (cycleOdd (odd4Coords c))
encodeAfterDecodeEvenAt c Shape.transpositionShape = refl
encodeAfterDecodeEvenAt c Shape.constantShape = refl
encodeAfterDecodeEvenAt c Shape.rank2OneFixedShape =
  evenReconstructed (even7 c Shape.rank2OneFixedShape) (rank2OneFixedOdd (odd4Coords c))
encodeAfterDecodeEvenAt c Shape.rank2TwoFixedShape =
  evenReconstructed (even7 c Shape.rank2TwoFixedShape) (rank2TwoFixedOdd (odd4Coords c))
encodeAfterDecodeEvenAt c Shape.rank2TwoCycleShape =
  evenReconstructed (even7 c Shape.rank2TwoCycleShape) (rank2TwoCycleOdd (odd4Coords c))

encodeAfterDecodeOddCycle :
  (c : EvenOddCoordinates) →
  cycleOdd (encodeOdd (decodeEvenOdd c)) ≡ cycleOdd (odd4Coords c)
encodeAfterDecodeOddCycle c =
  oddReconstructed (even7 c Shape.threeCycleShape) (cycleOdd (odd4Coords c))

encodeAfterDecodeOddOneFixed :
  (c : EvenOddCoordinates) →
  rank2OneFixedOdd (encodeOdd (decodeEvenOdd c)) ≡ rank2OneFixedOdd (odd4Coords c)
encodeAfterDecodeOddOneFixed c =
  oddReconstructed (even7 c Shape.rank2OneFixedShape) (rank2OneFixedOdd (odd4Coords c))

encodeAfterDecodeOddTwoFixed :
  (c : EvenOddCoordinates) →
  rank2TwoFixedOdd (encodeOdd (decodeEvenOdd c)) ≡ rank2TwoFixedOdd (odd4Coords c)
encodeAfterDecodeOddTwoFixed c =
  oddReconstructed (even7 c Shape.rank2TwoFixedShape) (rank2TwoFixedOdd (odd4Coords c))

encodeAfterDecodeOddTwoCycle :
  (c : EvenOddCoordinates) →
  rank2TwoCycleOdd (encodeOdd (decodeEvenOdd c)) ≡ rank2TwoCycleOdd (odd4Coords c)
encodeAfterDecodeOddTwoCycle c =
  oddReconstructed (even7 c Shape.rank2TwoCycleShape) (rank2TwoCycleOdd (odd4Coords c))

-- The involution acts diagonally in the transformed coordinates.
reflect11Field : Q.Field11 → Q.Field11
reflect11Field f o = f (Q.reflectionOn11 o)

negateOdd4 : Odd4 → Odd4
negateOdd4 (odd4 a b c d) =
  odd4 (C3.c3Inverse a) (C3.c3Inverse b)
       (C3.c3Inverse c) (C3.c3Inverse d)

reflectEvenIsFixed :
  (f : Q.Field11) (s : Shape.ShapeOrbit7) →
  encodeEven (reflect11Field f) s ≡ encodeEven f s
reflectEvenIsFixed f Shape.identityShape = refl
reflectEvenIsFixed f Shape.threeCycleShape =
  evenSymmetric (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
reflectEvenIsFixed f Shape.transpositionShape = refl
reflectEvenIsFixed f Shape.constantShape = refl
reflectEvenIsFixed f Shape.rank2OneFixedShape =
  evenSymmetric (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
reflectEvenIsFixed f Shape.rank2TwoFixedShape =
  evenSymmetric (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
reflectEvenIsFixed f Shape.rank2TwoCycleShape =
  evenSymmetric (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)

reflectOddCycleIsNegative :
  (f : Q.Field11) →
  cycleOdd (encodeOdd (reflect11Field f)) ≡ C3.c3Inverse (cycleOdd (encodeOdd f))
reflectOddCycleIsNegative f =
  oddAntisymmetric (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)

reflectOddOneFixedIsNegative :
  (f : Q.Field11) →
  rank2OneFixedOdd (encodeOdd (reflect11Field f)) ≡ C3.c3Inverse (rank2OneFixedOdd (encodeOdd f))
reflectOddOneFixedIsNegative f =
  oddAntisymmetric (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)

reflectOddTwoFixedIsNegative :
  (f : Q.Field11) →
  rank2TwoFixedOdd (encodeOdd (reflect11Field f)) ≡ C3.c3Inverse (rank2TwoFixedOdd (encodeOdd f))
reflectOddTwoFixedIsNegative f =
  oddAntisymmetric (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)

reflectOddTwoCycleIsNegative :
  (f : Q.Field11) →
  rank2TwoCycleOdd (encodeOdd (reflect11Field f)) ≡ C3.c3Inverse (rank2TwoCycleOdd (encodeOdd f))
reflectOddTwoCycleIsNegative f =
  oddAntisymmetric (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)

-- Reflection sign = exactly the same NONTRIVIAL 1-dimensional
-- character carried by the video cubic Vandermonde. The two
-- representations remain different objects with a common C2 character.
