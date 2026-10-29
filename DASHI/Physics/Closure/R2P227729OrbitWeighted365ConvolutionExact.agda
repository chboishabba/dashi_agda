module DASHI.Physics.Closure.R2P227729OrbitWeighted365ConvolutionExact where

------------------------------------------------------------------------
-- EXACT ORIENTED-PAIR EVENT COMPILER (365 PAIRS -> 729 EVENTS).
--
-- New source-written bridge; Agda kernel verification pending.
-- Inherited owners:
--   BalancedTernaryAntipodalOrbitExact (13/27 and 5/9 C2 classes)
--   R2P227729FourierObserverIncidenceExact (729 actual ordered pairs)
--   R2P227729PairOrbit365CanonicalSymmetryExact (orientation and count)
--   R2P227729HermitianThirteenPairFourierCodecExact (Hermitian inputs)
--   R2P227729AntipodalThirteenFiveOrbitFourierCutExact (output negation)
--   C3CubeCyclotomicFourierExact (exact Q(omega), conjugation).
--
-- A canonical pair requires ONE cyclotomic multiplication. Its mate
-- uses conjugation of that product, NOT a second multiplication.
-- The (0,0) ordered pair occurs ONCE and has no distinct mate.
-- This builds an operational 365-product event stream; it does NOT
-- yet prove a global list-permutation/sum equality in Agda.
-- Neither an FFT, a Leray NS nonlinear operator, Clay regularity,
-- GF(729), Monster 3B nor R2P2 measurements follow.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_,_)
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Conv
import DASHI.Physics.Closure.R2P227729PairOrbit365CanonicalSymmetryExact as Pair
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Herm
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

filterL : ∀ {A : Set} → (A → Bool) → List A → List A
filterL test [] = []
filterL test (x ∷ xs) with test x
... | true = x ∷ filterL test xs
... | false = filterL test xs

canonicalOrderedPairs : List I.ModePair729
canonicalOrderedPairs = filterL Pair.positivePair I.pair729

actual365CanonicalPairEntries :
  I.lengthL canonicalOrderedPairs ≡ 365
actual365CanonicalPairEntries = refl

record WeightedEvent : Set where
  constructor weightedEvent
  field
    output : Conv.WideCube125
    weight : C3.Cyclotomic3
open WeightedEvent public

sourceEvent :
  (a b : Herm.Hermitian27) →
  I.ModePair729 → WeightedEvent
sourceEvent a b (p , q) =
  weightedEvent (Conv.exactPairOutput p q)
    (C3._*C_ (Herm.coefficient a p) (Herm.coefficient b q))

invertedEvent : WeightedEvent → WeightedEvent
invertedEvent (weightedEvent k z) =
  weightedEvent (Ant.negateWideCube k) (C3.conjC z)

-- This is the crucial algebraic identity for TWO DIFFERENT Hermitian
-- fields. It uses the original *multiplicative* conjugation law.
reflectedEventIsConjugate :
  (a b : Herm.Hermitian27) (pair : I.ModePair729) →
  sourceEvent a b (Ant.simultaneouslyNegateOrderedPair pair)
    ≡ invertedEvent (sourceEvent a b pair)
reflectedEventIsConjugate a b (p , q)
  rewrite Ant.orderedPairOutputCovariantUnderSimultaneousNegation (p , q)
        | Herm.conjugateAtNegative a p
        | Herm.conjugateAtNegative b q
        | C3.conjugationMultiplicative
            (Herm.coefficient a p) (Herm.coefficient b q) = refl

-- Pair (0,0) is fixed under simultaneous inversion. All other
-- canonical pairs have a distinct mate. The source event is evaluated
-- once and then reused. No per-input independent sign quotient exists.
emitCanonicalPair :
  (a b : Herm.Hermitian27) →
  I.ModePair729 → List WeightedEvent
emitCanonicalPair a b pair with Pair.isCentralPair pair
... | true = sourceEvent a b pair ∷ []
... | false =
  let e = sourceEvent a b pair in e ∷ invertedEvent e ∷ []

centralPairIsEmittedOnce :
  (a b : Herm.Hermitian27) →
  emitCanonicalPair a b (Pair.zeroCube , Pair.zeroCube)
    ≡ sourceEvent a b (Pair.zeroCube , Pair.zeroCube) ∷ []
centralPairIsEmittedOnce a b = refl

orbitWeightedEvents :
  (a b : Herm.Hermitian27) → List WeightedEvent
orbitWeightedEvents a b =
  I.concatMapL (emitCanonicalPair a b) canonicalOrderedPairs

actual729WeightedEvents :
  (a b : Herm.Hermitian27) →
  I.lengthL (orbitWeightedEvents a b) ≡ 729
actual729WeightedEvents a b = refl

-- Output aggregation retains the ORIGINAL integer-frequency targets.
-- The 365 multiplications feed all 125 target coefficients; the mate
-- is obtained by conjugation. The complete 729-list reindexing theorem
-- remains a distinct unproved Agda obligation, not a hidden postulate.
sumEventsAt :
  Conv.WideCube125 → List WeightedEvent → C3.Cyclotomic3
sumEventsAt target [] = C3.zeroC
sumEventsAt target (e ∷ es) with Conv.eqWideCube (output e) target
... | true = C3._+C_ (weight e) (sumEventsAt target es)
... | false = sumEventsAt target es

orbitWeightedConvolutionAt :
  (a b : Herm.Hermitian27) → Conv.WideCube125 → C3.Cyclotomic3
orbitWeightedConvolutionAt a b target =
  sumEventsAt target (orbitWeightedEvents a b)

-- The exact source's full signed pair event stream is retained as an
-- explicit comparison target. No theorem equating the two lists is
-- asserted without a permutation/sum proof.
unreducedEvents :
  (a b : Herm.Hermitian27) → List WeightedEvent
unreducedEvents a b = I.mapL (sourceEvent a b) I.pair729

unreducedEventsCount729 :
  (a b : Herm.Hermitian27) →
  I.lengthL (unreducedEvents a b) ≡ 729
unreducedEventsCount729 a b = refl

unreducedConvolutionAt :
  (a b : Herm.Hermitian27) → Conv.WideCube125 → C3.Cyclotomic3
unreducedConvolutionAt a b target =
  sumEventsAt target (unreducedEvents a b)


------------------------------------------------------------------------
-- TWO-DIMENSIONAL SOURCE FIVE-IN-NINE EXTENSION: 81 -> 41 -> 81
-- Reuses the ORIGINAL plane Hermitian codec and its integer pair output.
-- No D4 irreducible-representation or Monster inference is permitted.
------------------------------------------------------------------------

import DASHI.Physics.Closure.R2P281PlaneHermitianFiveOrbitConvolutionExact as Plane
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M

isZeroPlane : Ant.Plane9 → Bool
isZeroPlane (M.modeZero , M.modeZero) = true
isZeroPlane _ = false

positivePlaneOrderedPair : Plane.PlanePair81 → Bool
positivePlaneOrderedPair (p , q) with isZeroPlane p
... | true = Herm.planePositiveSide q
... | false = Herm.planePositiveSide p

canonicalPlaneOrderedPairs : List Plane.PlanePair81
canonicalPlaneOrderedPairs =
  filterL positivePlaneOrderedPair Plane.planePairs81

actual41PlanePairOrbits :
  I.lengthL canonicalPlaneOrderedPairs ≡ 41
actual41PlanePairOrbits = refl

negatePlaneOrderedPair : Plane.PlanePair81 → Plane.PlanePair81
negatePlaneOrderedPair (p , q) =
  Ant.negatePlane9 p , Ant.negatePlane9 q

negateWidePlane : Plane.WidePlane25 → Plane.WidePlane25
negateWidePlane (x , y) =
  Ant.negateWideAxis x , Ant.negateWideAxis y

planePairOutputCovariant :
  (pair : Plane.PlanePair81) →
  Plane.planeTruePairSum (negatePlaneOrderedPair pair)
    ≡ negateWidePlane (Plane.planeTruePairSum pair)
planePairOutputCovariant ((a , b) , (c , d))
  rewrite Ant.trueSignedAxisSumNegatesCovariantly a c
        | Ant.trueSignedAxisSumNegatesCovariantly b d = refl

record WeightedPlaneEvent : Set where
  constructor weightedPlaneEvent
  field
    planeOutput : Plane.WidePlane25
    planeWeight : C3.Cyclotomic3
open WeightedPlaneEvent public

planeSourceEvent :
  (a b : Herm.Hermitian9) →
  Plane.PlanePair81 → WeightedPlaneEvent
planeSourceEvent a b (p , q) =
  weightedPlaneEvent (Plane.planeTruePairSum (p , q))
    (C3._*C_ (Herm.coefficient9 a p) (Herm.coefficient9 b q))

invertedPlaneEvent : WeightedPlaneEvent → WeightedPlaneEvent
invertedPlaneEvent (weightedPlaneEvent k z) =
  weightedPlaneEvent (negateWidePlane k) (C3.conjC z)

reflectedPlaneEventIsConjugate :
  (a b : Herm.Hermitian9) (pair : Plane.PlanePair81) →
  planeSourceEvent a b (negatePlaneOrderedPair pair)
    ≡ invertedPlaneEvent (planeSourceEvent a b pair)
reflectedPlaneEventIsConjugate a b (p , q)
  rewrite planePairOutputCovariant (p , q)
        | Herm.conjugateAtNegative9 a p
        | Herm.conjugateAtNegative9 b q
        | C3.conjugationMultiplicative
            (Herm.coefficient9 a p) (Herm.coefficient9 b q) = refl

isCentralPlanePair : Plane.PlanePair81 → Bool
isCentralPlanePair (p , q) with isZeroPlane p
... | true = isZeroPlane q
... | false = false

emitCanonicalPlanePair :
  (a b : Herm.Hermitian9) →
  Plane.PlanePair81 → List WeightedPlaneEvent
emitCanonicalPlanePair a b pair with isCentralPlanePair pair
... | true = planeSourceEvent a b pair ∷ []
... | false =
  let e = planeSourceEvent a b pair in
  e ∷ invertedPlaneEvent e ∷ []

orbitWeightedPlaneEvents :
  (a b : Herm.Hermitian9) → List WeightedPlaneEvent
orbitWeightedPlaneEvents a b =
  I.concatMapL (emitCanonicalPlanePair a b) canonicalPlaneOrderedPairs

actual81WeightedPlaneEvents :
  (a b : Herm.Hermitian9) →
  I.lengthL (orbitWeightedPlaneEvents a b) ≡ 81
actual81WeightedPlaneEvents a b = refl

sumPlaneEventsAt :
  Plane.WidePlane25 → List WeightedPlaneEvent → C3.Cyclotomic3
sumPlaneEventsAt target [] = C3.zeroC
sumPlaneEventsAt target (e ∷ es)
  with Plane.planeOutputEqual (planeOutput e) target
... | true = C3._+C_ (planeWeight e) (sumPlaneEventsAt target es)
... | false = sumPlaneEventsAt target es

orbitWeightedPlaneConvolutionAt :
  (a b : Herm.Hermitian9) → Plane.WidePlane25 → C3.Cyclotomic3
orbitWeightedPlaneConvolutionAt a b target =
  sumPlaneEventsAt target (orbitWeightedPlaneEvents a b)
