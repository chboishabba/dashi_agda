module DASHI.Physics.Closure.R2P227729PairSixTritFibreBidiExact where

------------------------------------------------------------------------
-- EXACT 27×27 ORDERED PAIR <-> EXISTING SIX-TRIT FUNCTION CARRIER.
--
-- Original proof owners:
--   DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact (recursive T^n)
--   DASHI.Foundations.Base369TernaryDeltaBasisCrossPollinationExact
--   DASHI.ComputerScience.BinaryThreeBitTrit27FibreLiftExact
--   DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact
--
-- New: explicit SIX-coordinate roundtrips for a PAIR of three-mode
-- integer frequency LABELS. This uses the actual shared T^6 carrier
-- rather than interpreting 27*27=729 as a model identity.
--
-- This is NOT a same-object map to GF(729), Monster 3B, Heisenberg
-- action, two optical clock measurements or actual NS velocity data.
-- A carrier equivalence need not intertwine any operator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact as Basis
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Foundations.Base369TernaryDeltaBasisCrossPollinationExact as Role

SixTritIndex : Set
SixTritIndex = Basis.TritCube 6

OrderedPair729 : Set
OrderedPair729 = I.ModeCube27 × I.ModeCube27

orderedPairToSixTrits : OrderedPair729 → SixTritIndex
orderedPairToSixTrits
  (I.modeCube a b c , I.modeCube d e f) =
  Basis.cubeS (M.threeModeToTrit a)
    (Basis.cubeS (M.threeModeToTrit b)
      (Basis.cubeS (M.threeModeToTrit c)
        (Basis.cubeS (M.threeModeToTrit d)
          (Basis.cubeS (M.threeModeToTrit e)
            (Basis.cubeS (M.threeModeToTrit f) Basis.cube0)))))

sixTritsToOrderedPair : SixTritIndex → OrderedPair729
sixTritsToOrderedPair
  (Basis.cubeS a
    (Basis.cubeS b
      (Basis.cubeS c
        (Basis.cubeS d
          (Basis.cubeS e
            (Basis.cubeS f Basis.cube0)))))) =
  I.modeCube (M.tritToThreeMode a)
             (M.tritToThreeMode b)
             (M.tritToThreeMode c)
  , I.modeCube (M.tritToThreeMode d)
               (M.tritToThreeMode e)
               (M.tritToThreeMode f)

sixTritsAfterOrderedPairRoundTrip :
  (p : OrderedPair729) →
  sixTritsToOrderedPair (orderedPairToSixTrits p) ≡ p
sixTritsAfterOrderedPairRoundTrip
  (I.modeCube a b c , I.modeCube d e f)
  rewrite M.threeModeAfterTritRoundTrip a
        | M.threeModeAfterTritRoundTrip b
        | M.threeModeAfterTritRoundTrip c
        | M.threeModeAfterTritRoundTrip d
        | M.threeModeAfterTritRoundTrip e
        | M.threeModeAfterTritRoundTrip f = refl

orderedPairAfterSixTritRoundTrip :
  (s : SixTritIndex) →
  orderedPairToSixTrits (sixTritsToOrderedPair s) ≡ s
orderedPairAfterSixTritRoundTrip
  (Basis.cubeS a
    (Basis.cubeS b
      (Basis.cubeS c
        (Basis.cubeS d
          (Basis.cubeS e
            (Basis.cubeS f Basis.cube0))))))
  rewrite M.tritAfterThreeModeRoundTrip a
        | M.tritAfterThreeModeRoundTrip b
        | M.tritAfterThreeModeRoundTrip c
        | M.tritAfterThreeModeRoundTrip d
        | M.tritAfterThreeModeRoundTrip e
        | M.tritAfterThreeModeRoundTrip f = refl

-- A function on the PAIR of integer input mode labels has the same
-- finite *domain* as a function on T^6. The source delta basis already
-- owns exact finite-function decomposition. Transport is by the BIDI,
-- not by a string-level or cardinality-level identification.
pairAmplitudeOnSixTrits :
  ∀ {Outcome : Set} → (OrderedPair729 → Outcome) → SixTritIndex → Outcome
pairAmplitudeOnSixTrits f s = f (sixTritsToOrderedPair s)

sixTritAmplitudeOnPairs :
  ∀ {Outcome : Set} → (SixTritIndex → Outcome) → OrderedPair729 → Outcome
sixTritAmplitudeOnPairs f pair = f (orderedPairToSixTrits pair)

pairAmplitudeAfterTransport :
  ∀ {Outcome : Set} (f : OrderedPair729 → Outcome) (pair : OrderedPair729) →
  sixTritAmplitudeOnPairs (pairAmplitudeOnSixTrits f) pair ≡ f pair
pairAmplitudeAfterTransport f pair
  rewrite sixTritsAfterOrderedPairRoundTrip pair = refl

sixTritAmplitudeAfterTransport :
  ∀ {Outcome : Set} (f : SixTritIndex → Outcome) (s : SixTritIndex) →
  pairAmplitudeOnSixTrits (sixTritAmplitudeOnPairs f) s ≡ f s
sixTritAmplitudeAfterTransport f s
  rewrite orderedPairAfterSixTritRoundTrip s = refl

-- Reuse original generic delta decomposition at depth 6 without
-- claiming any physical bilinear coefficient or field multiplication.
sourceSixTritDeltaReconstruction :
  (f : SixTritIndex → C3.Cyclotomic3)
  (s : SixTritIndex) →
  Basis.interpret (Basis.decompose f) s ≡ f s
sourceSixTritDeltaReconstruction = Basis.decomposeExact
