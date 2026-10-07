module DASHI.Moonshine.OggSSPHeisenbergSymplecticFieldNoGoExact where

------------------------------------------------------------------------
-- FULL HEISENBERG/SYMPLECTIC NO-GO FOR CANONICAL FIELD MULTIPLICATION
--
-- The paid Monster 3B finite-Heisenberg spine owns X6 + X6* with its exact
-- alternating symplectic pairing.  Swapping coordinates 0 and 1 simultaneously
-- in both halves preserves that pairing (and the additive structure), while the
-- generated finite-field receipt proves that the same coordinate swap changes
-- the selected GF(3^6) multiplication.  Therefore the currently paid standard
-- Heisenberg/symplectic structure still does not single out that multiplication.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Generated.OggSSPMaxCutRuntimeGenerated as Runtime

swap01X6 : G.X6 → G.X6
swap01X6 (G.x6 a0 a1 a2 a3 a4 a5) =
  G.x6 a1 a0 a2 a3 a4 a5

swap01X6Involutive : (x : G.X6) → swap01X6 (swap01X6 x) ≡ x
swap01X6Involutive (G.x6 a0 a1 a2 a3 a4 a5) = refl

swap01X6PreservesAdd :
  (x y : G.X6) →
  swap01X6 (H.addX6 x y) ≡ H.addX6 (swap01X6 x) (swap01X6 y)
swap01X6PreservesAdd
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5) = refl

swap01X6PreservesNeg :
  (x : G.X6) → swap01X6 (H.negX6 x) ≡ H.negX6 (swap01X6 x)
swap01X6PreservesNeg (G.x6 a0 a1 a2 a3 a4 a5) = refl

swap01X6PreservesDot :
  (x y : G.X6) → H.dot6 (swap01X6 x) (swap01X6 y) ≡ H.dot6 x y
swap01X6PreservesDot
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5) =
  Dot.moveMiddle
    (H._*3_ a1 b1)
    (H._*3_ a0 b0)
    (Dot.sum4
      (H._*3_ a2 b2)
      (H._*3_ a3 b3)
      (H._*3_ a4 b4)
      (H._*3_ a5 b5))

swap01Symplectic12 : H.Symplectic12 → H.Symplectic12
swap01Symplectic12 u =
  H.symplectic12
    (swap01X6 (H.translationPart u))
    (swap01X6 (H.modulationPart u))

swap01Symplectic12Involutive :
  (u : H.Symplectic12) →
  swap01Symplectic12 (swap01Symplectic12 u) ≡ u
swap01Symplectic12Involutive (H.symplectic12 x y)
  rewrite swap01X6Involutive x | swap01X6Involutive y = refl

swap01PreservesSymplecticPair :
  (u v : H.Symplectic12) →
  H.symplecticPair (swap01Symplectic12 u) (swap01Symplectic12 v)
  ≡ H.symplecticPair u v
swap01PreservesSymplecticPair
  (H.symplectic12 x xdual)
  (H.symplectic12 y ydual)
  rewrite swap01X6PreservesDot x ydual
        | swap01X6PreservesDot y xdual
  = refl

-- The same X6 coordinate symmetry changes the chosen degree-six field product
-- in the exhaustive runtime presentation.
runtimeSymplecticCoordinateSwapChangesChosenK6Multiplication :
  Runtime.k6CoordinateSwapChangesChosenMultiplication ≡ true
runtimeSymplecticCoordinateSwapChangesChosenK6Multiplication = refl

record HeisenbergSymplecticFieldNoGoBoundary : Set where
  constructor heisenberg-symplectic-field-no-go-boundary
  field
    x6CoordinateSwapInvolutive : Bool
    additiveStructurePreserved : Bool
    negationPreserved : Bool
    fullStandardSymplecticPairPreserved : Bool
    selectedK6FieldMultiplicationChanged : Bool
    currentHeisenbergSymplecticDataSelectsChosenFieldProduct : Bool
    richerPriorActionStillCouldSelectFieldProduct : Bool

canonicalHeisenbergSymplecticFieldNoGoBoundary :
  HeisenbergSymplecticFieldNoGoBoundary
canonicalHeisenbergSymplecticFieldNoGoBoundary =
  heisenberg-symplectic-field-no-go-boundary
    true true true true
    Runtime.k6CoordinateSwapChangesChosenMultiplication
    false true
