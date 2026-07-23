module DASHI.Cognition.VisualSymmetryFixedPoint where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.Base369ZeroFibre as Fibre
import DASHI.Cognition.CognitiveResearchSources as Sources

------------------------------------------------------------------------
-- Exact finite symmetry mode.
--
-- Neural-field motivation:
-- Ermentrout & Cowan (1979), DOI 10.1007/BF00336965.
-- Bressloff, Cowan, Golubitsky, Thomas & Wiener (2001),
-- DOI 10.1098/rstb.2000.0769.
--
-- The four-pixel carrier is not a cortical fit.  It proves the structural
-- statement that a pointwise-public-zero pattern can be a nontrivial fixed
-- point of spatial transport followed by hidden-fibre involution.
------------------------------------------------------------------------

visualSymmetrySource : Sources.ResearchSource
visualSymmetrySource = Sources.bressloffGeometricHallucinations

record OrientationPattern4 : Set where
  constructor pattern4
  field
    pixel0 : Fibre.Orientation
    pixel1 : Fibre.Orientation
    pixel2 : Fibre.Orientation
    pixel3 : Fibre.Orientation

open OrientationPattern4 public

flipOrientation : Fibre.Orientation → Fibre.Orientation
flipOrientation Fibre.forward = Fibre.reverse
flipOrientation Fibre.reverse = Fibre.forward

shiftPattern : OrientationPattern4 → OrientationPattern4
shiftPattern pattern = pattern4
  (pixel1 pattern)
  (pixel2 pattern)
  (pixel3 pattern)
  (pixel0 pattern)

flipPattern : OrientationPattern4 → OrientationPattern4
flipPattern pattern = pattern4
  (flipOrientation (pixel0 pattern))
  (flipOrientation (pixel1 pattern))
  (flipOrientation (pixel2 pattern))
  (flipOrientation (pixel3 pattern))

symmetryTransport : OrientationPattern4 → OrientationPattern4
symmetryTransport pattern = flipPattern (shiftPattern pattern)

checkerFixedPoint : OrientationPattern4
checkerFixedPoint = pattern4
  Fibre.forward
  Fibre.reverse
  Fibre.forward
  Fibre.reverse

checkerIsSymmetryFixedPoint :
  symmetryTransport checkerFixedPoint ≡ checkerFixedPoint
checkerIsSymmetryFixedPoint = refl

uniformForward : OrientationPattern4
uniformForward = pattern4
  Fibre.forward
  Fibre.forward
  Fibre.forward
  Fibre.forward

uniformForwardMovesToReverse :
  symmetryTransport uniformForward ≡
  pattern4 Fibre.reverse Fibre.reverse Fibre.reverse Fibre.reverse
uniformForwardMovesToReverse = refl

------------------------------------------------------------------------
-- All hidden orientations project to the same public ternary zero.
------------------------------------------------------------------------

observeOrientation : Fibre.Orientation → BT.Trit
observeOrientation orientation = BT.zero

record PublicPattern4 : Set where
  constructor publicPattern4
  field
    public0 : BT.Trit
    public1 : BT.Trit
    public2 : BT.Trit
    public3 : BT.Trit

observePattern : OrientationPattern4 → PublicPattern4
observePattern pattern = publicPattern4
  (observeOrientation (pixel0 pattern))
  (observeOrientation (pixel1 pattern))
  (observeOrientation (pixel2 pattern))
  (observeOrientation (pixel3 pattern))

checkerIsPointwisePublicZero :
  observePattern checkerFixedPoint ≡
  publicPattern4 BT.zero BT.zero BT.zero BT.zero
checkerIsPointwisePublicZero = refl

------------------------------------------------------------------------
-- Fixed-point defect is the count of hidden pixels changed by the generator.
------------------------------------------------------------------------

orientationEqual : Fibre.Orientation → Fibre.Orientation → Bool
orientationEqual Fibre.forward Fibre.forward = true
orientationEqual Fibre.reverse Fibre.reverse = true
orientationEqual _ _ = false

mismatch : Fibre.Orientation → Fibre.Orientation → Nat
mismatch left right with orientationEqual left right
... | true = 0
... | false = 1

fixedPointDefect : OrientationPattern4 → Nat
fixedPointDefect pattern =
  let transported = symmetryTransport pattern in
  mismatch (pixel0 transported) (pixel0 pattern) +
  mismatch (pixel1 transported) (pixel1 pattern) +
  mismatch (pixel2 transported) (pixel2 pattern) +
  mismatch (pixel3 transported) (pixel3 pattern)

checkerFixedPointDefectIsZero :
  fixedPointDefect checkerFixedPoint ≡ 0
checkerFixedPointDefectIsZero = refl

uniformPatternDefectIsFour :
  fixedPointDefect uniformForward ≡ 4
uniformPatternDefectIsFour = refl
