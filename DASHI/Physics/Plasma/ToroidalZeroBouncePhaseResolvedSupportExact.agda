module DASHI.Physics.Plasma.ToroidalZeroBouncePhaseResolvedSupportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PHASE-RESOLVED SUPPORT CARRIER
--
-- The 24 real free coordinates are twelve cos/sin harmonic planes.  The true
-- nontrivial C3 phase acts by a 120-degree linear rotation inside each plane,
-- not by permuting the selected real axes.  Therefore the raw 276 coordinate-
-- axis duads are not themselves a C3-set.
--
-- A phase-stable replacement uses three projective phase lines in each of the
-- twelve harmonic planes.  That carrier has 36 points and C(36,2)=630 pairs.
-- Local Python exhaustively verifies:
--   C3:      210 pair orbits, all of size 3;
--   C3⋊C2:    78 orbits of size 3 + 66 orbits of size 6.
------------------------------------------------------------------------

realHarmonicPlaneCount : Nat
realHarmonicPlaneCount = 12

realAxisCount : Nat
realAxisCount = 24

rawRealAxisPairCount : Nat
rawRealAxisPairCount = 276

projectivePhaseLinesPerPlane : Nat
projectivePhaseLinesPerPlane = 3

phaseResolvedLineCount : Nat
phaseResolvedLineCount = 36

phaseResolvedPairCount : Nat
phaseResolvedPairCount = 630

phaseResolvedLineCountCloses :
  realHarmonicPlaneCount * projectivePhaseLinesPerPlane ≡ phaseResolvedLineCount
phaseResolvedLineCountCloses = refl

phaseResolvedOrderedPairArithmetic :
  phaseResolvedLineCount * 35 ≡ 2 * phaseResolvedPairCount
phaseResolvedOrderedPairArithmetic = refl

c3PairOrbitCount : Nat
c3PairOrbitCount = 210

c3OrbitSize : Nat
c3OrbitSize = 3

c3PairOrbitAccounting :
  c3PairOrbitCount * c3OrbitSize ≡ phaseResolvedPairCount
c3PairOrbitAccounting = refl

completedSizeThreeOrbitCount : Nat
completedSizeThreeOrbitCount = 78

completedSizeSixOrbitCount : Nat
completedSizeSixOrbitCount = 66

completedOrbitAccounting :
  completedSizeThreeOrbitCount * 3 + completedSizeSixOrbitCount * 6 ≡
  phaseResolvedPairCount
completedOrbitAccounting = refl

record PhaseResolvedSupportAction : Set₁ where
  constructor phase-resolved-support-action
  field
    HarmonicPlane : Set
    PhaseLine : HarmonicPlane → Set
    c3Advance : ∀ {plane} → PhaseLine plane → PhaseLine plane
    inversePhase : ∀ {plane} → PhaseLine plane → PhaseLine plane
    c3OrderThreeReceipt : Set
    inversionInvolutiveReceipt : Set
    inversionConjugatesAdvanceReceipt : Set
    phasePairOrbitEnumerationReceipt : Set
    actionReference : String

open PhaseResolvedSupportAction public

record PhaseResolvedSupportBoundary : Set where
  constructor phase-resolved-support-boundary
  field
    nontrivialC3PermutesRawRealAxes : Bool
    nontrivialC3PermutesRawRealAxesIsFalse :
      nontrivialC3PermutesRawRealAxes ≡ false

    raw276AxisPairsCarryCanonicalC3Action : Bool
    raw276AxisPairsCarryCanonicalC3ActionIsFalse :
      raw276AxisPairsCarryCanonicalC3Action ≡ false

    phaseResolved36CarrierClosesUnderC3 : Bool
    phaseResolved36CarrierClosesUnderC3IsTrue :
      phaseResolved36CarrierClosesUnderC3 ≡ true

    phaseResolvedPairOrbitProfileNumericallyChecked : Bool
    phaseResolvedPairOrbitProfileNumericallyCheckedIsTrue :
      phaseResolvedPairOrbitProfileNumericallyChecked ≡ true

    phaseResolvedOrbitProfileProves243_27_6Recognition : Bool
    phaseResolvedOrbitProfileProves243_27_6RecognitionIsFalse :
      phaseResolvedOrbitProfileProves243_27_6Recognition ≡ false

canonicalPhaseResolvedSupportBoundary : PhaseResolvedSupportBoundary
canonicalPhaseResolvedSupportBoundary =
  phase-resolved-support-boundary
    false refl
    false refl
    true refl
    true refl
    false refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/magnet_duad_recognition_probe.py::raw_axis_support_closed_under_c3/phase_line_pair_orbit_profile"
