module DASHI.Reasoning.LeechPuncturedNineLearningBridgeExact where

-- Cross-owner adapter (no --safe promotion before import closure check).
-- Actual eight-point source: OggSSPP2BalancedTernaryPuncturedPlaneExact.
-- Distinguish point antipode, global coefficient sign, and Fourier
-- character conjugation: they are not definitionally identical.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Reasoning.LeechPuncturedNineArithmeticExact as Arithmetic
import DASHI.Foundations.Base369FaceSheetPunctureIncidenceIdentityExact as Face
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.JInvariant369CodecBidiExact as JCodec
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Nonary
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as JLevel
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response

-- The eight nonzero spatial points of F3², not eight Fourier modes.
PuncturedPoint : Set
PuncturedPoint = Plane.PuncturedNineSheet

oppositePoint : PuncturedPoint → PuncturedPoint
oppositePoint Plane.negativeFirstAxis = Plane.positiveFirstAxis
oppositePoint Plane.positiveFirstAxis = Plane.negativeFirstAxis
oppositePoint Plane.negativeSecondAxis = Plane.positiveSecondAxis
oppositePoint Plane.positiveSecondAxis = Plane.negativeSecondAxis
oppositePoint Plane.negativeEqualDiagonal = Plane.positiveEqualDiagonal
oppositePoint Plane.positiveEqualDiagonal = Plane.negativeEqualDiagonal
oppositePoint Plane.negativeOppositeDiagonal = Plane.positiveOppositeDiagonal
oppositePoint Plane.positiveOppositeDiagonal = Plane.negativeOppositeDiagonal

oppositePointTwice :
  (point : PuncturedPoint) → oppositePoint (oppositePoint point) ≡ point
oppositePointTwice Plane.negativeFirstAxis = refl
oppositePointTwice Plane.positiveFirstAxis = refl
oppositePointTwice Plane.negativeSecondAxis = refl
oppositePointTwice Plane.positiveSecondAxis = refl
oppositePointTwice Plane.negativeEqualDiagonal = refl
oppositePointTwice Plane.positiveEqualDiagonal = refl
oppositePointTwice Plane.negativeOppositeDiagonal = refl
oppositePointTwice Plane.positiveOppositeDiagonal = refl

-- This is a continuous/real-valued COEFFICIENT array indexed by a
-- discrete eight-element sheet, not a T^24 finite trit state.
record WaveBlock24 (Coefficient : Set) : Set where
  constructor waveBlock24
  field
    firstLane : PuncturedPoint → Coefficient
    secondLane : PuncturedPoint → Coefficient
    thirdLane : PuncturedPoint → Coefficient
open WaveBlock24 public

-- A transported wave field must distinguish a global amplitude sign
-- (acting on coefficients) from a site antipode (acting on indices).
record CoefficientSign (Coefficient : Set) : Set where
  field
    negateCoefficient : Coefficient → Coefficient
    negateTwice : (x : Coefficient) →
      negateCoefficient (negateCoefficient x) ≡ x
open CoefficientSign public

applyCoefficientSign :
  ∀ {A : Set} →
  CoefficientSign A → WaveBlock24 A → WaveBlock24 A
applyCoefficientSign signed block =
  waveBlock24
    (λ p → negateCoefficient signed (firstLane block p))
    (λ p → negateCoefficient signed (secondLane block p))
    (λ p → negateCoefficient signed (thirdLane block p))

-- Pointwise involution does not require function extensionality.
coefficientSignTwicePointwise :
  ∀ {A : Set} (signed : CoefficientSign A)
  (block : WaveBlock24 A) (p : PuncturedPoint) →
  firstLane (applyCoefficientSign signed
    (applyCoefficientSign signed block)) p ≡ firstLane block p
coefficientSignTwicePointwise signed block p =
  negateTwice signed (firstLane block p)

applyPointAntipode :
  ∀ {A : Set} → WaveBlock24 A → WaveBlock24 A
applyPointAntipode block =
  waveBlock24
    (λ p → firstLane block (oppositePoint p))
    (λ p → secondLane block (oppositePoint p))
    (λ p → thirdLane block (oppositePoint p))

pointAntipodeTwiceFirstLane :
  ∀ {A : Set} (block : WaveBlock24 A) (p : PuncturedPoint) →
  firstLane (applyPointAntipode (applyPointAntipode block)) p
    ≡ firstLane block p
pointAntipodeTwiceFirstLane block p
  rewrite oppositePointTwice p = refl

-- Fourier phase conjugation is owned separately by
-- C3FourierConjugationExact; the analytic J/phase payload is owned
-- separately by JInvariant369CodecBidiExact, and is NOT compressed or
-- identified by merely reindexing the eight-point carrier.
puncturedCount : Plane.puncturedNineSheetCount ≡ 8
puncturedCount = Plane.puncturedNineSheetCountIsThreeSquaredMinusOne

faceNineHasEightPunctures :
  Face.faceSheetCount ≡ 1 + Face.puncturedFaceCount
faceNineHasEightPunctures = refl

-- Opposing arguments are Response.ResponseKind values; this adapter
-- supplies no semantic-to-oppositePoint coercion.
ArgumentKind : Set
ArgumentKind = Response.ResponseKind


-- Decisive previously-proved algebraic firewall:
-- T² = C3 × C3 has exponent three, while Z/9 is cyclic and
-- contains an element of order nine. The two nine-element carriers
-- admit a set-theoretic rechart, NOT a group-action isomorphism.
phaseNineNotCyclicNonaryGroupIso :
  Nonary.Q9NonaryGroupIsomorphism → ⊥
phaseNineNotCyclicNonaryGroupIso =
  Nonary.q9NonaryGroupIsomorphismImpossible

-- The analytic j observer lives over a same-point modular fibre.
-- JInvariant369PhaseLevelSeparationExact proves phase-only C3
-- cannot recover nontrivial level translations; no Fourier-to-j
-- identification or modular-level 9-action is claimed here.
