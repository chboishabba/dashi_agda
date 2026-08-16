module DASHI.Physics.YangMills.Balaban1989RationalInverseSquareSmallCouplingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Close the rational representation leaf left by the terminal-history module.
-- Write u=g^{-2} and tau=gamma^{-2}, but do NOT use a square-root operation or
-- reciprocal-monotonicity lemma.  Instead assume the exact multiplicative
-- coordinate meanings
--
--      tau * gamma^2 = 1,
--      u   * g^2     = 1.
--
-- If 0<tau<=u, multiplying tau<=u by gamma^2 gives
--
--      1 <= u * gamma^2.
--
-- Replacing 1 by u*g^2 and cancelling positive u gives g^2<=gamma^2.
-- Nonnegative square-order reflection then yields g<=gamma.
--
-- This is exactly the order conversion needed by CMP122 Theorem 1.  It is
-- finite ordered-field algebra, not an RG assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; Positive; NonNegative; NonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact as Step
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact as History

squareNonnegative : ∀ value → 0ℚ ≤ value * value
squareNonnegative value = ℚP.nonNegative⁻¹ (value * value)

nonnegativeSquareReflectsOrder :
  ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right →
  left * left ≤ right * right →
  left ≤ right
nonnegativeSquareReflectsOrder left right leftNN rightNN squares
  with ℚP.≤-total left right
... | inj₁ leftBelow = leftBelow
... | inj₂ rightBelow with ℚP._≡?_ left 0ℚ
...   | yes leftZero =
  subst (λ selected → selected ≤ right) (sym leftZero) rightNN
...   | no leftNonzero =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN

      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN

      leftNonZero : NonZero left
      leftNonZero = ℚ.≢-nonZero leftNonzero

      leftPositive : Positive left
      leftPositive = ℚP.nonNeg∧nonZero⇒pos left

    rightSquareBelowRightLeft : right * right ≤ right * left
    rightSquareBelowRightLeft =
      ℚP.*-monoˡ-≤-nonNeg right rightBelow

    leftSquareBelowRightLeft : left * left ≤ right * left
    leftSquareBelowRightLeft =
      ℚP.≤-trans squares rightSquareBelowRightLeft
  in
  ℚP.*-cancelʳ-≤-pos left leftSquareBelowRightLeft

record RationalInverseSquareCoordinate : Set₁ where
  field
    coupling inverseCoupling gamma inverseThreshold : ℚ

    couplingNonnegative : 0ℚ ≤ coupling
    gammaNonnegative : 0ℚ ≤ gamma
    inverseThresholdPositive : 0ℚ < inverseThreshold

    thresholdCoordinateExact :
      inverseThreshold * (gamma * gamma) ≡ 1ℚ
    inverseCoordinateExact :
      inverseCoupling * (coupling * coupling) ≡ 1ℚ

open RationalInverseSquareCoordinate public

inverseSquareThresholdImpliesSmallCoupling :
  (coordinate : RationalInverseSquareCoordinate) →
  inverseThreshold coordinate ≤ inverseCoupling coordinate →
  coupling coordinate ≤ gamma coordinate
inverseSquareThresholdImpliesSmallCoupling coordinate thresholdBelow =
  let
    g = coupling coordinate
    u = inverseCoupling coordinate
    gammaValue = gamma coordinate
    threshold = inverseThreshold coordinate
    gammaSq = gammaValue * gammaValue
    gSq = g * g

    gammaSqNN : 0ℚ ≤ gammaSq
    gammaSqNN = squareNonnegative gammaValue

    scaledRaw :
      gammaSq * threshold ≤ gammaSq * u
    scaledRaw = Norm.scaleNonnegative gammaSq gammaSqNN thresholdBelow

    scaled : threshold * gammaSq ≤ u * gammaSq
    scaled = subst
      (λ lower → lower ≤ u * gammaSq)
      (ℚP.*-comm gammaSq threshold)
      (subst
        (λ upper → gammaSq * threshold ≤ upper)
        (ℚP.*-comm gammaSq u)
        scaledRaw)

    oneBelow : 1ℚ ≤ u * gammaSq
    oneBelow = subst
      (λ lower → lower ≤ u * gammaSq)
      (thresholdCoordinateExact coordinate)
      scaled

    uncancelled : u * gSq ≤ u * gammaSq
    uncancelled = subst
      (λ lower → lower ≤ u * gammaSq)
      (sym (inverseCoordinateExact coordinate))
      oneBelow

    uPositiveProof : 0ℚ < u
    uPositiveProof =
      ℚP.<-≤-trans (inverseThresholdPositive coordinate) thresholdBelow

    instance
      uPositive : Positive u
      uPositive = ℚ.positive uPositiveProof

    squares : gSq ≤ gammaSq
    squares = ℚP.*-cancelˡ-≤-pos u uncancelled
  in
  nonnegativeSquareReflectsOrder
    g gammaValue
    (couplingNonnegative coordinate)
    (gammaNonnegative coordinate)
    squares

record RationalInverseSquareTerminalHistory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    couplingAt : Nat → ℚ
    gamma inverseThreshold : ℚ
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale
    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤ Flow.inverseCoupling trajectory terminalScale
    betaNonnegative : Step.NonnegativeBetaTrajectory trajectory

    gammaNonnegative : 0ℚ ≤ gamma
    inverseThresholdPositive : 0ℚ < inverseThreshold
    thresholdCoordinateExact :
      inverseThreshold * (gamma * gamma) ≡ 1ℚ

    couplingNonnegative : ∀ scale → 0ℚ ≤ couplingAt scale
    inverseCoordinateExact : ∀ scale →
      Flow.inverseCoupling trajectory scale
        * (couplingAt scale * couplingAt scale)
      ≡ 1ℚ

open RationalInverseSquareTerminalHistory public

coordinateAt :
  ∀ {trajectory} → RationalInverseSquareTerminalHistory trajectory →
  Nat → RationalInverseSquareCoordinate
coordinateAt {trajectory} history scale = record
  { coupling = couplingAt history scale
  ; inverseCoupling = Flow.inverseCoupling trajectory scale
  ; gamma = gamma history
  ; inverseThreshold = inverseThreshold history
  ; couplingNonnegative = couplingNonnegative history scale
  ; gammaNonnegative = gammaNonnegative history
  ; inverseThresholdPositive = inverseThresholdPositive history
  ; thresholdCoordinateExact = thresholdCoordinateExact history
  ; inverseCoordinateExact = inverseCoordinateExact history scale
  }

asTerminalInverseThresholdHistory :
  ∀ {trajectory} →
  RationalInverseSquareTerminalHistory trajectory →
  History.TerminalInverseThresholdHistory trajectory
asTerminalInverseThresholdHistory history = record
  { History.TerminalInverseThresholdHistory.couplingAt = couplingAt history
  ; History.TerminalInverseThresholdHistory.gamma = gamma history
  ; History.TerminalInverseThresholdHistory.inverseThreshold =
      inverseThreshold history
  ; History.TerminalInverseThresholdHistory.terminalScale = terminalScale history
  ; History.TerminalInverseThresholdHistory.ActiveScale = ActiveScale history
  ; History.TerminalInverseThresholdHistory.terminalActive = terminalActive history
  ; History.TerminalInverseThresholdHistory.gapToTerminal = gapToTerminal history
  ; History.TerminalInverseThresholdHistory.scaleReachesTerminal =
      scaleReachesTerminal history
  ; History.TerminalInverseThresholdHistory.terminalInverseThreshold =
      terminalInverseThreshold history
  ; History.TerminalInverseThresholdHistory.betaNonnegative =
      betaNonnegative history
  ; History.TerminalInverseThresholdHistory.inverseThresholdImpliesSmallCoupling =
      λ scale thresholdBelow →
        inverseSquareThresholdImpliesSmallCoupling
          (coordinateAt history scale) thresholdBelow
  }

rationalInverseSquareOrderConversionLevel : ProofLevel
rationalInverseSquareOrderConversionLevel = machineChecked

rationalInverseSquareTerminalHistoryAdapterLevel : ProofLevel
rationalInverseSquareTerminalHistoryAdapterLevel = machineChecked
