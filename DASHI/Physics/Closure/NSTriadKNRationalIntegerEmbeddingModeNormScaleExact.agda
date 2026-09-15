module DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2c2a / RATIONAL INTEGER-EMBEDDING NORM SCALE
--
-- The two-shell gap is proved on the literal integer quantity
-- `modeNatNormSquared`, while the live R407 viscosity uses
-- `C3.normSquared I`.  Do not identify those carriers by fiat.
--
-- Over the rational carrier, however, every additive IntegerEmbedding is a
-- common scalar multiple of the standard integer embedding.  Put
--
--   c := E(1).
--
-- Then coordinatewise
--
--   E(z)^2 = c^2 * |z|^2,
--
-- and therefore
--
--   C3.normSquared I k = c^2 * natAsRational(modeNatNormSquared k).
--
-- Since c^2 >= 0, every concrete Nat frequency inequality transports to the
-- SAME live rational norm carrier used by R407.  This pays only the
-- same-object frequency-normalization seam; packet energy/dissipation sums and
-- the R98 SpectralCrossDissipationDatum remain the next leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNTwoShellLowRemoteEuclideanGapExact as Gap
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

F : C3.RealField _
F = Rational.rationalRealField

embeddingUnit : C3.IntegerEmbedding F → ℚ
embeddingUnit E = C3.embedInteger E (+ 1)

unitSquare : C3.IntegerEmbedding F → ℚ
unitSquare E = embeddingUnit E * embeddingUnit E

------------------------------------------------------------------------
-- Tiny Nat -> Q algebra for the exact S0 embedding.
------------------------------------------------------------------------

natAsRationalNonnegative : ∀ n → 0ℚ ≤ S0.natAsRational n
natAsRationalNonnegative zero = ℚP.≤-refl
natAsRationalNonnegative (suc n) =
  Rational.addNonnegative
    (subst (λ value → 0ℚ ≤ value) (sym (ℚP.+-identityʳ 1ℚ)) ℚP.≤-refl)
    (natAsRationalNonnegative n)

natAsRationalAdd : ∀ m n →
  S0.natAsRational (m + n)
  ≡ S0.natAsRational m + S0.natAsRational n
natAsRationalAdd zero n = sym (ℚP.+-identityˡ (S0.natAsRational n))
natAsRationalAdd (suc m) n
  rewrite natAsRationalAdd m n =
  solve (S0.natAsRational m ∷ S0.natAsRational n ∷ [])

natAsRationalMul : ∀ m n →
  S0.natAsRational (m * n)
  ≡ S0.natAsRational m * S0.natAsRational n
natAsRationalMul zero n = sym (ℚP.zero* (S0.natAsRational n))
natAsRationalMul (suc m) n
  rewrite natAsRationalAdd n (m * n)
        | natAsRationalMul m n =
  solve (S0.natAsRational m ∷ S0.natAsRational n ∷ [])

natAsRationalMonotone : ∀ {m n} → m ≤ n →
  S0.natAsRational m ≤ S0.natAsRational n
natAsRationalMonotone {zero} {n} z≤n = natAsRationalNonnegative n
natAsRationalMonotone {suc m} {suc n} (s≤s m≤n) =
  ℚP.+-mono-≤ ℚP.≤-refl (natAsRationalMonotone m≤n)

unitSquareNonnegative :
  (E : C3.IntegerEmbedding F) → 0ℚ ≤ unitSquare E
unitSquareNonnegative E = Rational.squareNonnegative (embeddingUnit E)

scaleMonotone :
  (E : C3.IntegerEmbedding F) →
  ∀ {left right} → left ≤ right →
  unitSquare E * left ≤ unitSquare E * right
scaleMonotone E left≤right =
  let instance unitNN = nonNegative (unitSquareNonnegative E)
  in ℚP.*-monoˡ-≤-nonNeg (unitSquare E) left≤right

------------------------------------------------------------------------
-- Every additive integer embedding into Q is one common scalar multiple.
------------------------------------------------------------------------

positiveNatEmbeddingScale :
  (E : C3.IntegerEmbedding F) →
  (n : Nat) →
  C3.embedInteger E (+ n)
  ≡ S0.natAsRational n * embeddingUnit E
positiveNatEmbeddingScale E zero =
  trans (C3.embedZero E) (sym (ℚP.zero* (embeddingUnit E)))
positiveNatEmbeddingScale E (suc n) =
  let
    step :
      C3.embedInteger E (+ suc n)
      ≡ C3.embedInteger E (+ 1) + C3.embedInteger E (+ n)
    step = C3.embedAdd E (+ 1) (+ n)
  in
  trans step
    (trans
      (cong₂ _+_ refl (positiveNatEmbeddingScale E n))
      (solve (S0.natAsRational n ∷ embeddingUnit E ∷ [])))

negativeMagnitudeEmbeddingScale :
  (E : C3.IntegerEmbedding F) →
  (n : Nat) →
  C3.embedInteger E (-[1+ n ])
  ≡ - (S0.natAsRational (suc n) * embeddingUnit E)
negativeMagnitudeEmbeddingScale E n =
  trans
    (C3.embedNegate E (+ suc n))
    (cong -_ (positiveNatEmbeddingScale E (suc n)))

coordinateSquareScale :
  (E : C3.IntegerEmbedding F) →
  (z : ℤ) →
  C3.embedInteger E z * C3.embedInteger E z
  ≡ unitSquare E
      * S0.natAsRational (ModeNorm.natSquare (Cube.integerMagnitude z))
coordinateSquareScale E (+ n)
  rewrite positiveNatEmbeddingScale E n
        | natAsRationalMul n n =
  solve (S0.natAsRational n ∷ embeddingUnit E ∷ [])
coordinateSquareScale E (-[1+ n ])
  rewrite negativeMagnitudeEmbeddingScale E n
        | natAsRationalMul (suc n) (suc n) =
  solve (S0.natAsRational (suc n) ∷ embeddingUnit E ∷ [])

modeNatNormAsRational : Z3.FourierMode → ℚ
modeNatNormAsRational mode =
  S0.natAsRational (ModeNorm.modeNatNormSquared mode)

modeNormCommonSquareScale :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  C3.normSquared I mode
  ≡ unitSquare E * modeNatNormAsRational mode
modeNormCommonSquareScale E I (Z3.mode x y z)
  rewrite C3.normSquaredMeaning I (Z3.mode x y z)
        | coordinateSquareScale E x
        | coordinateSquareScale E y
        | coordinateSquareScale E z
        | natAsRationalAdd
            (ModeNorm.natSquare (Cube.integerMagnitude x))
            (ModeNorm.natSquare (Cube.integerMagnitude y)
              + ModeNorm.natSquare (Cube.integerMagnitude z))
        | natAsRationalAdd
            (ModeNorm.natSquare (Cube.integerMagnitude y))
            (ModeNorm.natSquare (Cube.integerMagnitude z)) =
  solve
    ( embeddingUnit E
    ∷ S0.natAsRational (ModeNorm.natSquare (Cube.integerMagnitude x))
    ∷ S0.natAsRational (ModeNorm.natSquare (Cube.integerMagnitude y))
    ∷ S0.natAsRational (ModeNorm.natSquare (Cube.integerMagnitude z))
    ∷ [])

scaledNatFrequency : C3.IntegerEmbedding F → Nat → ℚ
scaledNatFrequency E n = unitSquare E * S0.natAsRational n

liveLowFrequencyCeiling :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  ∀ {low K} →
  Shell.shellIndex low < suc K →
  C3.normSquared I low
  ≤ scaledNatFrequency E (3 * R88.natSquare (Shell.pow2 K))
liveLowFrequencyCeiling E I {low} {K} lowShell =
  subst
    (λ left → left ≤ scaledNatFrequency E (3 * R88.natSquare (Shell.pow2 K)))
    (sym (modeNormCommonSquareScale E I low))
    (scaleMonotone E
      (natAsRationalMonotone (Gap.lowModeFrequencyCeiling lowShell)))

liveRemoteFrequencyFloor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  ∀ {remote K} →
  suc (suc K) ≤ Shell.shellIndex remote →
  scaledNatFrequency E (4 * R88.natSquare (Shell.pow2 K))
  ≤ C3.normSquared I remote
liveRemoteFrequencyFloor E I {remote} {K} remoteShell =
  subst
    (λ right →
      scaledNatFrequency E (4 * R88.natSquare (Shell.pow2 K)) ≤ right)
    (sym (modeNormCommonSquareScale E I remote))
    (scaleMonotone E
      (natAsRationalMonotone (Gap.remoteModeFrequencyFloor remoteShell)))

liveLowCeilingBelowRemoteFloor :
  (E : C3.IntegerEmbedding F) →
  (K : Nat) →
  scaledNatFrequency E (3 * R88.natSquare (Shell.pow2 K))
  ≤ scaledNatFrequency E (4 * R88.natSquare (Shell.pow2 K))
liveLowCeilingBelowRemoteFloor E K =
  scaleMonotone E
    (natAsRationalMonotone (Gap.lowCeilingBelowRemoteFloor K))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

integerEmbeddingCoordinateSquareScaleClosed : Bool
integerEmbeddingCoordinateSquareScaleClosed = true

modeNormCommonSquareScaleClosed : Bool
modeNormCommonSquareScaleClosed = true

shellGapTransportToLiveNormClosed : Bool
shellGapTransportToLiveNormClosed = true

integerEmbeddingCoordinateSquareScaleClosedIsTrue :
  integerEmbeddingCoordinateSquareScaleClosed ≡ true
integerEmbeddingCoordinateSquareScaleClosedIsTrue = refl

modeNormCommonSquareScaleClosedIsTrue :
  modeNormCommonSquareScaleClosed ≡ true
modeNormCommonSquareScaleClosedIsTrue = refl

shellGapTransportToLiveNormClosedIsTrue :
  shellGapTransportToLiveNormClosed ≡ true
shellGapTransportToLiveNormClosedIsTrue = refl
