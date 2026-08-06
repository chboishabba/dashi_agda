module DASHI.Physics.YangMills.BalabanP33UnscaledCyclePoincareWallExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- EXTERNAL STRESS-TEST TRIGGER, NOT A MATHEMATICAL DEPENDENCY
--
-- Lluis Eriksson,
-- "The Volume-Uniform Poincare Walls: Machine-Checked Obstructions for Flat
-- and Fluctuation-Sector Block-Poincare Routes to Combes--Thomas Coercivity
-- in Lattice Yang--Mills", ai.viXra:2607.0042, submitted 14 July 2026.
-- No DOI recorded.  No theorem or source code from that work is imported here.
--
-- DASHI CONTRIBUTION
--
-- Give a self-contained exact-rational obstruction to promoting a fixed-side
-- Poincare estimate to an unscaled volume-uniform estimate.
--
-- On the even cycle of side 2M, use the literal half-period square wave
--
--   (+1,...,+1,-1,...,-1),
--       M entries   M entries.
--
-- It has zero mean, norm square 2M, and cyclic nearest-neighbour energy 8:
-- only the two interfaces contribute, each by (1-(-1))^2=4.  Consequently a
-- Poincare constant c valid on every unscaled even cycle would satisfy
--
--   c (2M) <= 8.
--
-- Taking M=256 contradicts c=1/32, since the asserted inequality becomes
-- 16 <= 8.  This does not contradict the repository's literal side-four
-- theorem.  It proves that the latter is fixed-volume/terminal-scale data and
-- may not be silently promoted to a bare volume-uniform gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (length; _++_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Elementary exact finite-list calculus.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

sq : ℚ → ℚ
sq value = value * value

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

constantRun : Nat → ℚ → List ℚ
constantRun zero value = []
constantRun (suc n) value = value ∷ constantRun n value

sumValues : List ℚ → ℚ
sumValues [] = 0ℚ
sumValues (value ∷ values) = value + sumValues values

sumSquares : List ℚ → ℚ
sumSquares [] = 0ℚ
sumSquares (value ∷ values) = sq value + sumSquares values

lengthAppend : ∀ left right →
  length (left ++ right) ≡ length left + length right
lengthAppend [] right = refl
lengthAppend (value ∷ values) right =
  cong suc (lengthAppend values right)

constantRunLength : ∀ n value →
  length (constantRun n value) ≡ n
constantRunLength zero value = refl
constantRunLength (suc n) value =
  cong suc (constantRunLength n value)

sumValuesAppend : ∀ left right →
  sumValues (left ++ right) ≡ sumValues left + sumValues right
sumValuesAppend [] right = ℚRing.solve-∀ (sumValues right)
sumValuesAppend (value ∷ values) right =
  trans
    (cong (value +_) (sumValuesAppend values right))
    (ℚRing.solve-∀ value (sumValues values) (sumValues right))

sumSquaresAppend : ∀ left right →
  sumSquares (left ++ right) ≡ sumSquares left + sumSquares right
sumSquaresAppend [] right = ℚRing.solve-∀ (sumSquares right)
sumSquaresAppend (value ∷ values) right =
  trans
    (cong (sq value +_) (sumSquaresAppend values right))
    (ℚRing.solve-∀ (sq value) (sumSquares values) (sumSquares right))

constantRunSum : ∀ n value →
  sumValues (constantRun n value)
  ≡ natAsRational n * value
constantRunSum zero value = ℚRing.solve-∀ value
constantRunSum (suc n) value
  rewrite constantRunSum n value =
  ℚRing.solve-∀ (natAsRational n) value

constantRunSquareSum : ∀ n value →
  sumSquares (constantRun n value)
  ≡ natAsRational n * sq value
constantRunSquareSum zero value = ℚRing.solve-∀ value
constantRunSquareSum (suc n) value
  rewrite constantRunSquareSum n value =
  ℚRing.solve-∀ (natAsRational n) value

------------------------------------------------------------------------
-- Cyclic nearest-neighbour energy of a literal list.
------------------------------------------------------------------------

lastOr : ℚ → List ℚ → ℚ
lastOr fallback [] = fallback
lastOr fallback (value ∷ values) = lastOr value values

pathEnergyFrom : ℚ → List ℚ → ℚ
pathEnergyFrom previous [] = 0ℚ
pathEnergyFrom previous (value ∷ values) =
  sq (value - previous) + pathEnergyFrom value values

cycleEnergy : List ℚ → ℚ
cycleEnergy [] = 0ℚ
cycleEnergy (first ∷ rest) =
  pathEnergyFrom first rest + sq (first - lastOr first rest)

lastOrConstantSame : ∀ n value →
  lastOr value (constantRun n value) ≡ value
lastOrConstantSame zero value = refl
lastOrConstantSame (suc n) value =
  lastOrConstantSame n value

lastOrConstantNonempty : ∀ fallback n value →
  lastOr fallback (constantRun (suc n) value) ≡ value
lastOrConstantNonempty fallback n value =
  lastOrConstantSame n value

lastOrAppend : ∀ fallback left right →
  lastOr fallback (left ++ right)
  ≡ lastOr (lastOr fallback left) right
lastOrAppend fallback [] right = refl
lastOrAppend fallback (value ∷ values) right =
  lastOrAppend value values right

pathEnergyConstantSame : ∀ n value →
  pathEnergyFrom value (constantRun n value) ≡ 0ℚ
pathEnergyConstantSame zero value = refl
pathEnergyConstantSame (suc n) value
  rewrite pathEnergyConstantSame n value =
  ℚRing.solve-∀ value

pathEnergyConstantDifferent : ∀ n previous value →
  pathEnergyFrom previous (constantRun (suc n) value)
  ≡ sq (value - previous)
pathEnergyConstantDifferent n previous value
  rewrite pathEnergyConstantSame n value =
  ℚRing.solve-∀ previous value

pathEnergyAppend : ∀ previous left right →
  pathEnergyFrom previous (left ++ right)
  ≡ pathEnergyFrom previous left
    + pathEnergyFrom (lastOr previous left) right
pathEnergyAppend previous [] right =
  ℚRing.solve-∀ (pathEnergyFrom previous right)
pathEnergyAppend previous (value ∷ values) right
  rewrite pathEnergyAppend value values right =
  ℚRing.solve-∀
    (sq (value - previous))
    (pathEnergyFrom value values)
    (pathEnergyFrom (lastOr value values) right)

------------------------------------------------------------------------
-- The half-period square wave.
------------------------------------------------------------------------

halfPeriodSquareWave : Nat → List ℚ
halfPeriodSquareWave halfSide =
  constantRun halfSide 1ℚ ++ constantRun halfSide (- 1ℚ)

halfPeriodSquareWaveLength : ∀ halfSide →
  length (halfPeriodSquareWave halfSide)
  ≡ halfSide + halfSide
halfPeriodSquareWaveLength halfSide =
  trans
    (lengthAppend
      (constantRun halfSide 1ℚ)
      (constantRun halfSide (- 1ℚ)))
    (cong₂ _+_
      (constantRunLength halfSide 1ℚ)
      (constantRunLength halfSide (- 1ℚ)))

halfPeriodSquareWaveMeanZero : ∀ halfSide →
  sumValues (halfPeriodSquareWave halfSide) ≡ 0ℚ
halfPeriodSquareWaveMeanZero halfSide =
  trans
    (sumValuesAppend
      (constantRun halfSide 1ℚ)
      (constantRun halfSide (- 1ℚ)))
    (trans
      (cong₂ _+_
        (constantRunSum halfSide 1ℚ)
        (constantRunSum halfSide (- 1ℚ)))
      (ℚRing.solve-∀ (natAsRational halfSide)))

halfPeriodSquareWaveNormExact : ∀ halfSide →
  sumSquares (halfPeriodSquareWave halfSide)
  ≡ (+ 2 / 1) * natAsRational halfSide
halfPeriodSquareWaveNormExact halfSide =
  trans
    (sumSquaresAppend
      (constantRun halfSide 1ℚ)
      (constantRun halfSide (- 1ℚ)))
    (trans
      (cong₂ _+_
        (constantRunSquareSum halfSide 1ℚ)
        (constantRunSquareSum halfSide (- 1ℚ)))
      (ℚRing.solve-∀ (natAsRational halfSide)))

halfPeriodSquareWaveCycleEnergyExact : ∀ n →
  cycleEnergy (halfPeriodSquareWave (suc n)) ≡ + 8 / 1
halfPeriodSquareWaveCycleEnergyExact n =
  let
    positiveTail = constantRun n 1ℚ
    negativeRun = constantRun (suc n) (- 1ℚ)

    pathExact :
      pathEnergyFrom 1ℚ (positiveTail ++ negativeRun)
      ≡ + 4 / 1
    pathExact =
      trans
        (pathEnergyAppend 1ℚ positiveTail negativeRun)
        (trans
          (cong₂ _+_
            (pathEnergyConstantSame n 1ℚ)
            (subst
              (λ start →
                pathEnergyFrom start negativeRun
                ≡ sq ((- 1ℚ) - 1ℚ))
              (sym (lastOrConstantSame n 1ℚ))
              (pathEnergyConstantDifferent n 1ℚ (- 1ℚ))))
          (ℚRing.solve []))

    lastExact :
      lastOr 1ℚ (positiveTail ++ negativeRun) ≡ - 1ℚ
    lastExact =
      trans
        (lastOrAppend 1ℚ positiveTail negativeRun)
        (lastOrConstantNonempty (lastOr 1ℚ positiveTail) n (- 1ℚ))
  in
  trans
    (cong₂ _+_
      pathExact
      (cong sq (cong (1ℚ -_) lastExact)))
    (ℚRing.solve [])

------------------------------------------------------------------------
-- The exact volume-uniform obstruction.
------------------------------------------------------------------------

record UnscaledEvenCyclePoincareAt
    (halfSide : Nat) (coercivity : ℚ) : Set where
  field
    bound : ∀ values →
      length values ≡ halfSide + halfSide →
      sumValues values ≡ 0ℚ →
      coercivity * sumSquares values ≤ cycleEnergy values

open UnscaledEvenCyclePoincareAt public

UniformUnscaledEvenCyclePoincare : ℚ → Set
UniformUnscaledEvenCyclePoincare coercivity =
  ∀ predecessor →
    UnscaledEvenCyclePoincareAt (suc predecessor) coercivity

oneThirtySecond : ℚ
oneThirtySecond = + 1 / 32

squareWave256LeftExact :
  oneThirtySecond * sumSquares (halfPeriodSquareWave 256)
  ≡ + 16 / 1
squareWave256LeftExact =
  trans
    (cong (oneThirtySecond *_)
      (halfPeriodSquareWaveNormExact 256))
    (ℚRing.solve [])

squareWave256EnergyExact :
  cycleEnergy (halfPeriodSquareWave 256) ≡ + 8 / 1
squareWave256EnergyExact =
  halfPeriodSquareWaveCycleEnergyExact 255

sixteenNotBelowEight : Not ((+ 16 / 1) ≤ (+ 8 / 1))
sixteenNotBelowEight ()

oneThirtySecondNotUniformUnscaled :
  Not (UniformUnscaledEvenCyclePoincare oneThirtySecond)
oneThirtySecondNotUniformUnscaled uniform =
  let
    at256 = uniform 255

    asserted :
      oneThirtySecond * sumSquares (halfPeriodSquareWave 256)
      ≤ cycleEnergy (halfPeriodSquareWave 256)
    asserted =
      bound at256
        (halfPeriodSquareWave 256)
        (halfPeriodSquareWaveLength 256)
        (halfPeriodSquareWaveMeanZero 256)

    concrete : (+ 16 / 1) ≤ (+ 8 / 1)
    concrete =
      subst
        (λ left → left ≤ + 8 / 1)
        squareWave256LeftExact
        (subst
          (λ right →
            oneThirtySecond * sumSquares (halfPeriodSquareWave 256)
            ≤ right)
          squareWave256EnergyExact
          asserted)
  in
  sixteenNotBelowEight concrete

unscaledSquareWaveMeanZeroLevel : ProofLevel
unscaledSquareWaveMeanZeroLevel = machineChecked

unscaledSquareWaveNormLevel : ProofLevel
unscaledSquareWaveNormLevel = machineChecked

unscaledSquareWaveCycleEnergyLevel : ProofLevel
unscaledSquareWaveCycleEnergyLevel = machineChecked

oneThirtySecondBareVolumeUniformPoincareLevel : ProofLevel
oneThirtySecondBareVolumeUniformPoincareLevel = machineChecked
