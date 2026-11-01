module DASHI.Physics.Closure.NSPeriodicInfinityShellBernstein where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as Count
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Direct Bernstein reduction for max-coordinate Fourier support.
--
-- The finite combinatorial factor is exactly the cardinality of the literal
-- outer cube from NSPeriodicInfinityShellModeCount.  The only imported analysis
-- is finite Cauchy-Schwarz plus Parseval on the chosen Fourier normalization.
-- No Euclidean-shell comparison occurs in this module.
------------------------------------------------------------------------

record InfinityShellBernsteinInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i) : Set (lsuc i) where
  field
    ShellSupported : Nat → State → Set i

    coefficientL2 physicalL2 lInfinity : Nat → State → Scalar A

    natSquareRootEmbed : Nat → Scalar A
    scale : Scalar A → Scalar A → Scalar A

    modeCountFactor : Nat → Scalar A
    modeCountFactorMeaning : ∀ n →
      modeCountFactor n
      ≡ natSquareRootEmbed (Count.infinityCubeModeCount n)

    finiteFourierCauchySchwarz : ∀ n state →
      ShellSupported n state →
      _≤_ A
        (lInfinity n state)
        (scale (modeCountFactor n) (coefficientL2 n state))

    shellParseval : ∀ n state →
      coefficientL2 n state ≡ physicalL2 n state

open InfinityShellBernsteinInputs public

infinityShellBernsteinExactCount :
  ∀ {i} {A : AbsorptionArithmetic} {State : Set i} →
  (I : InfinityShellBernsteinInputs A State) →
  ∀ n state → ShellSupported I n state →
  _≤_ A
    (lInfinity I n state)
    (scale I
      (natSquareRootEmbed I (Count.infinityCubeModeCount n))
      (physicalL2 I n state))
infinityShellBernsteinExactCount {A = A} I n state supported =
  subst
    (λ coefficientNorm →
      _≤_ A
        (lInfinity I n state)
        (scale I
          (natSquareRootEmbed I (Count.infinityCubeModeCount n))
          coefficientNorm))
    (shellParseval I n state)
    (subst
      (λ factor →
        _≤_ A
          (lInfinity I n state)
          (scale I factor (coefficientL2 I n state)))
      (modeCountFactorMeaning I n)
      (finiteFourierCauchySchwarz I n state supported))

record CoarseDyadicBernsteinFactor
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i)
    (I : InfinityShellBernsteinInputs A State) : Set (lsuc i) where
  field
    dyadicThreeHalvesFactor : Nat → Scalar A
    coarseConstant : Scalar A

    exactCountFactorBelowCoarse : ∀ n state →
      _≤_ A
        (scale I
          (natSquareRootEmbed I (Count.infinityCubeModeCount n))
          (physicalL2 I n state))
        (scale I
          (dyadicThreeHalvesFactor n)
          (physicalL2 I n state))

open CoarseDyadicBernsteinFactor public

infinityShellBernsteinCoarseDyadic :
  ∀ {i} {A : AbsorptionArithmetic} {State : Set i} →
  (I : InfinityShellBernsteinInputs A State) →
  (C : CoarseDyadicBernsteinFactor A State I) →
  ∀ n state → ShellSupported I n state →
  _≤_ A
    (lInfinity I n state)
    (scale I (dyadicThreeHalvesFactor C n) (physicalL2 I n state))
infinityShellBernsteinCoarseDyadic {A = A} I C n state supported =
  ≤-trans A
    (infinityShellBernsteinExactCount I n state supported)
    (exactCountFactorBelowCoarse C n state)

record InfinityShellBernsteinSquaredInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i) : Set (lsuc i) where
  field
    pointwiseValueSquared : Nat → State → Scalar A
    physicalL2Squared : Nat → State → Scalar A
    shellCoefficients : Nat → State → List (Scalar A)
    sumCoefficientsSquared : List (Scalar A) → Scalar A
    sumCoefficientsSqSum : List (Scalar A) → Scalar A
    scaleNat : Nat → Scalar A → Scalar A

    pointwiseBound : ∀ n state →
      _≤_ A
        (pointwiseValueSquared n state)
        (sumCoefficientsSquared (shellCoefficients n state))

    coefficientBernsteinSquared : ∀ n state →
      _≤_ A
        (sumCoefficientsSquared (shellCoefficients n state))
        (scaleNat (27 * (Count.pow2 n * (Count.pow2 n * Count.pow2 n)))
          (sumCoefficientsSqSum (shellCoefficients n state)))

    shellParsevalSquared : ∀ n state →
      sumCoefficientsSqSum (shellCoefficients n state) ≡ physicalL2Squared n state

open InfinityShellBernsteinSquaredInputs public

infinityShellBernsteinSquaredExact :
  ∀ {i} {A : AbsorptionArithmetic} {State : Set i} →
  (I : InfinityShellBernsteinSquaredInputs A State) →
  ∀ n state →
  _≤_ A
    (pointwiseValueSquared I n state)
    (scaleNat I
      (27 * (Count.pow2 n * (Count.pow2 n * Count.pow2 n)))
      (physicalL2Squared I n state))
infinityShellBernsteinSquaredExact {A = A} I n state =
  subst
    (λ l2 →
      _≤_ A
        (pointwiseValueSquared I n state)
        (scaleNat I (27 * (Count.pow2 n * (Count.pow2 n * Count.pow2 n))) l2))
    (shellParsevalSquared I n state)
    (≤-trans A
      (pointwiseBound I n state)
      (coefficientBernsteinSquared I n state))

infinityShellBernsteinReductionLevel : ProofLevel
infinityShellBernsteinReductionLevel = machineChecked

infinityShellBernsteinSquaredReductionLevel : ProofLevel
infinityShellBernsteinSquaredReductionLevel = machineChecked

finiteFourierCauchySchwarzAuthorityLevel : ProofLevel
finiteFourierCauchySchwarzAuthorityLevel = standardImported

coarseThreeSqrtThreeConstantLevel : ProofLevel
coarseThreeSqrtThreeConstantLevel = conditional
