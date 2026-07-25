module DASHI.Physics.Closure.NSPeriodicInfinityShellBernstein where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
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

infinityShellBernsteinReductionLevel : ProofLevel
infinityShellBernsteinReductionLevel = machineChecked

finiteFourierCauchySchwarzAuthorityLevel : ProofLevel
finiteFourierCauchySchwarzAuthorityLevel = standardImported

coarseThreeSqrtThreeConstantLevel : ProofLevel
coarseThreeSqrtThreeConstantLevel = conditional
