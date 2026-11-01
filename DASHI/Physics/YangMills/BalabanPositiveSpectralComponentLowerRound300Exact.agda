{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact where

------------------------------------------------------------------------
-- ROUND300 / POSITIVE SPECTRAL COMPONENT -> LOWER CORRELATION ENVELOPE
--
-- R298 still lists "spectral lower from overlap" as a physical theorem.  That
-- is stronger than the actual mathematical seam once the reconstructed
-- semigroup correlation is written on its positive spectral decomposition.
--
-- If the exact selected continuum correlation decomposes as
--
--   C(t) = w(F,v) q_E^t + R(t)
--
-- with R(t) >= 0, then the lower bound
--
--   w(F,v) q_E^t <= C(t)
--
-- is elementary ordered rational algebra.  R299 makes the selected cyclic
-- overlap weight strictly positive by construction.  Therefore the remaining
-- physical/spectral payment is the SAME-HAMILTONIAN decomposition itself, not
-- a second lower-bound theorem and not a second amplitude-positivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297

record PositiveSpectralComponentDecomposition
    {Measure TestObservable Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)) : Set₁ where
  field
    indexFor : TestObservable → Nat → R278.Index tests

    subgapRatio :
      ∀ energy → R297.SubgapMode family energy → ℚ

    spectralRemainder :
      ∀ energy → R297.SubgapMode family energy → Nat → ℚ

    spectralRemainderNonnegative :
      ∀ energy mode time →
      0ℚ ≤ spectralRemainder energy mode time

    -- The proof-bearing spectral theorem / same-Hamiltonian seam.  The selected
    -- continuum covariance is the contribution of the chosen subgap component
    -- plus a nonnegative remainder on the exact reconstructed carrier.
    selectedCorrelationSpectralDecomposition :
      ∀ energy (mode : R297.SubgapMode family energy) time →
      let observable =
            R297.modeObservableFromActualNonzeroFamily family energy mode
          weight =
            R299.overlapWeight quantitative
              (R299.vectorOfObservable quantitative observable)
              (R297.modeVector family energy mode)
      in
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests (indexFor observable time))
        (R278.right tests (indexFor observable time))
      ≡ weight * Power.rationalPower (subgapRatio energy mode) time
          + spectralRemainder energy mode time

open PositiveSpectralComponentDecomposition public

selectedOverlapWeight :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)} →
  PositiveSpectralComponentDecomposition dataSet extension tests quantitative family →
  ∀ energy → R297.SubgapMode family energy → ℚ
selectedOverlapWeight {quantitative = quantitative} {family = family}
    decomposition energy mode =
  let observable =
        R297.modeObservableFromActualNonzeroFamily family energy mode
  in
  R299.overlapWeight quantitative
    (R299.vectorOfObservable quantitative observable)
    (R297.modeVector family energy mode)

selectedOverlapWeightPositive :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    (decomposition : PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    energy (mode : R297.SubgapMode family energy) →
  0ℚ < selectedOverlapWeight decomposition energy mode
selectedOverlapWeightPositive {quantitative = quantitative} {family = family}
    decomposition energy mode =
  R299.chosenObservableOverlapWeightPositive family energy mode

spectralComponentBelowCorrelation :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    (decomposition : PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    energy (mode : R297.SubgapMode family energy) time →
  let observable =
        R297.modeObservableFromActualNonzeroFamily family energy mode
      component =
        selectedOverlapWeight decomposition energy mode
        * Power.rationalPower (subgapRatio decomposition energy mode) time
  in
  component ≤
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (indexFor decomposition observable time))
      (R278.right tests (indexFor decomposition observable time))
spectralComponentBelowCorrelation decomposition energy mode time =
  let
    component =
      selectedOverlapWeight decomposition energy mode
      * Power.rationalPower (subgapRatio decomposition energy mode) time
    remainder = spectralRemainder decomposition energy mode time
    componentPlusZeroBelowComponentPlusRemainder :
      component + 0ℚ ≤ component + remainder
    componentPlusZeroBelowComponentPlusRemainder =
      ℚP.+-mono-≤ ℚP.≤-refl
        (spectralRemainderNonnegative decomposition energy mode time)
    componentBelowSum : component ≤ component + remainder
    componentBelowSum =
      subst
        (λ lower → lower ≤ component + remainder)
        (ℚP.+-identityʳ component)
        componentPlusZeroBelowComponentPlusRemainder
  in
  subst
    (λ upper → component ≤ upper)
    (sym (selectedCorrelationSpectralDecomposition
      decomposition energy mode time))
    componentBelowSum

record Round300Boundary : Set where
  constructor round300-boundary
  field
    separateOverlapAmplitudePositivityLeaf : Bool
    separateOverlapAmplitudePositivityLeafIsFalse :
      separateOverlapAmplitudePositivityLeaf ≡ false

    separateSpectralLowerInequalityLeaf : Bool
    separateSpectralLowerInequalityLeafIsFalse :
      separateSpectralLowerInequalityLeaf ≡ false

    sameHamiltonianSpectralDecompositionStillRequired : Bool
    sameHamiltonianSpectralDecompositionStillRequiredIsTrue :
      sameHamiltonianSpectralDecompositionStillRequired ≡ true

    nonnegativeSpectralRemainderStillRequired : Bool
    nonnegativeSpectralRemainderStillRequiredIsTrue :
      nonnegativeSpectralRemainderStillRequired ≡ true

canonicalRound300Boundary : Round300Boundary
canonicalRound300Boundary =
  round300-boundary false refl false refl true refl true refl

round300PositiveComponentLowerCompilerLevel : ProofLevel
round300PositiveComponentLowerCompilerLevel = machineChecked

-- Standard spectral theorem mathematics plus the SAME reconstructed-Hamiltonian
-- / SAME selected-correlation identification.  This is the first genuine
-- spectral representation seam after the compiler reductions above.
round300SameHamiltonianPositiveSpectralDecompositionLevel : ProofLevel
round300SameHamiltonianPositiveSpectralDecompositionLevel = conditional
