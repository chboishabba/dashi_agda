module DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalWeightedPowerDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Complete the rational Combes--Thomas residual estimate in both Schur
-- directions.  The same explicit diagonal weight used for the row estimate
-- yields, by summing the entrywise bound over rows,
--
--   columnMass(D R_A D^-1)
--     <= (6561/4096) columnMass(R_A)
--      <= 686287161/4294967296
--      < 1/6.
--
-- The finite l1 theorem then gives an actual weighted vector contraction and
-- the geometric power estimate
--
--   ||(D R_A D^-1)^n v||_1 <= (1/6)^n ||v||_1.
--
-- This closes the finite weighted residual-decay calculation required by a
-- Neumann/Combes--Thomas construction.  The only remaining inverse issue is
-- the infinite-limit/completeness (or exact finite inverse) bridge, not
-- smallness of the physical residual.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact as TwoSided
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeVector : Set
GaugeVector = Contraction.GaugeRow → ℚ

weightedColumnMassUpper : ∀ root kernel column →
  ColumnMass.squareColumnMass Contraction.gaugeRows
    (Weight.weightedKernel root kernel) column
  ≤ ColumnMass.squareColumnMass Contraction.gaugeRows kernel column
      * Weight.siteGrowthEnvelope
weightedColumnMassUpper root kernel column =
  let
    pointwise = Schur.sumPointwiseBelow Contraction.gaugeRows _ _
      (λ row → Weight.weightedEntryAbsoluteUpper root kernel row column)

    factor :
      Sums.sumRational Contraction.gaugeRows
        (λ row → ∣ kernel row column ∣ * Weight.siteGrowthEnvelope)
      ≡ ColumnMass.squareColumnMass Contraction.gaugeRows kernel column
          * Weight.siteGrowthEnvelope
    factor =
      trans
        (Sums.sumRationalCong Contraction.gaugeRows _ _
          (λ row → ℚP.*-comm ∣ kernel row column ∣ Weight.siteGrowthEnvelope))
        (trans
          (Sums.sumRationalScale Weight.siteGrowthEnvelope
            Contraction.gaugeRows (λ row → ∣ kernel row column ∣))
          (ℚP.*-comm Weight.siteGrowthEnvelope
            (ColumnMass.squareColumnMass Contraction.gaugeRows kernel column)))
  in
  subst
    (λ upper →
      ColumnMass.squareColumnMass Contraction.gaugeRows
        (Weight.weightedKernel root kernel) column ≤ upper)
    factor pointwise

selectedBackgroundWeightedGreenPerturbationAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root column →
  ColumnMass.squareColumnMass Contraction.gaugeRows
    (Weight.weightedSelectedBackgroundResidual root background) column
  ≤ Weight.weightedContractionBound
selectedBackgroundWeightedGreenPerturbationAbsoluteColumnMassBound
    background radius root column =
  let
    raw = weightedColumnMassUpper root
      (Contraction.flatGreenTimesPerturbationKernel background) column

    scaled = PerturbationMass.rightScaleMonotone Weight.siteGrowthEnvelope
      (ColumnMass.squareColumnMass Contraction.gaugeRows
        (Contraction.flatGreenTimesPerturbationKernel background) column)
      Contraction.greenPerturbationContractionBound
      (ℚP.nonNegative⁻¹ Weight.siteGrowthEnvelope)
      (TwoSided.selectedBackgroundFlatGreenPerturbationAbsoluteColumnMassBound
        background radius column)
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        ColumnMass.squareColumnMass Contraction.gaugeRows
          (Contraction.flatGreenTimesPerturbationKernel background) column
          * Weight.siteGrowthEnvelope ≤ upper)
      Weight.weightedContractionExactProduct scaled)

selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root column →
  ColumnMass.squareColumnMass Contraction.gaugeRows
    (Weight.weightedSelectedBackgroundResidual root background) column
  ≤ + 1 / 6
selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction
    background radius root column =
  ℚP.≤-trans
    (selectedBackgroundWeightedGreenPerturbationAbsoluteColumnMassBound
      background radius root column)
    Weight.weightedContractionBelowOneSixth

weightedResidualApply :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  GaugeVector → GaugeVector
weightedResidualApply root background =
  L1.applyKernel Contraction.gaugeRows
    (Weight.weightedSelectedBackgroundResidual root background)

weightedResidualOneStepL1Contraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root vector →
  L1.vectorL1 Contraction.gaugeRows
    (weightedResidualApply root background vector)
  ≤ (+ 1 / 6) * L1.vectorL1 Contraction.gaugeRows vector
weightedResidualOneStepL1Contraction background radius root vector =
  L1.applyKernelL1Bound Contraction.gaugeRows
    (Weight.weightedSelectedBackgroundResidual root background)
    vector (+ 1 / 6) (ℚP.nonNegative⁻¹ (+ 1 / 6))
    (selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction
      background radius root)

weightedResidualPowerApply :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  Nat → GaugeVector → GaugeVector
weightedResidualPowerApply root background zero vector = vector
weightedResidualPowerApply root background (suc exponent) vector =
  weightedResidualApply root background
    (weightedResidualPowerApply root background exponent vector)

powOneSixth : Nat → ℚ
powOneSixth zero = 1ℚ
powOneSixth (suc exponent) = (+ 1 / 6) * powOneSixth exponent

selectedBackgroundWeightedResidualPowerL1Decay :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root exponent vector →
  L1.vectorL1 Contraction.gaugeRows
    (weightedResidualPowerApply root background exponent vector)
  ≤ powOneSixth exponent * L1.vectorL1 Contraction.gaugeRows vector
selectedBackgroundWeightedResidualPowerL1Decay
    background radius root zero vector =
  subst
    (λ upper → L1.vectorL1 Contraction.gaugeRows vector ≤ upper)
    (sym
      (ℚRing.solve-∀ (L1.vectorL1 Contraction.gaugeRows vector) :
        1ℚ * L1.vectorL1 Contraction.gaugeRows vector
        ≡ L1.vectorL1 Contraction.gaugeRows vector))
    ℚP.≤-refl
selectedBackgroundWeightedResidualPowerL1Decay
    background radius root (suc exponent) vector =
  let
    previous = weightedResidualPowerApply root background exponent vector
    previousNorm = L1.vectorL1 Contraction.gaugeRows previous
    sourceNorm = L1.vectorL1 Contraction.gaugeRows vector
    qn = powOneSixth exponent

    oneStep = weightedResidualOneStepL1Contraction
      background radius root previous

    induction = selectedBackgroundWeightedResidualPowerL1Decay
      background radius root exponent vector

    scaled = Norm.scaleNonnegative (+ 1 / 6)
      (ℚP.nonNegative⁻¹ (+ 1 / 6)) induction

    reassociate :
      (+ 1 / 6) * (qn * sourceNorm)
      ≡ powOneSixth (suc exponent) * sourceNorm
    reassociate = ℚRing.solve-∀ qn sourceNorm
  in
  ℚP.≤-trans oneStep
    (subst
      (λ upper → (+ 1 / 6) * previousNorm ≤ upper)
      reassociate scaled)

selectedBackgroundWeightedTwoSidedContractionLevel : ProofLevel
selectedBackgroundWeightedTwoSidedContractionLevel = machineChecked

selectedBackgroundWeightedResidualPowerDecayLevel : ProofLevel
selectedBackgroundWeightedResidualPowerDecayLevel = machineChecked
