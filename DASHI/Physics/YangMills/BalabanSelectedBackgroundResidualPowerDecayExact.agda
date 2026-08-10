module DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- The previous modules prove both row and column absolute mass of the literal
-- residual
--
--   R_A = G_0 E_A
--
-- below q=1/10.  This module converts the column bound into an actual vector
-- contraction on the 768-coordinate multiplier carrier and iterates it:
--
--   ||R_A^n v||_1 <= (1/10)^n ||v||_1.
--
-- Thus the finite Neumann residual powers vanish geometrically at a rate far
-- stronger than the older generic half-contraction target.  This is concrete
-- convergence mathematics on the physical selected residual, not a receipt
-- for an assumed inverse.  Constructing the infinite inverse still requires a
-- complete scalar/vector carrier or a finite-dimensional exact-inverse theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact as TwoSided
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeVector : Set
GaugeVector = Contraction.GaugeRow → ℚ

residualApply : Physical.RationalSU2Background4 → GaugeVector → GaugeVector
residualApply background =
  L1.applyKernel Contraction.gaugeRows
    (Contraction.flatGreenTimesPerturbationKernel background)

residualPowerApply :
  Physical.RationalSU2Background4 → Nat → GaugeVector → GaugeVector
residualPowerApply background zero vector = vector
residualPowerApply background (suc exponent) vector =
  residualApply background (residualPowerApply background exponent vector)

powRational : ℚ → Nat → ℚ
powRational q zero = 1ℚ
powRational q (suc exponent) = q * powRational q exponent

oneTenthNonnegative : 0ℚ ≤ Contraction.oneTenth
oneTenthNonnegative = ℚP.nonNegative⁻¹ Contraction.oneTenth

residualOneStepL1Contraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ vector →
  L1.vectorL1 Contraction.gaugeRows (residualApply background vector)
  ≤ Contraction.oneTenth * L1.vectorL1 Contraction.gaugeRows vector
residualOneStepL1Contraction background radius vector =
  L1.applyKernelL1Bound
    Contraction.gaugeRows
    (Contraction.flatGreenTimesPerturbationKernel background)
    vector Contraction.oneTenth oneTenthNonnegative
    (TwoSided.selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction
      background radius)

selectedBackgroundResidualPowerL1Decay :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ exponent vector →
  L1.vectorL1 Contraction.gaugeRows
    (residualPowerApply background exponent vector)
  ≤ powRational Contraction.oneTenth exponent
      * L1.vectorL1 Contraction.gaugeRows vector
selectedBackgroundResidualPowerL1Decay background radius zero vector =
  subst
    (λ upper →
      L1.vectorL1 Contraction.gaugeRows vector ≤ upper)
    (sym
      (ℚRing.solve-∀
        (L1.vectorL1 Contraction.gaugeRows vector) :
        1ℚ * L1.vectorL1 Contraction.gaugeRows vector
        ≡ L1.vectorL1 Contraction.gaugeRows vector))
    ℚP.≤-refl
selectedBackgroundResidualPowerL1Decay
    background radius (suc exponent) vector =
  let
    previous = residualPowerApply background exponent vector
    previousNorm = L1.vectorL1 Contraction.gaugeRows previous
    sourceNorm = L1.vectorL1 Contraction.gaugeRows vector
    qn = powRational Contraction.oneTenth exponent

    oneStep :
      L1.vectorL1 Contraction.gaugeRows (residualApply background previous)
      ≤ Contraction.oneTenth * previousNorm
    oneStep = residualOneStepL1Contraction background radius previous

    induction : previousNorm ≤ qn * sourceNorm
    induction = selectedBackgroundResidualPowerL1Decay
      background radius exponent vector

    scaled :
      Contraction.oneTenth * previousNorm
      ≤ Contraction.oneTenth * (qn * sourceNorm)
    scaled = Norm.scaleNonnegative Contraction.oneTenth
      oneTenthNonnegative induction

    reassociate :
      Contraction.oneTenth * (qn * sourceNorm)
      ≡ powRational Contraction.oneTenth (suc exponent) * sourceNorm
    reassociate = ℚRing.solve-∀
      Contraction.oneTenth qn sourceNorm
  in
  ℚP.≤-trans oneStep
    (subst
      (λ upper → Contraction.oneTenth * previousNorm ≤ upper)
      reassociate scaled)

selectedBackgroundResidualPowerGeometricRateLevel : ProofLevel
selectedBackgroundResidualPowerGeometricRateLevel = machineChecked

selectedBackgroundExactInfiniteGreenStillRequiredLevel : ProofLevel
selectedBackgroundExactInfiniteGreenStillRequiredLevel = conditional
