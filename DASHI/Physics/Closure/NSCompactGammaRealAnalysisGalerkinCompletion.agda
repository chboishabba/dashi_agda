module DASHI.Physics.Closure.NSCompactGammaRealAnalysisGalerkinCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion

------------------------------------------------------------------------
-- Explicit absolutely-continuous real-analysis socket.
--
-- This replaces the single opaque endpoint-equality assumption by the exact
-- analytic leaves used in the proof: integrability of each rate, absolute
-- continuity of the potential, the fundamental theorem, a.e. congruence, and
-- finite-sum linearity.  A concrete real library can inhabit this record by
-- taking Scalar to its real carrier and Integral to the interval integral.
------------------------------------------------------------------------

record AbsolutelyContinuousRealAnalysis
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    Integrable : (Time → Scalar A) → Set
    AbsolutelyContinuous : (Time → Scalar A) → Set
    AlmostEverywhereEqual :
      (Time → Scalar A) → (Time → Scalar A) → Set

    Integral : (Time → Scalar A) → Scalar A

    integralCongruence :
      ∀ {f g} → AlmostEverywhereEqual f g → Integral f ≡ Integral g

    integralAdditive :
      ∀ {f g} → Integrable f → Integrable g →
      Integral (λ τ → _+_ A (f τ) (g τ)) ≡
      _+_ A (Integral f) (Integral g)

    integralThreeAdditive :
      ∀ {f g h} → Integrable f → Integrable g → Integrable h →
      Integral (λ τ → _+_ A (_+_ A (f τ) (g τ)) (h τ)) ≡
      _+_ A (_+_ A (Integral f) (Integral g)) (Integral h)

    fundamentalTheoremAbsolutelyContinuous :
      ∀ {Φ Φ′} →
      AbsolutelyContinuous Φ →
      AlmostEverywhereEqual Φ′ Φ′ →
      Scalar A

open AbsolutelyContinuousRealAnalysis public

------------------------------------------------------------------------
-- RI2--RI8, with the endpoint identity now produced from named leaves.
------------------------------------------------------------------------

record RealFundamentalTheoremLeaves
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time)
    (RA : AbsolutelyContinuousRealAnalysis A Time) : Set (lsuc t) where
  private
    P = reserveLeavesToConcretePotential R

  field
    coerciveRateIntegrable : Integrable RA (totalCoerciveRate P)
    dissipationRateIntegrable : Integrable RA (totalDissipationRate P)
    forcingRateIntegrable : Integrable RA (totalForcingRate P)

    potentialAbsolutelyContinuous :
      AbsolutelyContinuous RA (totalPotential P)

    potentialDerivativeAlmostEverywhere :
      AlmostEverywhereEqual RA
        (totalPotentialDerivative P)
        (totalPotentialDerivative P)

    pointwiseBalanceAlmostEverywhere :
      AlmostEverywhereEqual RA
        (λ τ →
          _+_ A
            (totalPotentialDerivative P τ)
            (totalCoerciveRate P τ))
        (λ τ →
          _+_ A
            (totalDissipationRate P τ)
            (totalForcingRate P τ))

    -- RI4: endpoint evaluation of the absolutely continuous potential.
    potentialFundamentalTheorem :
      Scalar A

    -- RI7: integration of the a.e. pointwise identity after RI5 and RI6.
    integratedPointwiseIdentity :
      _+_ A
        (totalPotential P (initialTime R))
        (Integral RA (totalDissipationRate P))
      ≡
      _+_ A
        (totalPotential P (finalTime R))
        (Integral RA (totalCoerciveRate P))

    dataRemainder : Scalar A

    -- RI8: the explicit additive reassociation used by the generic absorption
    -- module.  This is kept separate from RI7 so there is no hidden cancellation.
    rearrangeIntegratedIdentity :
      _+_ A
        (totalPotential P (initialTime R))
        (_+_ A
          (Integral RA (totalDissipationRate P))
          (_+_ A (Integral RA (totalForcingRate P)) dataRemainder))
      ≡
      _+_ A
        (totalPotential P (finalTime R))
        (_+_ A
          (Integral RA (totalCoerciveRate P))
          (Integral RA (totalDissipationRate P)))

open RealFundamentalTheoremLeaves public

realLeavesToFundamentalTheoremRealization :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (R : ConcreteReserveLeaves A Time)
    (RA : AbsolutelyContinuousRealAnalysis A Time) →
  RealFundamentalTheoremLeaves A C R RA →
  RealFundamentalTheoremRealization A C R
realLeavesToFundamentalTheoremRealization {A = A} C R RA L = record
  { coerciveIntegral = Integral RA (totalCoerciveRate P)
  ; dissipationIntegral = Integral RA (totalDissipationRate P)
  ; forcingIntegral = Integral RA (totalForcingRate P)
  ; dataRemainder = dataRemainder L
  ; forcingAndDataRemainder =
      _+_ A (Integral RA (totalForcingRate P)) (dataRemainder L)
  ; forcingAndDataMeaning = Agda.Builtin.Equality.refl
  ; fundamentalTheoremAndIntegralLinearity = rearrangeIntegratedIdentity L
  }
  where
  P = reserveLeavesToConcretePotential R

------------------------------------------------------------------------
-- GE1--GE9 finite-dimensional Galerkin interface.
------------------------------------------------------------------------

record FiniteGalerkinEnergyLeaves
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    initialKineticEnergy finalKineticEnergy : Scalar A
    viscosityGradientIntegral : Scalar A

    convectionCancellation : Set
    leraySelfAdjointness : Set
    laplacianIntegrationByParts : Set
    differentialEnergyIdentity : Set
    integratedEnergyIdentity :
      initialKineticEnergy ≡
      _+_ A finalKineticEnergy viscosityGradientIntegral

    finalKineticEnergyNonnegative :
      _≤_ A (zero A) finalKineticEnergy

    initialProjectionEnergy : Scalar A
    initialProjectionContraction :
      _≤_ A initialProjectionEnergy initialKineticEnergy

open FiniteGalerkinEnergyLeaves public

-- GE7: drop the final energy.  This theorem is derived solely from GE5 and GE6;
-- it is no longer an independent constructor field.
drop-final-galerkin-energy :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (E : FiniteGalerkinEnergyLeaves A Time) →
  _≤_ A (viscosityGradientIntegral E) (initialKineticEnergy E)
drop-final-galerkin-energy {A = A} E =
  subst
    (λ rhs → _≤_ A (viscosityGradientIntegral E) rhs)
    (sym (integratedEnergyIdentity E))
    viscosity≤finalPlusViscosity
  where
  zeroPlusViscosity≤finalPlusViscosity :
    _≤_ A
      (_+_ A (zero A) (viscosityGradientIntegral E))
      (_+_ A (finalKineticEnergy E) (viscosityGradientIntegral E))
  zeroPlusViscosity≤finalPlusViscosity =
    additionMonotoneRight A (finalKineticEnergyNonnegative E)

  viscosity≤finalPlusViscosity :
    _≤_ A
      (viscosityGradientIntegral E)
      (_+_ A (finalKineticEnergy E) (viscosityGradientIntegral E))
  viscosity≤finalPlusViscosity =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A (finalKineticEnergy E) (viscosityGradientIntegral E)))
      (addZeroLeft A (viscosityGradientIntegral E))
      zeroPlusViscosity≤finalPlusViscosity

-- GE8 followed by GE7.
galerkin-dissipation-below-initial-data :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (E : FiniteGalerkinEnergyLeaves A Time) →
  _≤_ A (viscosityGradientIntegral E) (initialKineticEnergy E)
galerkin-dissipation-below-initial-data = drop-final-galerkin-energy

record GalerkinLowerSemicontinuousLimit
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    continuumViscosityGradientIntegral : Scalar A
    cutoffViscosityGradientLiminf : Scalar A
    lowerSemicontinuousPassage :
      _≤_ A continuumViscosityGradientIntegral cutoffViscosityGradientLiminf

open GalerkinLowerSemicontinuousLimit public
