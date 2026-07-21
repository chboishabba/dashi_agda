module DASHI.Physics.Closure.NSCompactGammaExactMathematicalCutset where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
open import DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay public
open import DASHI.Physics.Closure.NSCompactGammaGammaNearTailCompletion public
open import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion public
open import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate public
open import DASHI.Physics.Closure.NSCompactGammaOfficialDataObstruction public
open import DASHI.Physics.Closure.NSCompactGammaOfficialCoverageCompletion public
open import DASHI.Physics.Closure.NSCompactGammaAbstractAdmissibilityObstruction public
open import DASHI.Physics.Closure.NSCompactGammaStandardAnalysisCompletion public
import DASHI.Physics.Closure.NSCompactGammaNearTriadRouteDecision as Absorption
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Galerkin
import DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas as Frontier

------------------------------------------------------------------------
-- One fail-closed owner for the exact mathematical cutset listed in the
-- accompanying review.  The signed cubic near-gain route is diagnostic only;
-- the official owner consumes dissipative absorption instead.
------------------------------------------------------------------------

record ExactCompactGammaMathematicalCutset
    {i t ℓState ℓProp : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (Official : OfficialInitialDataSetting i)
    (Time : Set t)
    (galerkinSetting : Galerkin.ConcreteGalerkinSetting ℓState ℓProp)
    : Set (lsuc (i ⊔ t ⊔ ℓState ⊔ ℓProp)) where
  field
    multiplicativeOrder : OrderedSemiringExtension A
    reflexiveOrder : ReflexiveOrderExtension A

    -- A1: the selected implementation route is the concrete adjacent-shell
    -- recurrence and its two-sided geometric assembly.
    shellDynamics : FourierShellDynamics A multiplicativeOrder
    twoSidedShellDecay :
      TwoSidedGeometricShellDecay
        A multiplicativeOrder reflexiveOrder shellDynamics

    -- B: the viable near-triad route is dissipative absorption, together with
    -- an explicit positive non-cubic source for the weighted rate.
    gammaRoute : Absorption.AbsorbedGammaRoute A Index

    -- C/D: the actual normalized Fourier low/high constants must fit the exact
    -- one-eighth budgets.  The arithmetic certificate alone is not sufficient.
    radiusEightAnalyticBounds : RadiusEightAnalyticBounds

    parameterNumerals : CanonicalParameterNumerals {i} A
    parameterInequalities :
      CanonicalParameterInequalities A Index parameterNumerals

    -- E: a proof-side route is required for the official completion owner.
    -- Obstructions remain exported as diagnostics, but cannot inhabit this
    -- field and therefore cannot be promoted to a global regularity result.
    officialCoverage : OfficialCoverageProof Official

    realIntegration : ConcreteRealIntegrationCompletion A Time

    galerkinLimit :
      Galerkin.ConcreteAubinLionsNonlinearLimitCertificate galerkinSetting

    offPacket : OffPacketAnalyticCompletion A Time

open ExactCompactGammaMathematicalCutset public

exactShellDecayEndpoint :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q j τ →
  _≤_ A
    (weightedFiveHalvesShell (shellDynamics C) j
      (selectedState (shellDynamics C) q τ))
    (_+_ A
      (decayCoefficient (twoSidedShellDecay C) q j)
      (compactGammaEnvelope (twoSidedShellDecay C) q τ))
exactShellDecayEndpoint C =
  iteratedTwoSidedFiveHalvesDecay (twoSidedShellDecay C)

exactAbsorbedGammaEndpoint :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (_+_ A
      (Absorption.gammaPotentialDerivative
        (Absorption.absorption (gammaRoute C)) q τ)
      (Absorption.weightedFiveHalvesRate
        (Absorption.absorption (gammaRoute C)) q τ))
    (_+_ A
      (_+_ A
        (Absorption.gammaDissipation
          (Absorption.absorption (gammaRoute C)) q τ)
        (Absorption.gammaForcing
          (Absorption.absorption (gammaRoute C)) q τ))
      (Absorption.residualEnvelope
        (Absorption.absorption (gammaRoute C)) q τ))
exactAbsorbedGammaEndpoint C =
  Absorption.absorbedGammaRouteDifferentialInequality (gammaRoute C)

exactBaseWeightedCoefficientProducesRate :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (Absorption._·_ (gammaRoute C)
      (Absorption.baseWeightedCoefficient (gammaRoute C))
      (Absorption.weightedFiveHalvesRate
        (Absorption.absorption (gammaRoute C)) q τ))
    (Absorption.positiveDissipativeTerm (gammaRoute C) q τ)
exactBaseWeightedCoefficientProducesRate C =
  Absorption.baseWeightedCoefficientProducesRateExact (gammaRoute C)

exactRadiusEightLowTailFits :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  normalizedLowTailAtEight (radiusEightAnalyticBounds C)
    ≤ᴺ epsilonLowAtEight
exactRadiusEightLowTailFits C =
  low-fits-certified-budget (radiusEightAnalyticBounds C)

exactRadiusEightHighTailFits :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  normalizedHighTailAtEight (radiusEightAnalyticBounds C)
    ≤ᴺ epsilonHighAtEight
exactRadiusEightHighTailFits C =
  high-fits-certified-budget (radiusEightAnalyticBounds C)

exactCanonicalTupleFeasible :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  Frontier.SharedParameterFeasibility
    A Index (canonicalSevenParameterTuple (parameterNumerals C))
exactCanonicalTupleFeasible C =
  canonicalTupleFeasible (parameterNumerals C) (parameterInequalities C)

-- Repository status remains fail-closed: defining the exact owner is not an
-- inhabitant for the official periodic three-dimensional Navier--Stokes model.
exactAnalyticCutsetInhabitedInOfficialCarrier : Bool
exactAnalyticCutsetInhabitedInOfficialCarrier = false

unconditionalPeriodicGlobalRegularityDerived : Bool
unconditionalPeriodicGlobalRegularityDerived = false
