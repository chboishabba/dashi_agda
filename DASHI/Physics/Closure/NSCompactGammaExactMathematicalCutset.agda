module DASHI.Physics.Closure.NSCompactGammaExactMathematicalCutset where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
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
import DASHI.Physics.Closure.NSCompactGammaFiveHalvesRouteDecision as FiveHalves
import DASHI.Physics.Closure.NSCompactGammaNearTriadRouteDecision as Absorption
import DASHI.Physics.Closure.NSCompactGammaNearTriadAbsorptionReduction as NearReduction
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction as RadiusEight
import DASHI.Physics.Closure.NSCompactGammaCanonicalParameterBridge as ParameterBridge
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
    -- A1: the selected implementation route is the adjacent-shell recurrence
    -- and its two-sided geometric assembly.  The direct weighted-sum route is
    -- retained separately as an alternative theorem owner.
    fiveHalvesRoute : FiveHalves.AdjacentRecurrenceFiveHalvesControl A

    -- B: literal Fourier expansion, paraproduct split, three Young estimates,
    -- Route-B balance and the positive non-cubic base rate are one owner.
    nearTriadReduction : NearReduction.ConcreteAbsorbedGammaRoute A Index

    -- C/D: one coherent radius-eight Fourier owner supplies the multiplier,
    -- commutator, Sobolev, geometric-series, paraproduct and normalized dyadic
    -- bounds.  The finite arithmetic certificate is obtained from this owner.
    radiusEightFourierReduction :
      RadiusEight.RadiusEightFourierReduction A Index

    -- The tuple's semantic real-carrier comparisons are derived from the exact
    -- dyadic certificate and the radius-eight Fourier owner, rather than being
    -- accepted as a disconnected `CanonicalParameterInequalities` witness.
    parameterNumerals : CanonicalParameterNumerals {i} A
    parameterBridge :
      ParameterBridge.CanonicalParameterSemanticBridge
        A Index parameterNumerals

    -- E: a proof-side route is required for the official completion owner.
    -- Obstructions remain exported as diagnostics, but cannot inhabit this
    -- field and therefore cannot be promoted to a global regularity result.
    officialCoverage : OfficialCoverageProof Official

    realIntegration : ConcreteRealIntegrationCompletion A Time

    galerkinLimit :
      Galerkin.ConcreteAubinLionsNonlinearLimitCertificate galerkinSetting

    offPacket : OffPacketAnalyticCompletion A Time

open ExactCompactGammaMathematicalCutset public

exactGammaRoute :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  ExactCompactGammaMathematicalCutset A Index Official Time G →
  Absorption.AbsorbedGammaRoute A Index
exactGammaRoute C =
  NearReduction.concreteAbsorbedGammaRoute (nearTriadReduction C)

exactShellDecayEndpoint :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q j τ →
  _≤_ A
    (weightedFiveHalvesShell
      (FiveHalves.dynamics (fiveHalvesRoute C)) j
      (selectedState
        (FiveHalves.dynamics (fiveHalvesRoute C)) q τ))
    (_+_ A
      (decayCoefficient
        (FiveHalves.decay (fiveHalvesRoute C)) q j)
      (compactGammaEnvelope
        (FiveHalves.decay (fiveHalvesRoute C)) q τ))
exactShellDecayEndpoint C =
  FiveHalves.periodicTwoSidedShellDecay (fiveHalvesRoute C)

exactFiveHalvesSumEndpoint :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (weightedShellSum
      (FiveHalves.decay (fiveHalvesRoute C)) q τ)
    (compactGammaEnvelope
      (FiveHalves.decay (fiveHalvesRoute C)) q τ)
exactFiveHalvesSumEndpoint C =
  FiveHalves.periodicAdjacentRouteControlsFiveHalvesSum
    (fiveHalvesRoute C)

exactNearTriadAbsorption :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (NearReduction.nearTriadMagnitude
      (NearReduction.paraproduct (nearTriadReduction C)) q τ)
    (_+_ A
      (NearReduction.deltaDissipation
        (NearReduction.paraproduct (nearTriadReduction C)) q τ)
      (NearReduction.residualEnvelope
        (NearReduction.paraproduct (nearTriadReduction C)) q τ))
exactNearTriadAbsorption C =
  NearReduction.youngAbsorbsNearTriad
    (NearReduction.paraproduct (nearTriadReduction C))

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
        (Absorption.absorption (exactGammaRoute C)) q τ)
      (Absorption.weightedFiveHalvesRate
        (Absorption.absorption (exactGammaRoute C)) q τ))
    (_+_ A
      (_+_ A
        (Absorption.gammaDissipation
          (Absorption.absorption (exactGammaRoute C)) q τ)
        (Absorption.gammaForcing
          (Absorption.absorption (exactGammaRoute C)) q τ))
      (Absorption.residualEnvelope
        (Absorption.absorption (exactGammaRoute C)) q τ))
exactAbsorbedGammaEndpoint C =
  Absorption.absorbedGammaRouteDifferentialInequality (exactGammaRoute C)

exactBaseWeightedCoefficientProducesRate :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (Absorption._·_ (exactGammaRoute C)
      (Absorption.baseWeightedCoefficient (exactGammaRoute C))
      (Absorption.weightedFiveHalvesRate
        (Absorption.absorption (exactGammaRoute C)) q τ))
    (Absorption.positiveDissipativeTerm (exactGammaRoute C) q τ)
exactBaseWeightedCoefficientProducesRate C =
  Absorption.baseWeightedCoefficientProducesRateExact (exactGammaRoute C)

exactBaseWeightedCoefficientDyadicMeaning :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  Absorption.baseWeightedCoefficient (exactGammaRoute C) ≡
  Absorption.interpretDyadic (exactGammaRoute C) baseWeightedCoefficient
exactBaseWeightedCoefficientDyadicMeaning C =
  Absorption.baseWeightedCoefficientHasCertifiedDyadicMeaning
    (exactGammaRoute C)

exactPeriodicFarLowCommutatorBound :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (RadiusEight.farLowTail (radiusEightFourierReduction C) q τ)
    (RadiusEight.farLowDisplayedBudget
      (radiusEightFourierReduction C) q τ)
exactPeriodicFarLowCommutatorBound C =
  RadiusEight.periodicFarLowCommutatorBound
    (radiusEightFourierReduction C)

exactPeriodicFarHighTailBound :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (RadiusEight.farHighTail (radiusEightFourierReduction C) q τ)
    (RadiusEight.farHighDisplayedBudget
      (radiusEightFourierReduction C) q τ)
exactPeriodicFarHighTailBound C =
  RadiusEight.periodicFarHighTailBound
    (radiusEightFourierReduction C)

exactRadiusEightLowTailFits :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  RadiusEight.normalizedFarLowAtEight (radiusEightFourierReduction C)
    ≤ᴺ epsilonLowAtEight
exactRadiusEightLowTailFits C =
  RadiusEight.normalizedFarLowAtEightFits
    (radiusEightFourierReduction C)

exactRadiusEightHighTailFits :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  RadiusEight.normalizedFarHighAtEight (radiusEightFourierReduction C)
    ≤ᴺ epsilonHighAtEight
exactRadiusEightHighTailFits C =
  RadiusEight.normalizedFarHighAtEightFits
    (radiusEightFourierReduction C)

exactRadiusEightAnalyticBounds :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  ExactCompactGammaMathematicalCutset A Index Official Time G →
  RadiusEightAnalyticBounds
exactRadiusEightAnalyticBounds C =
  RadiusEight.periodicRadiusEightAnalyticBounds
    (radiusEightFourierReduction C)

exactParameterInequalities :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  CanonicalParameterInequalities A Index (parameterNumerals C)
exactParameterInequalities C =
  ParameterBridge.canonicalParameterInequalitiesFromBridge
    (parameterBridge C)
    (exactRadiusEightAnalyticBounds C)

exactCanonicalTupleFeasible :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  Frontier.SharedParameterFeasibility
    A Index (canonicalSevenParameterTuple (parameterNumerals C))
exactCanonicalTupleFeasible C =
  canonicalTupleFeasible
    (parameterNumerals C)
    (exactParameterInequalities C)

-- Repository status remains fail-closed: defining the exact owner is not an
-- inhabitant for the official periodic three-dimensional Navier--Stokes model.
exactAnalyticCutsetInhabitedInOfficialCarrier : Bool
exactAnalyticCutsetInhabitedInOfficialCarrier = false

unconditionalPeriodicGlobalRegularityDerived : Bool
unconditionalPeriodicGlobalRegularityDerived = false
