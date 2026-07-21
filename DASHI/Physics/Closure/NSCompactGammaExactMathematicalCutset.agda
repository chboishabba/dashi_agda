module DASHI.Physics.Closure.NSCompactGammaExactMathematicalCutset where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
open import DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay public
open import DASHI.Physics.Closure.NSCompactGammaGammaNearTailCompletion public
open import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion public
open import DASHI.Physics.Closure.NSCompactGammaOfficialDataObstruction public
open import DASHI.Physics.Closure.NSCompactGammaStandardAnalysisCompletion public
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Galerkin
import DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas as Frontier

------------------------------------------------------------------------
-- One fail-closed owner for the exact mathematical cutset listed in the
-- accompanying review.  Structural assembly is explicit, but the record can be
-- inhabited only after the selected periodic Fourier carrier supplies the
-- genuinely analytic SD/GM/parameter/coverage/integration/Galerkin/off-packet
-- and Bernstein witnesses.
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

    shellDynamics : FourierShellDynamics A multiplicativeOrder
    twoSidedShellDecay :
      TwoSidedGeometricShellDecay
        A multiplicativeOrder reflexiveOrder shellDynamics

    gammaNearTail : GammaNearTailDynamics A Index

    parameterNumerals : CanonicalParameterNumerals {i} A
    parameterInequalities :
      CanonicalParameterInequalities A Index parameterNumerals

    officialCoverage : OfficialCoverageResolution Official

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

exactGammaCoerciveEndpoint :
  ∀ {i t ℓState ℓProp} {A : AbsorptionArithmetic}
    {Index : Set i} {Official : OfficialInitialDataSetting i}
    {Time : Set t}
    {G : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : ExactCompactGammaMathematicalCutset A Index Official Time G) →
  ∀ q τ →
  _≤_ A
    (_+_ A
      (gammaPotentialDerivative (gammaNearTail C) q τ)
      (survivingMargin (gammaNearTail C) q τ))
    (_+_ A
      (gammaDissipation (gammaNearTail C) q τ)
      (gammaForcing (gammaNearTail C) q τ))
exactGammaCoerciveEndpoint C =
  gammaCoerciveDifferentialInequality (gammaNearTail C)

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
