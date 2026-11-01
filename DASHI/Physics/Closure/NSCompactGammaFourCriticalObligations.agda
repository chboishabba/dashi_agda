module DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaInequalityExpenditureProducer

------------------------------------------------------------------------
-- The four remaining high-alpha mathematical obligations.
--
-- This owner does not turn their statements into conclusions by naming them.
-- It fixes the quantifiers, shared constants, uniformity requirements, and the
-- exact alternatives required for official-data coverage.  The composition
-- theorems below ensure that no separate parameter choices or restricted-data
-- theorem can be promoted to the final Navier--Stokes claim.
------------------------------------------------------------------------

record UniformFiveHalvesShellEnvelope
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Shell Cutoff Time State : Set i

    selectedState : Index → Time → State
    targetShell : Index → Shell
    cutoff : Index → Cutoff

    weightedShellL2 : Shell → State → Scalar A
    compactGammaEnvelope : Index → Time → Scalar A
    decayCoefficient : Shell → Shell → Scalar A
    coefficientSum : Shell → Scalar A
    uniformCoefficientBound : Scalar A

    sigmaPositive : Set i
    constantPositive : Set i

    -- 2^(5j/2) ||P_j u||_2 <= C 2^(-sigma |j-K|) E_Gamma.
    pointwiseFiveHalvesDecay : ∀ q j τ →
      _≤_ A
        (weightedShellL2 j (selectedState q τ))
        (_+_ A
          (decayCoefficient j (targetShell q))
          (compactGammaEnvelope q τ))

    -- The coefficient family is summable uniformly in the target shell and
    -- independent of the Galerkin cutoff.
    geometricCoefficientSummable : ∀ K →
      _≤_ A (coefficientSum K) uniformCoefficientBound

    cutoffUniform : ∀ q j τ → Set i

    -- The genuine shell-summation theorem produced from the preceding pointwise
    -- inequality and uniform coefficient bound.
    weightedShellSum : Index → Time → Scalar A
    summedFiveHalvesEnvelope : ∀ q τ →
      _≤_ A
        (weightedShellSum q τ)
        (compactGammaEnvelope q τ)

open UniformFiveHalvesShellEnvelope public

fiveHalvesEnvelopeUniformInCutoff :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (E : UniformFiveHalvesShellEnvelope A Index) →
  ∀ q j τ → Set i
fiveHalvesEnvelopeUniformInCutoff E = cutoffUniform E

record GammaNumeratorCoercivity
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i

    gammaPotentialDerivative : Index → Time → Scalar A
    gammaCoerciveRate : Index → Time → Scalar A
    gammaDissipationRate : Index → Time → Scalar A
    gammaForcingRate : Index → Time → Scalar A

    nearGain farTailLoss coerciveMargin weightedShellRate :
      Index → Time → Scalar A

    -- Explicit constants and signs are carried by one selected parameter set.
    nearGainConstant tailConstant coerciveConstant : Scalar A
    nearGainConstantPositive : Set i
    tailConstantNonnegative : Set i
    coerciveConstantPositive : Set i

    -- The far contribution is small enough to be absorbed by the near gain.
    farTailAbsorbed : ∀ q τ →
      _≤_ A (farTailLoss q τ) (nearGain q τ)

    -- The surviving margin dominates the five-halves shell rate.
    marginDominatesWeightedShell : ∀ q τ →
      _≤_ A (weightedShellRate q τ) (coerciveMargin q τ)

    coerciveMarginBelowGammaRate : ∀ q τ →
      _≤_ A (coerciveMargin q τ) (gammaCoerciveRate q τ)

    -- Natural Route-B differential law after near/far decomposition.
    gammaDifferentialInequality : ∀ q τ →
      _≤_ A
        (_+_ A
          (gammaPotentialDerivative q τ)
          (gammaCoerciveRate q τ))
        (_+_ A
          (gammaDissipationRate q τ)
          (gammaForcingRate q τ))

open GammaNumeratorCoercivity public

gammaCoerciveRateDominatesFiveHalvesShell :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (G : GammaNumeratorCoercivity A Index) → ∀ q τ →
  _≤_ A (weightedShellRate G q τ) (gammaCoerciveRate G q τ)
gammaCoerciveRateDominatesFiveHalvesShell {A = A} G q τ =
  ≤-trans A
    (marginDominatesWeightedShell G q τ)
    (coerciveMarginBelowGammaRate G q τ)

record SharedCompactGammaParameters
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    radius gammaFloor energyFloor offPacketCeiling : Scalar A
    alphaEnergy alphaGamma alphaOffPacket : Scalar A

    radiusAdmissible : Set i
    gammaFloorPositive : Set i
    energyFloorPositive : Set i
    offPacketCeilingPositive : Set i
    alphaEnergyPositive : Set i
    alphaGammaPositive : Set i
    alphaOffPacketPositive : Set i

    -- Every estimate consumes this same seven-parameter tuple.
    tailAbsorptionAtSharedParameters : Index → Set i
    gammaInwardAtSharedParameters : Index → Set i
    packetEnergyPositiveAtSharedParameters : Index → Set i
    offPacketInwardAtSharedParameters : Index → Set i
    expenditureCoerciveAtSharedParameters : Index → Set i

open SharedCompactGammaParameters public

record SimultaneousLocalClosure
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (P : SharedCompactGammaParameters A Index) : Set (lsuc i) where
  field
    allFiveConditionsHold : ∀ q →
      Σ (tailAbsorptionAtSharedParameters P q) (λ _ →
      Σ (gammaInwardAtSharedParameters P q) (λ _ →
      Σ (packetEnergyPositiveAtSharedParameters P q) (λ _ →
      Σ (offPacketInwardAtSharedParameters P q) (λ _ →
          expenditureCoerciveAtSharedParameters P q))))

open SimultaneousLocalClosure public

sharedParametersCloseAllLocalConditions :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {P : SharedCompactGammaParameters A Index} →
  SimultaneousLocalClosure A Index P → ∀ q →
  Σ (tailAbsorptionAtSharedParameters P q) (λ _ →
  Σ (gammaInwardAtSharedParameters P q) (λ _ →
  Σ (packetEnergyPositiveAtSharedParameters P q) (λ _ →
  Σ (offPacketInwardAtSharedParameters P q) (λ _ →
      expenditureCoerciveAtSharedParameters P q))))
sharedParametersCloseAllLocalConditions C = allFiveConditionsHold C

------------------------------------------------------------------------
-- Official initial-data coverage.
------------------------------------------------------------------------

record OfficialInitialDataSetting (i : Level) : Set (lsuc i) where
  field
    InitialDatum Solution Time : Set i
    SmoothDivergenceFreeFiniteEnergy : InitialDatum → Set i
    SolvesFrom : InitialDatum → Solution → Set i
    CompactGammaAdmissible : Solution → Time → Set i
    BeforeAnySingularity : Solution → Time → Set i
    UniversalContinuationMechanism : InitialDatum → Set i

open OfficialInitialDataSetting public

record AllDataInitiallyAdmissible
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initialTime : Time S
    everyOfficialDatumStartsAdmissible : ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      CompactGammaAdmissible S u initialTime

open AllDataInitiallyAdmissible public

record EverySolutionEntersBeforeSingularity
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    entryTime : InitialDatum S → Solution S → Time S
    everyOfficialSolutionEnters : ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      Σ (BeforeAnySingularity S u (entryTime u₀ u)) (λ _ →
          CompactGammaAdmissible S u (entryTime u₀ u))

open EverySolutionEntersBeforeSingularity public

record UniversalReplacementMechanism
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    allOfficialDataHaveUniversalMechanism : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      UniversalContinuationMechanism S u₀

open UniversalReplacementMechanism public

OfficialDataCoverage :
  ∀ {i} → OfficialInitialDataSetting i → Set (lsuc i)
OfficialDataCoverage S =
  AllDataInitiallyAdmissible S
  ⊎ (EverySolutionEntersBeforeSingularity S
  ⊎ UniversalReplacementMechanism S)

record FullOfficialClassClosure
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    coverage : OfficialDataCoverage S
    GlobalSmoothSolution : InitialDatum S → Set i

    initialAdmissibilityCloses :
      AllDataInitiallyAdmissible S → ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      GlobalSmoothSolution u₀

    entryBeforeSingularityCloses :
      EverySolutionEntersBeforeSingularity S → ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      GlobalSmoothSolution u₀

    universalMechanismCloses :
      UniversalReplacementMechanism S → ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      GlobalSmoothSolution u₀

open FullOfficialClassClosure public

officialDataCoverageYieldsGlobalSmoothness :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : FullOfficialClassClosure S) → ∀ u₀ →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  GlobalSmoothSolution C u₀
officialDataCoverageYieldsGlobalSmoothness C u₀ official with coverage C
... | inj₁ starts = initialAdmissibilityCloses C starts u₀ official
... | inj₂ (inj₁ enters) = entryBeforeSingularityCloses C enters u₀ official
... | inj₂ (inj₂ universal) = universalMechanismCloses C universal u₀ official

------------------------------------------------------------------------
-- One fail-closed package: all four obligations must coexist.
------------------------------------------------------------------------

record FourCriticalObligationsClosed
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    fiveHalvesEnvelope : UniformFiveHalvesShellEnvelope A Index
    gammaCoercivity : GammaNumeratorCoercivity A Index
    sharedParameters : SharedCompactGammaParameters A Index
    simultaneousLocalClosure :
      SimultaneousLocalClosure A Index sharedParameters
    officialClassClosure : FullOfficialClassClosure S

open FourCriticalObligationsClosed public
