module DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations

------------------------------------------------------------------------
-- Frontier attack owner.
--
-- This file proves the algebraic and logical reductions surrounding the four
-- remaining critical obligations.  The genuinely harmonic-analytic estimates
-- remain visible as named leaves, alongside precise finite counterexample forms.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Five-halves shell envelope.
------------------------------------------------------------------------

record TwoSidedShellDecayAttack
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Shell Time State Cutoff : Set i
    selectedState : Index → Time → State
    targetShell : Index → Shell
    cutoff : Index → Cutoff

    weightedFiveHalvesShell : Shell → State → Scalar A
    compactGammaEnvelope : Index → Time → Scalar A
    geometricCoefficient : Shell → Shell → Scalar A

    targetShellBound : ∀ q τ →
      _≤_ A
        (weightedFiveHalvesShell (targetShell q) (selectedState q τ))
        (compactGammaEnvelope q τ)

    -- Exact analytic leaf: iterate adjacent-shell decay in both directions.
    iteratedTwoSidedDecay : ∀ q j τ →
      _≤_ A
        (weightedFiveHalvesShell j (selectedState q τ))
        (_+_ A
          (geometricCoefficient j (targetShell q))
          (compactGammaEnvelope q τ))

    coefficientSum uniformCoefficientBound : Shell → Scalar A
    geometricFamilySummable : ∀ K →
      _≤_ A (coefficientSum K) (uniformCoefficientBound K)

    weightedShellSum : Index → Time → Scalar A
    sumPointwiseDecay :
      (∀ q j τ →
        _≤_ A
          (weightedFiveHalvesShell j (selectedState q τ))
          (_+_ A
            (geometricCoefficient j (targetShell q))
            (compactGammaEnvelope q τ))) →
      ∀ q τ →
      _≤_ A (weightedShellSum q τ) (compactGammaEnvelope q τ)

    cutoffIndependence : ∀ q j τ → Set i

open TwoSidedShellDecayAttack public

five-halves-pointwise-from-two-sided-decay :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : TwoSidedShellDecayAttack A Index) → ∀ q j τ →
  _≤_ A
    (weightedFiveHalvesShell D j (selectedState D q τ))
    (_+_ A
      (geometricCoefficient D j (targetShell D q))
      (compactGammaEnvelope D q τ))
five-halves-pointwise-from-two-sided-decay D = iteratedTwoSidedDecay D

five-halves-summed-envelope-from-two-sided-decay :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : TwoSidedShellDecayAttack A Index) → ∀ q τ →
  _≤_ A (weightedShellSum D q τ) (compactGammaEnvelope D q τ)
five-halves-summed-envelope-from-two-sided-decay D =
  sumPointwiseDecay D (five-halves-pointwise-from-two-sided-decay D)

record FiveHalvesEnvelopeCounterexample
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (D : TwoSidedShellDecayAttack A Index) : Set (lsuc i) where
  field
    q : Index
    j : Shell D
    τ : Time D
    Violates : Scalar A → Scalar A → Set i
    witness :
      Violates
        (weightedFiveHalvesShell D j (selectedState D q τ))
        (_+_ A
          (geometricCoefficient D j (targetShell D q))
          (compactGammaEnvelope D q τ))

open FiveHalvesEnvelopeCounterexample public

------------------------------------------------------------------------
-- 2. Gamma near/tail coercivity.
------------------------------------------------------------------------

record RawGammaNearTailInequality
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i
    gammaPotentialDerivative gammaDissipation gammaForcing :
      Index → Time → Scalar A
    survivingMargin farTailPayment weightedFiveHalvesRate :
      Index → Time → Scalar A

    survivingMarginPositive : Set i
    weightedRateBelowMargin : ∀ q τ →
      _≤_ A (weightedFiveHalvesRate q τ) (survivingMargin q τ)

    -- Raw signed estimate with the identical tail payment on both sides.
    rawNearTailInequality : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A (gammaPotentialDerivative q τ) (survivingMargin q τ))
          (farTailPayment q τ))
        (_+_ A
          (_+_ A (gammaDissipation q τ) (gammaForcing q τ))
          (farTailPayment q τ))

open RawGammaNearTailInequality public

gamma-near-tail-cancellation :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (G : RawGammaNearTailInequality A Index) → ∀ q τ →
  _≤_ A
    (_+_ A (gammaPotentialDerivative G q τ) (survivingMargin G q τ))
    (_+_ A (gammaDissipation G q τ) (gammaForcing G q τ))
gamma-near-tail-cancellation {A = A} G q τ =
  additionCancelRight A (rawNearTailInequality G q τ)

gamma-surviving-margin-dominates-five-halves :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (G : RawGammaNearTailInequality A Index) → ∀ q τ →
  _≤_ A (weightedFiveHalvesRate G q τ) (survivingMargin G q τ)
gamma-surviving-margin-dominates-five-halves G = weightedRateBelowMargin G

record GammaCoercivityCounterexample
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (G : RawGammaNearTailInequality A Index) : Set (lsuc i) where
  field
    q : Index
    τ : Time G
    StrictlyExceeds : Scalar A → Scalar A → Set i
    tailDestroysMargin :
      StrictlyExceeds
        (farTailPayment G q τ)
        (survivingMargin G q τ)

open GammaCoercivityCounterexample public

------------------------------------------------------------------------
-- 3. One shared parameter tuple.
------------------------------------------------------------------------

record CompactGammaParameterTuple
    {i : Level}
    (A : AbsorptionArithmetic) : Set (lsuc i) where
  field
    radius gammaFloor energyFloor offPacketCeiling : Scalar A
    alphaEnergy alphaGamma alphaOffPacket : Scalar A

open CompactGammaParameterTuple public

record SharedParameterFeasibility
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (P : CompactGammaParameterTuple {i} A) : Set (lsuc i) where
  field
    radiusAdmissible gammaFloorPositive energyFloorPositive : Set i
    offPacketCeilingPositive : Set i
    alphaEnergyPositive alphaGammaPositive alphaOffPacketPositive : Set i

    tailAbsorption gammaInwardness packetPositivity : Index → Set i
    offPacketInwardness expenditureCoercivity : Index → Set i

    simultaneousWitness : ∀ q →
      Σ (tailAbsorption q) (λ _ →
      Σ (gammaInwardness q) (λ _ →
      Σ (packetPositivity q) (λ _ →
      Σ (offPacketInwardness q) (λ _ → expenditureCoercivity q))))

open SharedParameterFeasibility public

feasibleTuple-to-sharedParameters :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (P : CompactGammaParameterTuple {i} A) →
  SharedParameterFeasibility A Index P →
  SharedCompactGammaParameters A Index
feasibleTuple-to-sharedParameters P F = record
  { radius = radius P
  ; gammaFloor = gammaFloor P
  ; energyFloor = energyFloor P
  ; offPacketCeiling = offPacketCeiling P
  ; alphaEnergy = alphaEnergy P
  ; alphaGamma = alphaGamma P
  ; alphaOffPacket = alphaOffPacket P
  ; radiusAdmissible = radiusAdmissible F
  ; gammaFloorPositive = gammaFloorPositive F
  ; energyFloorPositive = energyFloorPositive F
  ; offPacketCeilingPositive = offPacketCeilingPositive F
  ; alphaEnergyPositive = alphaEnergyPositive F
  ; alphaGammaPositive = alphaGammaPositive F
  ; alphaOffPacketPositive = alphaOffPacketPositive F
  ; tailAbsorptionAtSharedParameters = tailAbsorption F
  ; gammaInwardAtSharedParameters = gammaInwardness F
  ; packetEnergyPositiveAtSharedParameters = packetPositivity F
  ; offPacketInwardAtSharedParameters = offPacketInwardness F
  ; expenditureCoerciveAtSharedParameters = expenditureCoercivity F
  }

feasibleTuple-to-simultaneousClosure :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (P : CompactGammaParameterTuple {i} A)
    (F : SharedParameterFeasibility A Index P) →
  SimultaneousLocalClosure A Index (feasibleTuple-to-sharedParameters P F)
feasibleTuple-to-simultaneousClosure P F = record
  { allFiveConditionsHold = simultaneousWitness F }

record ParameterFeasibilityCounterexample
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    attemptedTuple : CompactGammaParameterTuple {i} A
    FailedCondition : Set i
    failureWitness : FailedCondition

open ParameterFeasibilityCounterexample public

------------------------------------------------------------------------
-- 4. Official-data coverage: proof and refutation gates.
------------------------------------------------------------------------

record InitialAdmissibilityObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initialTime : Time S
    u₀ : InitialDatum S
    u : Solution S
    official : SmoothDivergenceFreeFiniteEnergy S u₀
    solves : SolvesFrom S u₀ u
    Not : Set i → Set i
    notInitiallyAdmissible : Not (CompactGammaAdmissible S u initialTime)
    contradiction :
      CompactGammaAdmissible S u initialTime →
      Not (CompactGammaAdmissible S u initialTime) → ⊥

open InitialAdmissibilityObstruction public

initial-obstruction-refutes-all-data-initially-admissible :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  InitialAdmissibilityObstruction S →
  AllDataInitiallyAdmissible S → ⊥
initial-obstruction-refutes-all-data-initially-admissible O A₀ =
  contradiction O
    (everyOfficialDatumStartsAdmissible A₀
      (u₀ O) (u O) (official O) (solves O))
    (notInitiallyAdmissible O)

record EntryBeforeSingularityObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    u₀ : InitialDatum S
    u : Solution S
    official : SmoothDivergenceFreeFiniteEnergy S u₀
    solves : SolvesFrom S u₀ u
    NotEntry : Time S → Set i
    noEntry : ∀ τ →
      Σ (BeforeAnySingularity S u τ)
        (λ _ → CompactGammaAdmissible S u τ) → NotEntry τ
    contradiction : ∀ τ →
      NotEntry τ →
      Σ (BeforeAnySingularity S u τ)
        (λ _ → CompactGammaAdmissible S u τ) → ⊥

open EntryBeforeSingularityObstruction public

entry-obstruction-refutes-universal-entry :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  EntryBeforeSingularityObstruction S →
  EverySolutionEntersBeforeSingularity S → ⊥
entry-obstruction-refutes-universal-entry {S = S} O E =
  contradiction O τ (noEntry O τ witness) witness
  where
  τ : Time S
  τ = entryTime E (u₀ O) (u O)

  witness :
    Σ (BeforeAnySingularity S (u O) τ)
      (λ _ → CompactGammaAdmissible S (u O) τ)
  witness = everyOfficialSolutionEnters E
    (u₀ O) (u O) (official O) (solves O)

record UniversalMechanismObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    u₀ : InitialDatum S
    official : SmoothDivergenceFreeFiniteEnergy S u₀
    Not : Set i → Set i
    noMechanism : Not (UniversalContinuationMechanism S u₀)
    contradiction :
      UniversalContinuationMechanism S u₀ →
      Not (UniversalContinuationMechanism S u₀) → ⊥

open UniversalMechanismObstruction public

mechanism-obstruction-refutes-universal-replacement :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  UniversalMechanismObstruction S →
  UniversalReplacementMechanism S → ⊥
mechanism-obstruction-refutes-universal-replacement O U =
  contradiction O
    (allOfficialDataHaveUniversalMechanism U (u₀ O) (official O))
    (noMechanism O)

record AllCoverageRoutesObstructed
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initial : InitialAdmissibilityObstruction S
    entry : EntryBeforeSingularityObstruction S
    replacement : UniversalMechanismObstruction S

open AllCoverageRoutesObstructed public

all-obstructions-refute-official-data-coverage :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  AllCoverageRoutesObstructed S → OfficialDataCoverage S → ⊥
all-obstructions-refute-official-data-coverage O (inj₁ starts) =
  initial-obstruction-refutes-all-data-initially-admissible (initial O) starts
all-obstructions-refute-official-data-coverage O (inj₂ (inj₁ enters)) =
  entry-obstruction-refutes-universal-entry (entry O) enters
all-obstructions-refute-official-data-coverage O (inj₂ (inj₂ universal)) =
  mechanism-obstruction-refutes-universal-replacement (replacement O) universal

------------------------------------------------------------------------
-- Proof-or-refutation frontier package.
------------------------------------------------------------------------

record FrontierResolution
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    fiveHalvesResolved :
      UniformFiveHalvesShellEnvelope A Index
      ⊎ Σ (TwoSidedShellDecayAttack A Index)
          (λ D → FiveHalvesEnvelopeCounterexample A Index D)

    gammaResolved :
      GammaNumeratorCoercivity A Index
      ⊎ Σ (RawGammaNearTailInequality A Index)
          (λ G → GammaCoercivityCounterexample A Index G)

    parametersResolved :
      Σ (CompactGammaParameterTuple {i} A)
        (λ P → SharedParameterFeasibility A Index P)
      ⊎ ParameterFeasibilityCounterexample A Index

    officialCoverageResolved :
      OfficialDataCoverage S ⊎ AllCoverageRoutesObstructed S

open FrontierResolution public
