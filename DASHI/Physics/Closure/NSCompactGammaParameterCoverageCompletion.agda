module DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas as Frontier

------------------------------------------------------------------------
-- One canonical seven-parameter tuple.
--
-- The generic arithmetic layer cannot manufacture rational numerals.  The
-- selected real carrier therefore supplies exact meanings for 8, 1/4, 1/2,
-- 1 and 2.  The tuple is fixed once and all five local estimates consume it.
-- Unlike the earlier candidate, eta* is represented by 1/2, making the strict
-- off-packet barrier requirement visible rather than silently using eta*=1.
------------------------------------------------------------------------

record CanonicalParameterNumerals
    {i : Level}
    (A : AbsorptionArithmetic) : Set (lsuc i) where
  field
    eight quarter half one two : Scalar A

open CanonicalParameterNumerals public

canonicalSevenParameterTuple :
  ∀ {i} {A : AbsorptionArithmetic} →
  CanonicalParameterNumerals {i} A →
  Frontier.CompactGammaParameterTuple {i} A
canonicalSevenParameterTuple N = record
  { radius = eight N
  ; gammaFloor = quarter N
  ; energyFloor = quarter N
  ; offPacketCeiling = half N
  ; alphaEnergy = two N
  ; alphaGamma = two N
  ; alphaOffPacket = one N
  }

------------------------------------------------------------------------
-- Exact scalar constraints for feasibility.
------------------------------------------------------------------------

record CanonicalParameterInequalities
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (N : CanonicalParameterNumerals {i} A) : Set (lsuc i) where
  field
    Positive StrictlyBelow : Scalar A → Set i
    LessThan : Scalar A → Scalar A → Set i

    radiusLargeEnoughForTail : Set i
    gammaFloorCompatible : Positive (quarter N)
    energyFloorCompatible : Positive (quarter N)
    offPacketCeilingPositive : Positive (half N)
    offPacketCeilingStrict : LessThan (half N) (one N)

    alphaEnergyPositive : Positive (two N)
    alphaGammaPositive : Positive (two N)
    alphaOffPacketPositive : Positive (one N)

    packetWeightAbsorbsError : Index → Set i
    gammaWeightAbsorbsError : Index → Set i
    offPacketWeightAbsorbsError : Index → Set i
    tailAbsorptionAtCanonicalTuple : Index → Set i
    gammaInwardAtCanonicalTuple : Index → Set i
    packetEnergyPositiveAtCanonicalTuple : Index → Set i
    offPacketInwardAtCanonicalTuple : Index → Set i
    totalCoerciveCoefficientPositive : Index → Set i

    allCanonicalConditionsHold : ∀ q →
      Σ (tailAbsorptionAtCanonicalTuple q) (λ _ →
      Σ (gammaInwardAtCanonicalTuple q) (λ _ →
      Σ (packetEnergyPositiveAtCanonicalTuple q) (λ _ →
      Σ (offPacketInwardAtCanonicalTuple q)
        (λ _ → totalCoerciveCoefficientPositive q))))

open CanonicalParameterInequalities public

canonicalTupleFeasible :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (N : CanonicalParameterNumerals {i} A) →
  CanonicalParameterInequalities A Index N →
  Frontier.SharedParameterFeasibility A Index
    (canonicalSevenParameterTuple N)
canonicalTupleFeasible N C = record
  { radiusAdmissible = radiusLargeEnoughForTail C
  ; gammaFloorPositive = gammaFloorCompatible C
  ; energyFloorPositive = energyFloorCompatible C
  ; offPacketCeilingPositive = offPacketCeilingPositive C
  ; alphaEnergyPositive = alphaEnergyPositive C
  ; alphaGammaPositive = alphaGammaPositive C
  ; alphaOffPacketPositive = alphaOffPacketPositive C
  ; tailAbsorption = tailAbsorptionAtCanonicalTuple C
  ; gammaInwardness = gammaInwardAtCanonicalTuple C
  ; packetPositivity = packetEnergyPositiveAtCanonicalTuple C
  ; offPacketInwardness = offPacketInwardAtCanonicalTuple C
  ; expenditureCoercivity = totalCoerciveCoefficientPositive C
  ; simultaneousWitness = allCanonicalConditionsHold C
  }

canonicalTupleClosesAllLocalConditions :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (N : CanonicalParameterNumerals {i} A)
    (C : CanonicalParameterInequalities A Index N) →
  SimultaneousLocalClosure A Index
    (Frontier.feasibleTuple-to-sharedParameters
      (canonicalSevenParameterTuple N)
      (canonicalTupleFeasible N C))
canonicalTupleClosesAllLocalConditions N C =
  Frontier.feasibleTuple-to-simultaneousClosure
    (canonicalSevenParameterTuple N)
    (canonicalTupleFeasible N C)

------------------------------------------------------------------------
-- Official-data coverage route A: split the zero solution from nonzero data.
------------------------------------------------------------------------

record ZeroNonzeroOfficialCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    zeroDatum : InitialDatum S
    zeroSolution : Solution S
    zeroIsOfficial : SmoothDivergenceFreeFiniteEnergy S zeroDatum
    zeroSolves : SolvesFrom S zeroDatum zeroSolution

    GlobalSmoothSolution : InitialDatum S → Set i
    zeroDatumGlobalSmooth : GlobalSmoothSolution zeroDatum

    NotEqual : InitialDatum S → InitialDatum S → Set i
    Shell : Set i
    selectedShell : InitialDatum S → Shell
    initialTime : Time S
    AdmissibleAtShell : Shell → Solution S → Time S → Set i

    nonzeroOfficialDatumInitiallyAdmissibleAfterCanonicalSelection :
      ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      NotEqual u₀ zeroDatum →
      AdmissibleAtShell (selectedShell u₀) u initialTime

    nonzeroRouteCloses : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      NotEqual u₀ zeroDatum →
      GlobalSmoothSolution u₀

open ZeroNonzeroOfficialCoverage public

zeroDatumGlobalSmoothTheorem :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : ZeroNonzeroOfficialCoverage S) →
  GlobalSmoothSolution C (zeroDatum C)
zeroDatumGlobalSmoothTheorem = zeroDatumGlobalSmooth

nonzeroOfficialDatumInitiallyAdmissible :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : ZeroNonzeroOfficialCoverage S) →
  ∀ u₀ u →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  SolvesFrom S u₀ u →
  NotEqual C u₀ (zeroDatum C) →
  AdmissibleAtShell C (selectedShell C u₀) u (initialTime C)
nonzeroOfficialDatumInitiallyAdmissible =
  nonzeroOfficialDatumInitiallyAdmissibleAfterCanonicalSelection

------------------------------------------------------------------------
-- Official-data coverage route B: entry before the maximal singular time.
------------------------------------------------------------------------

record EntryCoverageRoute
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    entryTime : InitialDatum S → Solution S → Time S
    everyOfficialSolutionEntersCompactGammaRegion : ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      Σ (BeforeAnySingularity S u (entryTime u₀ u))
        (λ _ → CompactGammaAdmissible S u (entryTime u₀ u))

    preservationAfterEntry : ∀ u₀ u → Set i

open EntryCoverageRoute public

entryRouteToRepositoryCoverage :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  EntryCoverageRoute S → EverySolutionEntersBeforeSingularity S
entryRouteToRepositoryCoverage E = record
  { entryTime = entryTime E
  ; everyOfficialSolutionEnters =
      everyOfficialSolutionEntersCompactGammaRegion E
  }

------------------------------------------------------------------------
-- Official-data coverage route C: a finite packet atlas with controlled chart
-- switching.  This avoids requiring one fixed active shell for every datum.
------------------------------------------------------------------------

record FinitePacketAtlasCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    Chart : Set i
    chartFor : Solution S → Time S → Chart
    AdmissibleInChart : Chart → Solution S → Time S → Set i
    IsZeroSolution : Solution S → Set i
    Not : Set i → Set i

    finitePacketAtlasCoversEveryNonzeroState : ∀ u τ →
      Not (IsZeroSolution u) →
      Σ Chart (λ chart → AdmissibleInChart chart u τ)

    packetChartSwitchPreservesAbsoluteContinuity : ∀ u → Set i
    packetChartSwitchHasSummableCost : ∀ u → Set i
    packetAtlasInvariantUntilContinuation : ∀ u → Set i

    atlasSuppliesUniversalMechanism : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      UniversalContinuationMechanism S u₀

open FinitePacketAtlasCoverage public

packetAtlasToRepositoryCoverage :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  FinitePacketAtlasCoverage S → UniversalReplacementMechanism S
packetAtlasToRepositoryCoverage A = record
  { allOfficialDataHaveUniversalMechanism =
      atlasSuppliesUniversalMechanism A
  }

------------------------------------------------------------------------
-- Route D: rigorous obstruction to all compact-Gamma coverage mechanisms.
------------------------------------------------------------------------

record FullCompactGammaUniversalityObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initialRouteObstruction : Frontier.InitialAdmissibilityObstruction S
    entryRouteObstruction : Frontier.EntryBeforeSingularityObstruction S
    replacementRouteObstruction : Frontier.UniversalMechanismObstruction S

    SmoothProfile : Set i
    smoothDatumNeverEntersAnyCompactGammaChart : SmoothProfile
    activeShellSwitchingHasInfiniteVariation : SmoothProfile
    fiveHalvesEnvelopeCounterexample : SmoothProfile
    gammaMarginCounterexample : SmoothProfile

open FullCompactGammaUniversalityObstruction public

fullObstructionRefutesOfficialDataCoverage :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  FullCompactGammaUniversalityObstruction S →
  OfficialDataCoverage S → ⊥
fullObstructionRefutesOfficialDataCoverage O =
  Frontier.all-obstructions-refute-official-data-coverage record
    { initial = initialRouteObstruction O
    ; entry = entryRouteObstruction O
    ; replacement = replacementRouteObstruction O
    }

------------------------------------------------------------------------
-- One exact proof-or-obstruction resolution type for the official class.
------------------------------------------------------------------------

OfficialCoverageResolution :
  ∀ {i} → OfficialInitialDataSetting i → Set (lsuc i)
OfficialCoverageResolution S =
  ZeroNonzeroOfficialCoverage S
  ⊎ (EntryCoverageRoute S
  ⊎ (FinitePacketAtlasCoverage S
  ⊎ FullCompactGammaUniversalityObstruction S))

record ParameterAndCoverageResolution
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i)
    (N : CanonicalParameterNumerals {i} A) : Set (lsuc i) where
  field
    parameters :
      CanonicalParameterInequalities A Index N
      ⊎ Frontier.ParameterFeasibilityCounterexample A Index
    officialCoverage : OfficialCoverageResolution S

open ParameterAndCoverageResolution public
