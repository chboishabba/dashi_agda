module DASHI.Physics.Closure.NSPeriodicFourierUniversalTailReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion as Parameters
import DASHI.Physics.Closure.NSCompactGammaCanonicalParameterBridge as ParameterBridge
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction as RadiusEight
import DASHI.Physics.Closure.NSCompactGammaFiveHalvesSummationReduction as Summation
import DASHI.Physics.Closure.NSPeriodicFourierYoungFactorization as Young
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction as Tail
import DASHI.Physics.Closure.NSCompactGammaInvariantCoverageReduction as Coverage
import DASHI.Physics.Closure.NSCompactGammaDiniFirstExitReduction as Dini

------------------------------------------------------------------------
-- One owner for the six universal packages after the finite certificate.
--
-- The fields are deliberately the earliest honest analytic inputs:
--
--   1. pointwise five-halves decay plus countable coefficient summation;
--   2. cutoff-uniform Fourier product bounds plus one generic Young law;
--   3/4. primitive far-low/far-high chains;
--   5. semantic real-carrier parameter interpretation plus concrete Dini data;
--   6. adaptive-chart-or-direct-BKM official coverage.
--
-- All algebraic, summation, transitivity, Young-composition, no-first-exit and
-- coverage-case assembly is proved below.  Supplying the fields in the concrete
-- periodic carrier remains the genuine PDE work.
------------------------------------------------------------------------

record IndexedFiveHalvesUniversal
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time State : Set i
    selectedState : Index → Time → State
    weightedFiveHalvesSum compactGammaEnvelope :
      Index → Time → Scalar A

    compactGammaControlsFiveHalvesUniversally : ∀ q τ →
      _≤_ A
        (weightedFiveHalvesSum q τ)
        (compactGammaEnvelope q τ)

open IndexedFiveHalvesUniversal public

pointwiseSummationToIndexedFiveHalves :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : Summation.FiveHalvesPointwiseSummationInputs A Index) →
  IndexedFiveHalvesUniversal A Index
pointwiseSummationToIndexedFiveHalves P = record
  { Time = Summation.Time P
  ; State = Summation.State P
  ; selectedState = Summation.selectedState P
  ; weightedFiveHalvesSum = Summation.weightedFiveHalvesSum P
  ; compactGammaEnvelope = Summation.displayedCompactGammaEnvelope P
  ; compactGammaControlsFiveHalvesUniversally =
      Summation.fiveHalvesSumBelowDisplayedEnvelope P
  }

record RealCarrierInwardCoercivePackage
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (R8 : Tail.RadiusEightPrimitiveInputs A Index) : Set (lsuc i) where
  field
    parameterNumerals : Parameters.CanonicalParameterNumerals {i} A

    semanticBridge :
      ParameterBridge.CanonicalParameterSemanticBridge
        A Index parameterNumerals

    diniOrder : Dini.DiniBoundaryOrder i
    diniFirstExit : Dini.FourFaceDiniFirstExitReduction diniOrder

open RealCarrierInwardCoercivePackage public

realCarrierParameterInequalities :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {R8 : Tail.RadiusEightPrimitiveInputs A Index} →
  (R : RealCarrierInwardCoercivePackage A Index R8) →
  Parameters.CanonicalParameterInequalities
    A Index (parameterNumerals R)
realCarrierParameterInequalities {R8 = R8} R =
  ParameterBridge.canonicalParameterInequalitiesFromBridge
    (semanticBridge R)
    (RadiusEight.periodicRadiusEightAnalyticBounds
      (Tail.primitiveInputsToRadiusEightReduction R8))

realCarrierFirstExitImpossible :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {R8 : Tail.RadiusEightPrimitiveInputs A Index} →
  (R : RealCarrierInwardCoercivePackage A Index R8) →
  ∀ τ u →
  Dini.FirstExit (diniFirstExit R) τ u →
  ⊥
realCarrierFirstExitImpossible R =
  Dini.diniFirstExitImpossible (diniFirstExit R)

record UniversalPeriodicFourierTailInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    fiveHalvesPointwise :
      Summation.FiveHalvesPointwiseSummationInputs A Index

    youngLaw : Young.OrderedYoungLaw A
    nearTriad :
      Young.FactorizedNearTriadInputs A Index youngLaw

    radiusEight : Tail.RadiusEightPrimitiveInputs A Index

    realCarrier :
      RealCarrierInwardCoercivePackage A Index radiusEight

    officialCoverage : Coverage.AdaptiveChartOrDirectBKM S

open UniversalPeriodicFourierTailInputs public

fiveHalves :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  UniversalPeriodicFourierTailInputs A Index S →
  IndexedFiveHalvesUniversal A Index
fiveHalves U =
  pointwiseSummationToIndexedFiveHalves (fiveHalvesPointwise U)

universalFiveHalvesEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (IndexedFiveHalvesUniversal.weightedFiveHalvesSum
      (fiveHalves U) q τ)
    (IndexedFiveHalvesUniversal.compactGammaEnvelope
      (fiveHalves U) q τ)
universalFiveHalvesEndpoint U =
  IndexedFiveHalvesUniversal.compactGammaControlsFiveHalvesUniversally
    (fiveHalves U)

universalNearTriadEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Young.nearTriadMagnitude (nearTriad U) q τ)
    (_+_ A
      (Young.deltaDissipation (nearTriad U) q τ)
      (Young.residualEnvelope (nearTriad U) q τ))
universalNearTriadEndpoint U =
  Young.nearTriadAbsorptionFromFactorizedYoung (nearTriad U)

universalRadiusEightFarLowEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Tail.farLowTail (Tail.low (radiusEight U)) q τ)
    (Tail.displayedLowBudget (Tail.low (radiusEight U)) q τ)
universalRadiusEightFarLowEndpoint U =
  Tail.farLowRadiusEightFromPrimitive (Tail.low (radiusEight U))

universalRadiusEightFarHighEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Tail.farHighTail (Tail.high (radiusEight U)) q τ)
    (Tail.displayedHighBudget (Tail.high (radiusEight U)) q τ)
universalRadiusEightFarHighEndpoint U =
  Tail.farHighRadiusEightFromPrimitive (Tail.high (radiusEight U))

universalRealCarrierParameterEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  Parameters.CanonicalParameterInequalities
    A Index (parameterNumerals (realCarrier U))
universalRealCarrierParameterEndpoint U =
  realCarrierParameterInequalities (realCarrier U)

universalOfficialCoverageEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  UniversalPeriodicFourierTailInputs A Index S →
  UniversalReplacementMechanism S
universalOfficialCoverageEndpoint U =
  Coverage.adaptiveChartOrDirectBKMMechanism (officialCoverage U)

-- The owner and its projection theorems do not provide a concrete inhabitant.
universalTailInputsInhabitedInOfficialPeriodicCarrier : Bool
universalTailInputsInhabitedInOfficialPeriodicCarrier = false

unconditionalPeriodicGlobalRegularityFromThisModule : Bool
unconditionalPeriodicGlobalRegularityFromThisModule = false
