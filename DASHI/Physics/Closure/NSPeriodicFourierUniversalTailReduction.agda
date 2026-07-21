module DASHI.Physics.Closure.NSPeriodicFourierUniversalTailReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic
import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion as Parameters
import DASHI.Physics.Closure.NSCompactGammaCanonicalParameterBridge as ParameterBridge
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction as RadiusEight
import DASHI.Physics.Closure.NSPeriodicFourierNearTriadPreYoung as Near
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction as Tail
import DASHI.Physics.Closure.NSCompactGammaInvariantCoverageReduction as Coverage

------------------------------------------------------------------------
-- One owner for the six universal packages after the finite certificate.
--
-- The fields are deliberately the earliest honest analytic inputs:
--
--   1. a universal five-halves theorem;
--   2. cutoff-uniform Fourier product bounds before Young;
--   3/4. primitive far-low/far-high chains;
--   5. semantic real-carrier parameter interpretation plus first-exit reduction;
--   6. adaptive-chart-or-direct-BKM official coverage.
--
-- All algebraic, transitivity, Young-composition, no-first-exit and coverage-case
-- assembly is proved below.  Supplying the fields in the concrete periodic
-- carrier remains the genuine PDE work.
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

    firstExitBoundary : Coverage.FirstExitBoundaryReduction i

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
  Coverage.FirstExit (firstExitBoundary R) τ u →
  Data.Empty.⊥
realCarrierFirstExitImpossible R =
  Coverage.compactGammaFirstExitImpossible (firstExitBoundary R)

record UniversalPeriodicFourierTailInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    fiveHalves : IndexedFiveHalvesUniversal A Index
    nearTriad : Near.NearTriadPreYoungInputs A Index
    radiusEight : Tail.RadiusEightPrimitiveInputs A Index

    realCarrier :
      RealCarrierInwardCoercivePackage A Index radiusEight

    officialCoverage : Coverage.AdaptiveChartOrDirectBKM S

open UniversalPeriodicFourierTailInputs public

universalFiveHalvesEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (weightedFiveHalvesSum (fiveHalves U) q τ)
    (compactGammaEnvelope (fiveHalves U) q τ)
universalFiveHalvesEndpoint U =
  compactGammaControlsFiveHalvesUniversally (fiveHalves U)

universalNearTriadEndpoint :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Near.nearTriadMagnitude (nearTriad U) q τ)
    (_+_ A
      (Near.deltaDissipation (nearTriad U) q τ)
      (Near.residualEnvelope (nearTriad U) q τ))
universalNearTriadEndpoint U =
  Near.nearTriadAbsorptionFromPreYoung (nearTriad U)

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
