module DASHI.Physics.Closure.NSPeriodicFourierUniversalTailReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion as Parameters
import DASHI.Physics.Closure.NSCompactGammaCanonicalParameterBridge as ParameterBridge
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction as RadiusEight
import DASHI.Physics.Closure.NSCompactGammaFiveHalvesSummationReduction as Summation
import DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters as Selected
import DASHI.Physics.Closure.NSPeriodicFourierYoungFactorization as Young
import DASHI.Physics.Closure.NSPeriodicFourierNearTriadAuthorityBridge as NearBridge
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction as Tail
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightAuthorityBridge as RadiusBridge
import DASHI.Physics.Closure.NSCompactGammaDiniFirstExitReduction as Dini
import DASHI.Physics.Closure.NSPeriodicContinuationAuthorityAdapter as Continuation
import DASHI.Physics.Closure.NSCompactGammaCoverageFromContinuationAuthority as Coverage

------------------------------------------------------------------------
-- One owner for the six universal packages after the finite certificate.
--
-- Standard Bony, commutator, Sobolev-tail and continuation theorems are consumed
-- through exact carrier adapters.  The remaining fields are the genuinely novel
-- compact-Gamma interpretations, normalizations, boundary estimates and all-data
-- classification.  Carrier-equality fields prevent cross-model witness mixing.
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
    SharedShell SharedTime SharedState : Set i

    harmonicAuthority :
      Selected.SelectedPeriodicHarmonicAuthority
        A Index SharedShell SharedTime SharedState

    fiveHalvesPointwise :
      Summation.FiveHalvesPointwiseSummationInputs A Index

    youngLaw : Young.OrderedYoungLaw A

    nearTriadInterpretation :
      NearBridge.NearTriadAuthorityInterpretation
        A Index SharedShell SharedTime SharedState
        harmonicAuthority youngLaw

    radiusEightInterpretation :
      RadiusBridge.RadiusEightAuthorityInterpretation
        A Index SharedShell SharedTime SharedState
        harmonicAuthority

    realCarrier :
      RealCarrierInwardCoercivePackage A Index
        (RadiusBridge.authorityInterpretationToRadiusEightPrimitive
          radiusEightInterpretation)

    continuationAuthority :
      Continuation.SelectedPeriodicContinuationAuthority S

    novelCoverage :
      Coverage.NovelCoverageInputs S continuationAuthority

    fiveHalvesTimeCoherent :
      Summation.Time fiveHalvesPointwise ≡ SharedTime
    fiveHalvesStateCoherent :
      Summation.State fiveHalvesPointwise ≡ SharedState

    fiveHalvesSelectedStateCoherent : ∀ q τ →
      subst (λ Carrier → Carrier) fiveHalvesStateCoherent
        (Summation.selectedState fiveHalvesPointwise q τ) ≡
      Selected.selectedState harmonicAuthority q
        (subst (λ Carrier → Carrier) fiveHalvesTimeCoherent τ)

    diniTimeCoherent :
      Dini.Time (diniFirstExit realCarrier) ≡ SharedTime
    diniStateCoherent :
      Dini.State (diniFirstExit realCarrier) ≡ SharedState
    officialTimeCoherent :
      Time S ≡ SharedTime
    officialSolutionCoherent :
      Solution S ≡ SharedState

open UniversalPeriodicFourierTailInputs public

fiveHalves :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  UniversalPeriodicFourierTailInputs A Index S →
  IndexedFiveHalvesUniversal A Index
fiveHalves U =
  pointwiseSummationToIndexedFiveHalves (fiveHalvesPointwise U)

nearTriad :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (U : UniversalPeriodicFourierTailInputs A Index S) →
  Young.FactorizedNearTriadInputs A Index (youngLaw U)
nearTriad U =
  NearBridge.authorityInterpretationToFactorizedNearTriad
    (nearTriadInterpretation U)

radiusEight :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  UniversalPeriodicFourierTailInputs A Index S →
  Tail.RadiusEightPrimitiveInputs A Index
radiusEight U =
  RadiusBridge.authorityInterpretationToRadiusEightPrimitive
    (radiusEightInterpretation U)

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
  Coverage.coverageFromStandardContinuationAndNovelInputs
    (novelCoverage U)

universalTailInputsInhabitedInOfficialPeriodicCarrier : Bool
universalTailInputsInhabitedInOfficialPeriodicCarrier = false

unconditionalPeriodicGlobalRegularityFromThisModule : Bool
unconditionalPeriodicGlobalRegularityFromThisModule = false
