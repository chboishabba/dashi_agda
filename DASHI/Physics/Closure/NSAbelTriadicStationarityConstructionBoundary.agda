module DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary as Abel
import DASHI.Physics.Closure.NSBoundedAbelMassEstimateBoundary as BoundedMass
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary as LRT
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary as Sheaf
import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as Symbol

------------------------------------------------------------------------
-- First NS analytic rung: Abel triadic stationarity construction boundary.
--
-- This boundary records the exact coupled A1/A3 bootstrap theorem wall needed
-- before the Abel triadic measure route can be handed downstream to A4:
--
--   A1.1 bounded Abel-weighted defect-measure mass
--   A1.2 weak-* compactness on the bounded Abel branch
--   A1.3 shell-tail control on the selected weak-* branch
--   A3.1 Seregin epsilon-rate intake
--   A3.2 energy ODE on Abel windows
--   A3.3 delta_r -> 0 stationarity defect limit
--   A3.4 multiscale Abel-summation closure
--   A4 downstream output-support transfer handoff (separate consumer)
--
-- It is a boundary module only.  No bounded-mass/compactness theorem, no
-- coupled A1/A3 bootstrap theorem, no A4 transfer theorem, no residual
-- consumer theorem, no Clay Navier-Stokes theorem, and no promotion flag is
-- introduced.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- A1-A4 carriers.

data BoundedMassA1Carrier : Set where
  boundedAbelTriadicDefectMass :
    Abel.AbelTriadicDefectMeasureCarrier →
    Abel.CriticalDissipationCarrier →
    BoundedMassA1Carrier

data TriadicObservableA2Carrier : Set where
  recordedTrueLerayTriadicObservable :
    Symbol.TrueNSBilinearSymbol →
    Sheaf.TriadicPatch →
    Sheaf.OutputProjection →
    TriadicObservableA2Carrier

data StationarityDefectScale : Set where
  delta-r :
    Abel.ParabolicScaleCarrier →
    StationarityDefectScale

data ApproximateTNSStationarityA3Carrier : Set where
  approximateTNSStationarityWithDeltaRTendingZero :
    Abel.AbelTriadicDefectMeasureCarrier →
    TriadicObservableA2Carrier →
    StationarityDefectScale →
    ApproximateTNSStationarityA3Carrier

data LRTOutputSupportTransferA4Carrier : Set where
  lrtOutputSupportTransferForStationarityRung :
    LRT.GreatCircleHittingProperty →
    Abel.OutputSupportTransferBoundary →
    Sheaf.OutputProjection →
    LRTOutputSupportTransferA4Carrier

canonicalA1BoundedMass :
  BoundedMassA1Carrier
canonicalA1BoundedMass =
  boundedAbelTriadicDefectMass
    Abel.canonicalAbelTriadicDefectMeasure
    Abel.canonicalDissipationDr

canonicalA2TriadicObservable :
  TriadicObservableA2Carrier
canonicalA2TriadicObservable =
  recordedTrueLerayTriadicObservable
    Symbol.canonicalTrueNSBilinearSymbol
    Sheaf.canonicalResonantPatch
    Sheaf.canonicalOutputProjection

canonicalDeltaR :
  StationarityDefectScale
canonicalDeltaR =
  delta-r Abel.canonicalParabolicScale

canonicalA3ApproximateTNSStationarity :
  ApproximateTNSStationarityA3Carrier
canonicalA3ApproximateTNSStationarity =
  approximateTNSStationarityWithDeltaRTendingZero
    Abel.canonicalAbelTriadicDefectMeasure
    canonicalA2TriadicObservable
    canonicalDeltaR

canonicalA4LRTOutputSupportTransfer :
  LRTOutputSupportTransferA4Carrier
canonicalA4LRTOutputSupportTransfer =
  lrtOutputSupportTransferForStationarityRung
    LRT.canonicalGreatCircleHittingProperty
    Abel.canonicalLRTGreatCircleOutputSupportTransfer
    Sheaf.canonicalOutputProjection

------------------------------------------------------------------------
-- Rung obligations and blockers.

data CoupledA1A3BootstrapObligation : Set where
  A11BoundedAbelMassObligation :
    CoupledA1A3BootstrapObligation
  A12WeakStarCompactnessObligation :
    CoupledA1A3BootstrapObligation
  A13ShellTailControlObligation :
    CoupledA1A3BootstrapObligation
  A31SereginEpsilonRateIntakeObligation :
    CoupledA1A3BootstrapObligation
  A32EnergyODEOnAbelWindowsObligation :
    CoupledA1A3BootstrapObligation
  A33DeltaRToZeroObligation :
    CoupledA1A3BootstrapObligation
  A34MultiscaleAbelSummationClosureObligation :
    CoupledA1A3BootstrapObligation
  A4DownstreamOutputSupportTransferHandoffObligation :
    CoupledA1A3BootstrapObligation
  keepClayPromotionBooleansFalseObligation :
    CoupledA1A3BootstrapObligation

canonicalNSAnalyticRungObligations :
  List CoupledA1A3BootstrapObligation
canonicalNSAnalyticRungObligations =
  A11BoundedAbelMassObligation
  ∷ A12WeakStarCompactnessObligation
  ∷ A13ShellTailControlObligation
  ∷ A31SereginEpsilonRateIntakeObligation
  ∷ A32EnergyODEOnAbelWindowsObligation
  ∷ A33DeltaRToZeroObligation
  ∷ A34MultiscaleAbelSummationClosureObligation
  ∷ A4DownstreamOutputSupportTransferHandoffObligation
  ∷ keepClayPromotionBooleansFalseObligation
  ∷ []

nsAnalyticRungObligationCount : Nat
nsAnalyticRungObligationCount =
  listLength canonicalNSAnalyticRungObligations

nsAnalyticRungObligationCountIs9 :
  nsAnalyticRungObligationCount ≡ 9
nsAnalyticRungObligationCountIs9 =
  refl

data CandidateCoupledA1A3BootstrapStep : Set where
  boundedAbelMassStep :
    CandidateCoupledA1A3BootstrapStep
  weakStarCompactnessStep :
    CandidateCoupledA1A3BootstrapStep
  shellTailControlStep :
    CandidateCoupledA1A3BootstrapStep
  sereginEpsilonRateIntakeStep :
    CandidateCoupledA1A3BootstrapStep
  energyODEStep :
    CandidateCoupledA1A3BootstrapStep
  deltaRToZeroStep :
    CandidateCoupledA1A3BootstrapStep
  multiscaleAbelSummationClosureStep :
    CandidateCoupledA1A3BootstrapStep

canonicalCandidateA1A3BootstrapSteps :
  List CandidateCoupledA1A3BootstrapStep
canonicalCandidateA1A3BootstrapSteps =
  boundedAbelMassStep
  ∷ weakStarCompactnessStep
  ∷ shellTailControlStep
  ∷ sereginEpsilonRateIntakeStep
  ∷ energyODEStep
  ∷ deltaRToZeroStep
  ∷ multiscaleAbelSummationClosureStep
  ∷ []

candidateA1A3BootstrapStepCount : Nat
candidateA1A3BootstrapStepCount =
  listLength canonicalCandidateA1A3BootstrapSteps

candidateA1A3BootstrapStepCountIs7 :
  candidateA1A3BootstrapStepCount ≡ 7
candidateA1A3BootstrapStepCountIs7 = refl

data CoupledA1A3BootstrapBlocker : Set where
  blockerA11BoundedAbelMass :
    CoupledA1A3BootstrapBlocker
  blockerA12WeakStarCompactness :
    CoupledA1A3BootstrapBlocker
  blockerA13ShellTailControl :
    CoupledA1A3BootstrapBlocker
  blockerA31SereginEpsilonRateIntake :
    CoupledA1A3BootstrapBlocker
  blockerA32EnergyODEOnAbelWindows :
    CoupledA1A3BootstrapBlocker
  blockerA33DeltaRToZero :
    CoupledA1A3BootstrapBlocker
  blockerA34MultiscaleAbelSummationClosure :
    CoupledA1A3BootstrapBlocker
  blockerA4DownstreamOutputSupportTransfer :
    CoupledA1A3BootstrapBlocker
  blockerResidualConsumerDownstream :
    CoupledA1A3BootstrapBlocker
  clayNavierStokesPromotionClosed :
    CoupledA1A3BootstrapBlocker

canonicalNSAnalyticRungBlockers :
  List CoupledA1A3BootstrapBlocker
canonicalNSAnalyticRungBlockers =
  blockerA11BoundedAbelMass
  ∷ blockerA12WeakStarCompactness
  ∷ blockerA13ShellTailControl
  ∷ blockerA31SereginEpsilonRateIntake
  ∷ blockerA32EnergyODEOnAbelWindows
  ∷ blockerA33DeltaRToZero
  ∷ blockerA34MultiscaleAbelSummationClosure
  ∷ blockerA4DownstreamOutputSupportTransfer
  ∷ blockerResidualConsumerDownstream
  ∷ clayNavierStokesPromotionClosed
  ∷ []

nsAnalyticRungBlockerCount : Nat
nsAnalyticRungBlockerCount =
  listLength canonicalNSAnalyticRungBlockers

nsAnalyticRungBlockerCountIs10 :
  nsAnalyticRungBlockerCount ≡ 10
nsAnalyticRungBlockerCountIs10 =
  refl

a31EnergyODETargetLabel : String
a31EnergyODETargetLabel =
  "A3.1 energy ODE"

a31EnergyODEContractText : String
a31EnergyODEContractText =
  "A3.1 energy-ODE clause: define the Abel-window profile difference W_r = U_r - U_infty and route the candidate windowed energy inequality against the imported A1 defect mass, with the closed estimate still blocked."

a31EnergyODEPrimaryBlockerName : String
a31EnergyODEPrimaryBlockerName =
  "blockerA32EnergyODEOnAbelWindows"

a32SereginESSIntakeTargetLabel : String
a32SereginESSIntakeTargetLabel =
  "A3.2 ESS/Seregin intake"

a32SereginESSIntakeContractText : String
a32SereginESSIntakeContractText =
  "A3.2 ESS/Seregin intake clause: record the Seregin/ESS compactness and epsilon-regularity intake as the imported candidate rate source epsilon = 1/6, with the actual quantitative extraction still blocked."

a32SereginESSIntakePrimaryBlockerName : String
a32SereginESSIntakePrimaryBlockerName =
  "blockerA31SereginEpsilonRateIntake"

a33StationarityDefectRateTargetLabel : String
a33StationarityDefectRateTargetLabel =
  "A3.3 stationarity-defect rate"

a33StationarityDefectRateContractText : String
a33StationarityDefectRateContractText =
  "A3.3 stationarity-defect rate clause: record the candidate stationarity-defect package delta_r = O(r^(1/12)) as the intended quantitative bridge to delta_r -> 0, while the actual derivation and limit remain blocked."

a33StationarityDefectRatePrimaryBlockerName : String
a33StationarityDefectRatePrimaryBlockerName =
  "blockerA33DeltaRToZero"

a34MultiscaleAbelSummationTargetLabel : String
a34MultiscaleAbelSummationTargetLabel =
  "A3.4 multiscale Abel-summation"

a34MultiscaleAbelSummationContractText : String
a34MultiscaleAbelSummationContractText =
  "A3.4 multiscale Abel-summation clause: keep the multiscale Abel-summation / fixed-point closure explicit before any A4 handoff, with no theorem promotion until the contraction route is discharged."

a34MultiscaleAbelSummationPrimaryBlockerName : String
a34MultiscaleAbelSummationPrimaryBlockerName =
  "blockerA34MultiscaleAbelSummationClosure"

record CoupledA3TargetRow : Set where
  field
    obligation :
      CoupledA1A3BootstrapObligation
    label :
      String
    contractText :
      String
    primaryBlocker :
      CoupledA1A3BootstrapBlocker
    primaryBlockerName :
      String
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false

open CoupledA3TargetRow public

mkCoupledA3TargetRow :
  CoupledA1A3BootstrapObligation →
  String →
  String →
  CoupledA1A3BootstrapBlocker →
  String →
  CoupledA3TargetRow
mkCoupledA3TargetRow obligation label contractText primaryBlocker
  primaryBlockerName =
  record
    { obligation =
        obligation
    ; label =
        label
    ; contractText =
        contractText
    ; primaryBlocker =
        primaryBlocker
    ; primaryBlockerName =
        primaryBlockerName
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalCoupledA3TargetRows :
  List CoupledA3TargetRow
canonicalCoupledA3TargetRows =
  mkCoupledA3TargetRow
    A32EnergyODEOnAbelWindowsObligation
    a31EnergyODETargetLabel
    a31EnergyODEContractText
    blockerA32EnergyODEOnAbelWindows
    a31EnergyODEPrimaryBlockerName
  ∷ mkCoupledA3TargetRow
    A31SereginEpsilonRateIntakeObligation
    a32SereginESSIntakeTargetLabel
    a32SereginESSIntakeContractText
    blockerA31SereginEpsilonRateIntake
    a32SereginESSIntakePrimaryBlockerName
  ∷ mkCoupledA3TargetRow
    A33DeltaRToZeroObligation
    a33StationarityDefectRateTargetLabel
    a33StationarityDefectRateContractText
    blockerA33DeltaRToZero
    a33StationarityDefectRatePrimaryBlockerName
  ∷ mkCoupledA3TargetRow
    A34MultiscaleAbelSummationClosureObligation
    a34MultiscaleAbelSummationTargetLabel
    a34MultiscaleAbelSummationContractText
    blockerA34MultiscaleAbelSummationClosure
    a34MultiscaleAbelSummationPrimaryBlockerName
  ∷ []

coupledA3TargetRowCount : Nat
coupledA3TargetRowCount =
  listLength canonicalCoupledA3TargetRows

coupledA3TargetRowCountIs4 :
  coupledA3TargetRowCount ≡ 4
coupledA3TargetRowCountIs4 =
  refl

------------------------------------------------------------------------
-- Public flags.

NSAbelTriadicStationarityConstructionBoundaryRecorded : Bool
NSAbelTriadicStationarityConstructionBoundaryRecorded =
  true

A1BoundedMassRecorded : Bool
A1BoundedMassRecorded =
  true

A2TriadicObservableRecorded : Bool
A2TriadicObservableRecorded =
  true

A3ApproximateTNSStationarityDeltaRToZeroRecorded : Bool
A3ApproximateTNSStationarityDeltaRToZeroRecorded =
  true

A4LRTOutputSupportTransferRecorded : Bool
A4LRTOutputSupportTransferRecorded =
  true

A1BoundedMassProved : Bool
A1BoundedMassProved =
  false

A2TriadicObservableContinuityProved : Bool
A2TriadicObservableContinuityProved =
  false

A3TNSStationarityProved : Bool
A3TNSStationarityProved =
  false

deltaRTendsToZeroProved : Bool
deltaRTendsToZeroProved =
  false

A4LRTOutputSupportTransferProved : Bool
A4LRTOutputSupportTransferProved =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

abelDefectMeasureBoundaryAnchor : Bool
abelDefectMeasureBoundaryAnchor =
  Abel.NSAbelTriadicDefectMeasureConstructionBoundaryRecorded

abelMeasureConstructedStillFalseAnchor : Bool
abelMeasureConstructedStillFalseAnchor =
  Abel.AbelTriadicDefectMeasureConstructed

abelOutputSupportTransferStillFalseAnchor : Bool
abelOutputSupportTransferStillFalseAnchor =
  Abel.OutputSupportTransferProved

lrtBoundaryAnchor : Bool
lrtBoundaryAnchor =
  LRT.NSLeiRenTianGreatCircleCriterionBoundaryRecorded

boundedMassBoundaryAnchor : Bool
boundedMassBoundaryAnchor =
  BoundedMass.NSBoundedAbelMassEstimateBoundaryRecorded

boundedMassProofStillFalseAnchor : Bool
boundedMassProofStillFalseAnchor =
  BoundedMass.BoundedAbelMassEstimateProved

recordsNSAbelTriadicStationarityBoundary :
  NSAbelTriadicStationarityConstructionBoundaryRecorded ≡ true
recordsNSAbelTriadicStationarityBoundary =
  refl

recordsA1BoundedMass :
  A1BoundedMassRecorded ≡ true
recordsA1BoundedMass =
  refl

recordsA2TriadicObservable :
  A2TriadicObservableRecorded ≡ true
recordsA2TriadicObservable =
  refl

recordsA3ApproximateTNSStationarity :
  A3ApproximateTNSStationarityDeltaRToZeroRecorded ≡ true
recordsA3ApproximateTNSStationarity =
  refl

recordsA4LRTOutputSupportTransfer :
  A4LRTOutputSupportTransferRecorded ≡ true
recordsA4LRTOutputSupportTransfer =
  refl

keepsA1BoundedMassProofFalse :
  A1BoundedMassProved ≡ false
keepsA1BoundedMassProofFalse =
  refl

keepsA2TriadicObservableContinuityFalse :
  A2TriadicObservableContinuityProved ≡ false
keepsA2TriadicObservableContinuityFalse =
  refl

keepsA3TNSStationarityFalse :
  A3TNSStationarityProved ≡ false
keepsA3TNSStationarityFalse =
  refl

keepsDeltaRTendsToZeroFalse :
  deltaRTendsToZeroProved ≡ false
keepsDeltaRTendsToZeroFalse =
  refl

keepsA4LRTOutputSupportTransferFalse :
  A4LRTOutputSupportTransferProved ≡ false
keepsA4LRTOutputSupportTransferFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker lane NS-A1A3-synthesis owns the coupled A1/A3 boundary receipt: A1.1 bounded Abel mass -> A1.2 weak-* compactness -> A1.3 shell-tail control -> A3.1 Seregin intake -> A3.2 energy ODE -> A3.3 delta_r -> 0 -> A3.4 multiscale Abel-summation closure, then separate downstream A4 handoff."

requirementString : String
requirementString =
  "R: Record the exact coupled bootstrap theorem wall and its downstream A4 consumer handoff while keeping every theorem, Clay, residual, and promotion boolean false."

codeArtifactString : String
codeArtifactString =
  "C: NSAbelTriadicStationarityConstructionBoundary is the single theorem-wall file for the coupled A1/A3 synthesis boundary, exposing canonical carriers, coupled obligations, candidate steps, blocker names, and the separate A4 handoff marker."

stateString : String
stateString =
  "S: The boundary is recorded only; bounded Abel mass, weak-* compactness, shell-tail control, Seregin intake, the Abel-window energy ODE, delta_r convergence, multiscale Abel-summation closure, and the downstream A4 transfer all remain unproved."

latticeString : String
latticeString =
  "L: broad first-rung receipt -> exact coupled bootstrap theorem wall -> separate A4 consumer handoff."

proposalString : String
proposalString =
  "P: Use this theorem wall to pin the open coupled route on the exact sequence bounded Abel mass + weak-* compactness + shell-tail control + Seregin intake + energy ODE + delta_r -> 0 + multiscale Abel-summation closure, with A4 transfer recorded as the next separate handoff."

governanceString : String
governanceString =
  "G: Only this boundary file records the coupled contract; bookkeeping flags may be true, but theorem, residual, Clay, and promotion booleans remain fail-closed."

gapString : String
gapString =
  "F: The one coherent remaining theorem wall is the coupled A1/A3 bootstrap itself: bounded Abel mass, weak-* compactness, shell-tail control, Seregin epsilon-rate intake, the Abel-window energy ODE, delta_r -> 0, and multiscale Abel-summation closure; A4 transfer is downstream but separate."

------------------------------------------------------------------------
-- Canonical receipt.

record NSAbelTriadicStationarityConstructionBoundary : Set where
  constructor nsAbelTriadicStationarityConstructionBoundary
  field
    a1BoundedMass :
      BoundedMassA1Carrier
    a1BoundedMassIsCanonical :
      a1BoundedMass ≡ canonicalA1BoundedMass
    a2TriadicObservable :
      TriadicObservableA2Carrier
    a2TriadicObservableIsCanonical :
      a2TriadicObservable ≡ canonicalA2TriadicObservable
    deltaR :
      StationarityDefectScale
    deltaRIsCanonical :
      deltaR ≡ canonicalDeltaR
    a3Stationarity :
      ApproximateTNSStationarityA3Carrier
    a3StationarityIsCanonical :
      a3Stationarity ≡ canonicalA3ApproximateTNSStationarity
    a4LRTOutputSupportTransfer :
      LRTOutputSupportTransferA4Carrier
    a4LRTOutputSupportTransferIsCanonical :
      a4LRTOutputSupportTransfer ≡ canonicalA4LRTOutputSupportTransfer
    obligations :
      List CoupledA1A3BootstrapObligation
    obligationsAreCanonical :
      obligations ≡ canonicalNSAnalyticRungObligations
    blockers :
      List CoupledA1A3BootstrapBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSAnalyticRungBlockers
    a3TargetRows :
      List CoupledA3TargetRow
    a3TargetRowsAreCanonical :
      a3TargetRows ≡ canonicalCoupledA3TargetRows
    a3TargetRowCountIsFour :
      coupledA3TargetRowCount ≡ 4
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString
    boundaryRecorded :
      NSAbelTriadicStationarityConstructionBoundaryRecorded ≡ true
    a1Recorded :
      A1BoundedMassRecorded ≡ true
    a2Recorded :
      A2TriadicObservableRecorded ≡ true
    a3Recorded :
      A3ApproximateTNSStationarityDeltaRToZeroRecorded ≡ true
    a4Recorded :
      A4LRTOutputSupportTransferRecorded ≡ true
    a1ProofFalse :
      A1BoundedMassProved ≡ false
    a2ContinuityFalse :
      A2TriadicObservableContinuityProved ≡ false
    a3StationarityFalse :
      A3TNSStationarityProved ≡ false
    deltaRLimitFalse :
      deltaRTendsToZeroProved ≡ false
    a4SupportTransferFalse :
      A4LRTOutputSupportTransferProved ≡ false
    residualNonPositiveFalse :
      NSCriticalResidualNonPositive ≡ false
    claySolvedFalse :
      fullClayNSSolved ≡ false
    clayPromotionFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSAbelTriadicStationarityConstructionBoundary public

canonicalNSAbelTriadicStationarityConstructionBoundary :
  NSAbelTriadicStationarityConstructionBoundary
canonicalNSAbelTriadicStationarityConstructionBoundary =
  nsAbelTriadicStationarityConstructionBoundary
    canonicalA1BoundedMass
    refl
    canonicalA2TriadicObservable
    refl
    canonicalDeltaR
    refl
    canonicalA3ApproximateTNSStationarity
    refl
    canonicalA4LRTOutputSupportTransfer
    refl
    canonicalNSAnalyticRungObligations
    refl
    canonicalNSAnalyticRungBlockers
    refl
    canonicalCoupledA3TargetRows
    refl
    refl
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
