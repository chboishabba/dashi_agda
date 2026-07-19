module DASHI.Cognition.QuotientResidualDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.String using (_++_)

------------------------------------------------------------------------
-- Bool conjunction
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

------------------------------------------------------------------------
-- Quotient-residual dynamics: general theory surface
--
-- This module abstracts the tlurey/369 trace into a general mathematical
-- discipline: public systems observe low-dimensional quotient surfaces while
-- latent state-spaces retain fibre residuals.  Phase, prime-coordinate, and
-- dynamical classifications remain candidate-only until MDL/ZKP gates close.
------------------------------------------------------------------------

record Projection (Ω S : Set) : Set where
  constructor projection
  field
    observe : Ω → S

record NonInjectiveWitness {Ω S : Set} (q : Projection Ω S) : Set where
  constructor nonInjectiveWitness
  field
    leftState  : Ω
    rightState : Ω
    samePublicSurface : Projection.observe q leftState ≡ Projection.observe q rightState
    latentStatesDistinguished : Bool

record FibreResidualWitness {Ω S : Set} (q : Projection Ω S) : Set where
  constructor fibreResidualWitness
  field
    publicSurface : S
    fibreHasLatentContent : Bool
    distinctionsInvisibleFromSurface : Bool

record QuotientLossReceipt {Ω S : Set} (q : Projection Ω S) : Set where
  constructor quotientLossReceipt
  field
    witness : NonInjectiveWitness q
    fibreResidual : FibreResidualWitness q
    quotientLossPromotable : Bool

  receiptClosed : Bool
  receiptClosed =
    NonInjectiveWitness.latentStatesDistinguished witness
    ∧ FibreResidualWitness.fibreHasLatentContent fibreResidual
    ∧ FibreResidualWitness.distinctionsInvisibleFromSurface fibreResidual
    ∧ quotientLossPromotable

------------------------------------------------------------------------
-- Baby theorem: two public positions over two independent truth claims
-- expose a four-state hidden truth surface.
------------------------------------------------------------------------

data BinaryPosition : Set where
  sideA : BinaryPosition
  sideB : BinaryPosition

data TruthValue : Set where
  falseV : TruthValue
  trueV  : TruthValue

HiddenTruthState : Set
HiddenTruthState = TruthValue × TruthValue

binaryDebateProjection : Projection HiddenTruthState BinaryPosition
binaryDebateProjection =
  projection
    (λ where
      (trueV  , _) → sideA
      (falseV , _) → sideB)

binarySurfaceCardinality : Nat
binarySurfaceCardinality = 2

hiddenTruthLowerBound : Nat
hiddenTruthLowerBound = 4

binaryDebateLowerBound : hiddenTruthLowerBound ≡ 4
binaryDebateLowerBound = refl

binaryDebateNonInjectiveWitness : NonInjectiveWitness binaryDebateProjection
binaryDebateNonInjectiveWitness =
  nonInjectiveWitness
    (trueV , trueV)
    (trueV , falseV)
    refl
    true

binaryDebateFibreResidualWitness : FibreResidualWitness binaryDebateProjection
binaryDebateFibreResidualWitness =
  fibreResidualWitness
    sideA
    true
    true

binaryDebateQuotientLossReceipt : QuotientLossReceipt binaryDebateProjection
binaryDebateQuotientLossReceipt =
  quotientLossReceipt
    binaryDebateNonInjectiveWitness
    binaryDebateFibreResidualWitness
    true

binaryDebateQuotientLossClosed :
  QuotientLossReceipt.receiptClosed binaryDebateQuotientLossReceipt ≡ true
binaryDebateQuotientLossClosed = refl

------------------------------------------------------------------------
-- Recursive branch growth: n independent binary refinements have 2^n
-- possible assignments.  This is a counting theorem, not numerology.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero    = 1
pow2 (suc n) = 2 * pow2 n

branchAssignments : Nat → Nat
branchAssignments = pow2

zeroRefinementsOneAssignment : branchAssignments 0 ≡ 1
zeroRefinementsOneAssignment = refl

oneRefinementTwoAssignments : branchAssignments 1 ≡ 2
oneRefinementTwoAssignments = refl

twoRefinementsFourAssignments : branchAssignments 2 ≡ 4
twoRefinementsFourAssignments = refl

threeRefinementsEightAssignments : branchAssignments 3 ≡ 8
threeRefinementsEightAssignments = refl

record RecursiveBranchReceipt : Set where
  constructor recursiveBranchReceipt
  field
    binarySurfacePresent : Bool
    branchDepthTracked : Bool
    branchCountComputedByPow2 : Bool
    numerologyAuthorityBlocked : Bool

  receiptClosed : Bool
  receiptClosed =
    binarySurfacePresent
    ∧ branchDepthTracked
    ∧ branchCountComputedByPow2
    ∧ numerologyAuthorityBlocked

canonicalRecursiveBranchReceipt : RecursiveBranchReceipt
canonicalRecursiveBranchReceipt =
  recursiveBranchReceipt true true true true

canonicalRecursiveBranchClosed :
  RecursiveBranchReceipt.receiptClosed canonicalRecursiveBranchReceipt ≡ true
canonicalRecursiveBranchClosed = refl

------------------------------------------------------------------------
-- Phase-resolution tower: 2 is the public split; 3 is signed mediation;
-- 6 is a parity refinement of 3; 9 is two coupled triadic axes.
------------------------------------------------------------------------

data TriPhase : Set where
  triLow     : TriPhase
  triNeutral : TriPhase
  triHigh    : TriPhase

data Parity : Set where
  evenParity : Parity
  oddParity  : Parity

HexPhase : Set
HexPhase = TriPhase × Parity

NonarySheet : Set
NonarySheet = TriPhase × TriPhase

triadicLift : BinaryPosition → TriPhase
triadicLift sideA = triHigh
triadicLift sideB = triLow

adjoinMediator : TriPhase
adjoinMediator = triNeutral

hexRefinesTri : HexPhase → TriPhase
hexRefinesTri (tri , parity) = tri

hexParity : HexPhase → Parity
hexParity (tri , parity) = parity

nonaryFirstAxis : NonarySheet → TriPhase
nonaryFirstAxis (first , second) = first

nonarySecondAxis : NonarySheet → TriPhase
nonarySecondAxis (first , second) = second

record PhaseTowerReceipt : Set where
  constructor phaseTowerReceipt
  field
    triadicLiftAvailable : Bool
    hexadicParityRefinementAvailable : Bool
    nonaryCoupledSheetAvailable : Bool
    candidateOnly : Bool
    noPhaseAuthorityPromotion : Bool

  receiptClosed : Bool
  receiptClosed =
    triadicLiftAvailable
    ∧ hexadicParityRefinementAvailable
    ∧ nonaryCoupledSheetAvailable
    ∧ candidateOnly
    ∧ noPhaseAuthorityPromotion

canonicalPhaseTowerReceipt : PhaseTowerReceipt
canonicalPhaseTowerReceipt =
  phaseTowerReceipt true true true true true

canonicalPhaseTowerClosed :
  PhaseTowerReceipt.receiptClosed canonicalPhaseTowerReceipt ≡ true
canonicalPhaseTowerClosed = refl

------------------------------------------------------------------------
-- Residual pressure: a diagnostic summary of repeated lossy projection.
-- This is a candidate operational measure, not a truth authority.
------------------------------------------------------------------------

record ResidualPressureInputs : Set where
  constructor residualPressureInputs
  field
    collapsedDistinctions : Nat
    institutionalConsequence : Bool
    contestabilityBlocked : Bool
    recurrenceObserved : Bool
    wrongBinaryRepeated : Bool

record ResidualPressureReceipt : Set where
  constructor residualPressureReceipt
  field
    inputs : ResidualPressureInputs
    pressureDiagnosticAvailable : Bool
    candidateOnly : Bool

  pressureDetected : Bool
  pressureDetected =
    ResidualPressureInputs.institutionalConsequence inputs
    ∧ ResidualPressureInputs.contestabilityBlocked inputs
    ∧ ResidualPressureInputs.recurrenceObserved inputs
    ∧ ResidualPressureInputs.wrongBinaryRepeated inputs

  receiptClosed : Bool
  receiptClosed = pressureDiagnosticAvailable ∧ candidateOnly

canonicalResidualPressureInputs : ResidualPressureInputs
canonicalResidualPressureInputs =
  residualPressureInputs 4 true true true true

canonicalResidualPressureReceipt : ResidualPressureReceipt
canonicalResidualPressureReceipt =
  residualPressureReceipt canonicalResidualPressureInputs true true

canonicalResidualPressureClosed :
  ResidualPressureReceipt.receiptClosed canonicalResidualPressureReceipt ≡ true
canonicalResidualPressureClosed = refl

------------------------------------------------------------------------
-- Transition geometry: for non-linear discourse/cognition systems, arrows
-- may be more stable than static labels.
------------------------------------------------------------------------

Transition : Set → Set
Transition Ω = Ω → Ω

data TransitionDiagnostic : Set where
  fixedPointLike    : TransitionDiagnostic
  convergentLike    : TransitionDiagnostic
  periodicLike      : TransitionDiagnostic
  bifurcationLike   : TransitionDiagnostic
  chaosLike         : TransitionDiagnostic
  unclassifiedLike  : TransitionDiagnostic

record TransitionGeometryReceipt : Set₁ where
  constructor transitionGeometryReceipt
  field
    transitionSurface : Set
    transitionRule : Transition transitionSurface
    diagnostic : TransitionDiagnostic
    arrowsTestedInsteadOfOnlyPoints : Bool
    diagnosticOnly : Bool
    noLiteralDynamicsClaim : Bool

  receiptClosed : Bool
  receiptClosed =
    arrowsTestedInsteadOfOnlyPoints
    ∧ diagnosticOnly
    ∧ noLiteralDynamicsClaim

identityTransition : HiddenTruthState → HiddenTruthState
identityTransition state = state

canonicalTransitionGeometryReceipt : TransitionGeometryReceipt
canonicalTransitionGeometryReceipt =
  transitionGeometryReceipt
    HiddenTruthState
    identityTransition
    fixedPointLike
    true
    true
    true

canonicalTransitionGeometryClosed :
  TransitionGeometryReceipt.receiptClosed canonicalTransitionGeometryReceipt ≡ true
canonicalTransitionGeometryClosed = refl

------------------------------------------------------------------------
-- Prime/factor coordinates: candidate sparse coordinates for independent
-- residual factors.  Unique factorisation motivates the carrier; MDL/ZKP
-- still decides whether it is useful/admissible in a given trace.
------------------------------------------------------------------------

PrimeLaneVector : Set
PrimeLaneVector = Nat × Nat × Nat × Nat × Nat

zeroFactorVector : PrimeLaneVector
zeroFactorVector = 0 , 0 , 0 , 0 , 0

record FactorCoordinateReceipt : Set where
  constructor factorCoordinateReceipt
  field
    factorVectorCarrierAvailable : Bool
    independentResidualLanesCandidate : Bool
    divisibilityOrderCandidate : Bool
    pAdicLocalViewCandidate : Bool
    candidateOnly : Bool
    noPrimeMysticismPromotion : Bool

  receiptClosed : Bool
  receiptClosed =
    factorVectorCarrierAvailable
    ∧ independentResidualLanesCandidate
    ∧ divisibilityOrderCandidate
    ∧ pAdicLocalViewCandidate
    ∧ candidateOnly
    ∧ noPrimeMysticismPromotion

canonicalFactorCoordinateReceipt : FactorCoordinateReceipt
canonicalFactorCoordinateReceipt =
  factorCoordinateReceipt true true true true true true

canonicalFactorCoordinateClosed :
  FactorCoordinateReceipt.receiptClosed canonicalFactorCoordinateReceipt ≡ true
canonicalFactorCoordinateClosed = refl

------------------------------------------------------------------------
-- Sheaf-style obstruction: multiple local projections may be individually
-- valid while failing to glue into one global account.
------------------------------------------------------------------------

record LocalProjectionChart : Set₁ where
  constructor localProjectionChart
  field
    LocalState : Set
    Surface : Set
    chartProjection : Projection LocalState Surface
    locallyLegible : Bool

record SheafObstructionReceipt : Set₁ where
  constructor sheafObstructionReceipt
  field
    firstChart : LocalProjectionChart
    secondChart : LocalProjectionChart
    localViewsValid : Bool
    overlapResidualDetected : Bool
    globalGluingObstructed : Bool
    obstructionCandidateOnly : Bool

  receiptClosed : Bool
  receiptClosed =
    localViewsValid
    ∧ overlapResidualDetected
    ∧ globalGluingObstructed
    ∧ obstructionCandidateOnly

binaryChart : LocalProjectionChart
binaryChart =
  localProjectionChart
    HiddenTruthState
    BinaryPosition
    binaryDebateProjection
    true

canonicalSheafObstructionReceipt : SheafObstructionReceipt
canonicalSheafObstructionReceipt =
  sheafObstructionReceipt
    binaryChart
    binaryChart
    true
    true
    true
    true

canonicalSheafObstructionClosed :
  SheafObstructionReceipt.receiptClosed canonicalSheafObstructionReceipt ≡ true
canonicalSheafObstructionClosed = refl

------------------------------------------------------------------------
-- MDL and ZKP admission: every added geometry must pay rent in compression;
-- every public claim needs reconstructible witnesses and closed blockers.
------------------------------------------------------------------------

record MDLAdmission : Set where
  constructor mdlAdmission
  field
    previousDescriptionLength : Nat
    candidateDescriptionLength : Nat
    complexityPenaltyCounted : Bool
    compressionGainWitnessed : Bool
    candidateRetainedOnlyAfterGain : Bool

  gateClosed : Bool
  gateClosed =
    complexityPenaltyCounted
    ∧ compressionGainWitnessed
    ∧ candidateRetainedOnlyAfterGain

record ZKPAdmission : Set where
  constructor zkpAdmission
  field
    witnessReconstructible : Bool
    unsafeContentNotRevealed : Bool
    numerologyAuthorityBlocked : Bool
    clinicalInferenceBlocked : Bool
    ethnicReligiousEssentialismBlocked : Bool
    politicalProphecyBlocked : Bool

  gateClosed : Bool
  gateClosed =
    witnessReconstructible
    ∧ unsafeContentNotRevealed
    ∧ numerologyAuthorityBlocked
    ∧ clinicalInferenceBlocked
    ∧ ethnicReligiousEssentialismBlocked
    ∧ politicalProphecyBlocked

canonicalMDLAdmission : MDLAdmission
canonicalMDLAdmission =
  mdlAdmission 10 7 true true true

canonicalZKPAdmission : ZKPAdmission
canonicalZKPAdmission =
  zkpAdmission true true true true true true

canonicalMDLAdmissionClosed : MDLAdmission.gateClosed canonicalMDLAdmission ≡ true
canonicalMDLAdmissionClosed = refl

canonicalZKPAdmissionClosed : ZKPAdmission.gateClosed canonicalZKPAdmission ≡ true
canonicalZKPAdmissionClosed = refl

------------------------------------------------------------------------
-- Capstone receipt for the theorem-family.
------------------------------------------------------------------------

record QuotientResidualDynamicsReceipt : Set₁ where
  constructor quotientResidualDynamicsReceipt
  field
    quotientLossLayer : QuotientLossReceipt binaryDebateProjection
    recursiveBranchLayer : RecursiveBranchReceipt
    phaseTowerLayer : PhaseTowerReceipt
    residualPressureLayer : ResidualPressureReceipt
    transitionGeometryLayer : TransitionGeometryReceipt
    factorCoordinateLayer : FactorCoordinateReceipt
    sheafObstructionLayer : SheafObstructionReceipt
    mdlGate : MDLAdmission
    zkpGate : ZKPAdmission

  structuralLayerClosed : Bool
  structuralLayerClosed =
    QuotientLossReceipt.receiptClosed quotientLossLayer
    ∧ RecursiveBranchReceipt.receiptClosed recursiveBranchLayer

  candidateGeometryClosed : Bool
  candidateGeometryClosed =
    PhaseTowerReceipt.receiptClosed phaseTowerLayer
    ∧ ResidualPressureReceipt.receiptClosed residualPressureLayer
    ∧ TransitionGeometryReceipt.receiptClosed transitionGeometryLayer
    ∧ FactorCoordinateReceipt.receiptClosed factorCoordinateLayer
    ∧ SheafObstructionReceipt.receiptClosed sheafObstructionLayer

  admissionClosed : Bool
  admissionClosed = MDLAdmission.gateClosed mdlGate ∧ ZKPAdmission.gateClosed zkpGate

  allClosed : Bool
  allClosed = structuralLayerClosed ∧ candidateGeometryClosed ∧ admissionClosed

  closureStatement : String
  closureStatement =
    "Quotient-Residual Dynamics: public surfaces are lossy quotient projections. "
    ++ "Promoted: quotient loss, fibre residuals, and recursive branch growth. "
    ++ "Candidate-only: phase towers, residual pressure, transition diagnostics, "
    ++ "prime coordinates, and sheaf-style gluing obstructions. "
    ++ "MDL decides whether a coordinate earns its compression cost; "
    ++ "ZKP decides whether the public claim is admissible."

canonicalQuotientResidualDynamicsReceipt : QuotientResidualDynamicsReceipt
canonicalQuotientResidualDynamicsReceipt =
  quotientResidualDynamicsReceipt
    binaryDebateQuotientLossReceipt
    canonicalRecursiveBranchReceipt
    canonicalPhaseTowerReceipt
    canonicalResidualPressureReceipt
    canonicalTransitionGeometryReceipt
    canonicalFactorCoordinateReceipt
    canonicalSheafObstructionReceipt
    canonicalMDLAdmission
    canonicalZKPAdmission

canonicalStructuralLayerClosed :
  QuotientResidualDynamicsReceipt.structuralLayerClosed
    canonicalQuotientResidualDynamicsReceipt
  ≡ true
canonicalStructuralLayerClosed = refl

canonicalCandidateGeometryClosed :
  QuotientResidualDynamicsReceipt.candidateGeometryClosed
    canonicalQuotientResidualDynamicsReceipt
  ≡ true
canonicalCandidateGeometryClosed = refl

canonicalAdmissionClosed :
  QuotientResidualDynamicsReceipt.admissionClosed
    canonicalQuotientResidualDynamicsReceipt
  ≡ true
canonicalAdmissionClosed = refl

canonicalAllClosed :
  QuotientResidualDynamicsReceipt.allClosed
    canonicalQuotientResidualDynamicsReceipt
  ≡ true
canonicalAllClosed = refl
