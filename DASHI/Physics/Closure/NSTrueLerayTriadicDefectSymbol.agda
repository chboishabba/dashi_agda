module DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- True Leray triadic defect symbol boundary.
--
-- The old scalar angular zero-mode surface is too small for Navier-Stokes:
-- the actual nonlinear obstruction is bilinear.  This module records the
-- exact non-averaged Leray triad object as a fail-closed Agda boundary:
--
--   input directions a,b
--   scale ratio rho
--   output direction c = normalize (rho a + b)
--   divergence-free polarizations
--   output Leray projector P(c)
--   true bilinear symbol B_NS(a,b,c,pol)
--   stretching projection Pi(c)
--   Delta_NS^triad = Pi N^dagger (1 - Pi) N Pi
--   zero-mode family targets I/II
--   Tao averaged-NS falsifiability guard
--
-- This is a recording surface only.  It does not prove positive output
-- width, cascade-closed rigidity, leakage transfer, residual monotonicity,
-- or Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Symbolic vector, scale, and polarization carriers.

data Direction3 : Set where
  inputDirectionA :
    Direction3
  inputDirectionB :
    Direction3
  outputDirectionC :
    Direction3
  outputVorticityDirection :
    Direction3
  maximalStretchingDirection :
    Direction3

data PositiveScaleRatio : Set where
  rhoPositive :
    PositiveScaleRatio

data TriadResonanceLaw : Set where
  outputIsNormalizeRhoAToB :
    PositiveScaleRatio →
    Direction3 →
    Direction3 →
    Direction3 →
    TriadResonanceLaw

canonicalRho : PositiveScaleRatio
canonicalRho =
  rhoPositive

canonicalInputA : Direction3
canonicalInputA =
  inputDirectionA

canonicalInputB : Direction3
canonicalInputB =
  inputDirectionB

canonicalOutputC : Direction3
canonicalOutputC =
  outputDirectionC

canonicalTriadResonanceLaw : TriadResonanceLaw
canonicalTriadResonanceLaw =
  outputIsNormalizeRhoAToB
    canonicalRho
    canonicalInputA
    canonicalInputB
    canonicalOutputC

data PolarizationChannel : Set where
  divergenceFreeInputPolarizationA :
    PolarizationChannel
  divergenceFreeInputPolarizationB :
    PolarizationChannel
  outputDivergenceFreePolarization :
    PolarizationChannel
  stretchingChannelPolarization :
    PolarizationChannel
  leakageChannelPolarization :
    PolarizationChannel

data TriadPolarizationPackage : Set where
  triadPolarizations :
    PolarizationChannel →
    PolarizationChannel →
    PolarizationChannel →
    TriadPolarizationPackage

canonicalTriadPolarizations : TriadPolarizationPackage
canonicalTriadPolarizations =
  triadPolarizations
    divergenceFreeInputPolarizationA
    divergenceFreeInputPolarizationB
    outputDivergenceFreePolarization

record ResonantTriad : Set where
  constructor resonantTriad
  field
    aDirection :
      Direction3
    bDirection :
      Direction3
    rho :
      PositiveScaleRatio
    cDirection :
      Direction3
    resonanceLaw :
      TriadResonanceLaw
    resonanceLawIsCanonical :
      resonanceLaw ≡ canonicalTriadResonanceLaw
    polarizations :
      TriadPolarizationPackage
    polarizationsAreCanonical :
      polarizations ≡ canonicalTriadPolarizations

open ResonantTriad public

canonicalResonantTriad : ResonantTriad
canonicalResonantTriad =
  resonantTriad
    canonicalInputA
    canonicalInputB
    canonicalRho
    canonicalOutputC
    canonicalTriadResonanceLaw
    refl
    canonicalTriadPolarizations
    refl

------------------------------------------------------------------------
-- True non-averaged Leray bilinear pieces.

data LerayProjectorComponent : Set where
  kroneckerDeltaTerm :
    LerayProjectorComponent
  outputRadialRankOneSubtraction :
    Direction3 →
    LerayProjectorComponent

data LerayProjector : Set where
  trueOutputLerayProjector :
    Direction3 →
    LerayProjectorComponent →
    LerayProjectorComponent →
    LerayProjector

canonicalLerayProjector : LerayProjector
canonicalLerayProjector =
  trueOutputLerayProjector
    canonicalOutputC
    kroneckerDeltaTerm
    (outputRadialRankOneSubtraction canonicalOutputC)

data BilinearDerivativeInput : Set where
  etaDerivativeOnSecondInput :
    Direction3 →
    BilinearDerivativeInput

data TrueNSBilinearSymbol : Set where
  trueNonAveragedLerayBilinearSymbol :
    LerayProjector →
    BilinearDerivativeInput →
    TriadPolarizationPackage →
    TrueNSBilinearSymbol

canonicalBilinearDerivativeInput : BilinearDerivativeInput
canonicalBilinearDerivativeInput =
  etaDerivativeOnSecondInput canonicalInputB

canonicalTrueNSBilinearSymbol : TrueNSBilinearSymbol
canonicalTrueNSBilinearSymbol =
  trueNonAveragedLerayBilinearSymbol
    canonicalLerayProjector
    canonicalBilinearDerivativeInput
    canonicalTriadPolarizations

data StretchingProjection : Set where
  outputMaximalStretchingProjection :
    Direction3 →
    Direction3 →
    PolarizationChannel →
    StretchingProjection

canonicalStretchingProjection : StretchingProjection
canonicalStretchingProjection =
  outputMaximalStretchingProjection
    canonicalOutputC
    maximalStretchingDirection
    stretchingChannelPolarization

data OrthogonalStretchingComplement : Set where
  oneMinusStretchingProjection :
    StretchingProjection →
    OrthogonalStretchingComplement

canonicalStretchingComplement : OrthogonalStretchingComplement
canonicalStretchingComplement =
  oneMinusStretchingProjection canonicalStretchingProjection

data SymbolAdjoint : Set where
  bilinearSymbolAdjoint :
    TrueNSBilinearSymbol →
    SymbolAdjoint

canonicalSymbolAdjoint : SymbolAdjoint
canonicalSymbolAdjoint =
  bilinearSymbolAdjoint canonicalTrueNSBilinearSymbol

data TriadicDefectLaplacian : Set where
  piNDaggerOneMinusPiNPi :
    StretchingProjection →
    SymbolAdjoint →
    OrthogonalStretchingComplement →
    TrueNSBilinearSymbol →
    StretchingProjection →
    TriadicDefectLaplacian

canonicalTriadicDefectLaplacian : TriadicDefectLaplacian
canonicalTriadicDefectLaplacian =
  piNDaggerOneMinusPiNPi
    canonicalStretchingProjection
    canonicalSymbolAdjoint
    canonicalStretchingComplement
    canonicalTrueNSBilinearSymbol
    canonicalStretchingProjection

data TriadicZeroModeEquation : Set where
  oneMinusPiNPiEqualsZeroTarget :
    OrthogonalStretchingComplement →
    TrueNSBilinearSymbol →
    StretchingProjection →
    TriadicZeroModeEquation

canonicalTriadicZeroModeEquationTarget : TriadicZeroModeEquation
canonicalTriadicZeroModeEquationTarget =
  oneMinusPiNPiEqualsZeroTarget
    canonicalStretchingComplement
    canonicalTrueNSBilinearSymbol
    canonicalStretchingProjection

------------------------------------------------------------------------
-- Algebraic zero-mode family targets.

data TangentialProjectionAtOutput : Set where
  tangentialProjectionAtC :
    Direction3 →
    Direction3 →
    TangentialProjectionAtOutput

canonicalTangentialProjectionOfA : TangentialProjectionAtOutput
canonicalTangentialProjectionOfA =
  tangentialProjectionAtC canonicalOutputC canonicalInputA

canonicalTangentialProjectionOfB : TangentialProjectionAtOutput
canonicalTangentialProjectionOfB =
  tangentialProjectionAtC canonicalOutputC canonicalInputB

data ZeroModeFamilyTarget : Set where
  familyIOutputVorticityParallelToPcB :
    Direction3 →
    TangentialProjectionAtOutput →
    ZeroModeFamilyTarget
  familyIIOutputVorticityOrthogonalToPcA :
    Direction3 →
    TangentialProjectionAtOutput →
    ZeroModeFamilyTarget
  cascadeClosedZeroModeOutputWidthTarget :
    ZeroModeFamilyTarget

canonicalZeroModeFamilyTargets : List ZeroModeFamilyTarget
canonicalZeroModeFamilyTargets =
  familyIOutputVorticityParallelToPcB
    outputVorticityDirection
    canonicalTangentialProjectionOfB
  ∷ familyIIOutputVorticityOrthogonalToPcA
    outputVorticityDirection
    canonicalTangentialProjectionOfA
  ∷ cascadeClosedZeroModeOutputWidthTarget
  ∷ []

zeroModeFamilyTargetCount : Nat
zeroModeFamilyTargetCount =
  listLength canonicalZeroModeFamilyTargets

zeroModeFamilyTargetCountIs3 :
  zeroModeFamilyTargetCount ≡ 3
zeroModeFamilyTargetCountIs3 =
  refl

------------------------------------------------------------------------
-- Tao averaged-NS falsifiability guard.

data AveragingGuardStatus : Set where
  trueSymbolUsesOutputLerayProjectorAtXiPlusEta :
    AveragingGuardStatus
  rotationalAveragingWouldThickenZeroModes :
    AveragingGuardStatus
  proofMustFailForTaoAveragedOperator :
    AveragingGuardStatus
  energyCancellationAloneIsInsufficient :
    AveragingGuardStatus

canonicalAveragingGuardStatuses : List AveragingGuardStatus
canonicalAveragingGuardStatuses =
  trueSymbolUsesOutputLerayProjectorAtXiPlusEta
  ∷ rotationalAveragingWouldThickenZeroModes
  ∷ proofMustFailForTaoAveragedOperator
  ∷ energyCancellationAloneIsInsufficient
  ∷ []

averagingGuardStatusCount : Nat
averagingGuardStatusCount =
  listLength canonicalAveragingGuardStatuses

averagingGuardStatusCountIs4 :
  averagingGuardStatusCount ≡ 4
averagingGuardStatusCountIs4 =
  refl

------------------------------------------------------------------------
-- Boundary ledger and fail-closed gates.

data TrueLerayTriadicSymbolRow : Set where
  resonantInteractionPhaseSpaceRow :
    TrueLerayTriadicSymbolRow
  outputDirectionNormalizeRhoAPlusBRow :
    TrueLerayTriadicSymbolRow
  divergenceFreePolarizationPackageRow :
    TrueLerayTriadicSymbolRow
  exactOutputLerayProjectorRow :
    TrueLerayTriadicSymbolRow
  trueNonAveragedBilinearSymbolRow :
    TrueLerayTriadicSymbolRow
  stretchingProjectionRow :
    TrueLerayTriadicSymbolRow
  triadicDefectLaplacianRow :
    TrueLerayTriadicSymbolRow
  zeroModeFamiliesIAndIITargetRow :
    TrueLerayTriadicSymbolRow
  cascadeClosedWidthTargetRow :
    TrueLerayTriadicSymbolRow
  taoAveragedNSFalsifiabilityGuardRow :
    TrueLerayTriadicSymbolRow
  downstreamLeakageTransferBlockedRow :
    TrueLerayTriadicSymbolRow

canonicalTrueLerayTriadicSymbolRows :
  List TrueLerayTriadicSymbolRow
canonicalTrueLerayTriadicSymbolRows =
  resonantInteractionPhaseSpaceRow
  ∷ outputDirectionNormalizeRhoAPlusBRow
  ∷ divergenceFreePolarizationPackageRow
  ∷ exactOutputLerayProjectorRow
  ∷ trueNonAveragedBilinearSymbolRow
  ∷ stretchingProjectionRow
  ∷ triadicDefectLaplacianRow
  ∷ zeroModeFamiliesIAndIITargetRow
  ∷ cascadeClosedWidthTargetRow
  ∷ taoAveragedNSFalsifiabilityGuardRow
  ∷ downstreamLeakageTransferBlockedRow
  ∷ []

trueLerayTriadicSymbolRowCount : Nat
trueLerayTriadicSymbolRowCount =
  listLength canonicalTrueLerayTriadicSymbolRows

trueLerayTriadicSymbolRowCountIs11 :
  trueLerayTriadicSymbolRowCount ≡ 11
trueLerayTriadicSymbolRowCountIs11 =
  refl

data TrueLerayTriadicFalseGate : Set where
  widthPositiveTheoremFalseGate :
    TrueLerayTriadicFalseGate
  cascadeClosedRigidityFalseGate :
    TrueLerayTriadicFalseGate
  abelTriadicMeasureConstructionFalseGate :
    TrueLerayTriadicFalseGate
  leakageSquareFunctionCoercivityFalseGate :
    TrueLerayTriadicFalseGate
  criticalResidualTransferFalseGate :
    TrueLerayTriadicFalseGate
  clayNavierStokesPromotionFalseGate :
    TrueLerayTriadicFalseGate

canonicalTrueLerayTriadicFalseGates :
  List TrueLerayTriadicFalseGate
canonicalTrueLerayTriadicFalseGates =
  widthPositiveTheoremFalseGate
  ∷ cascadeClosedRigidityFalseGate
  ∷ abelTriadicMeasureConstructionFalseGate
  ∷ leakageSquareFunctionCoercivityFalseGate
  ∷ criticalResidualTransferFalseGate
  ∷ clayNavierStokesPromotionFalseGate
  ∷ []

trueLerayTriadicFalseGateCount : Nat
trueLerayTriadicFalseGateCount =
  listLength canonicalTrueLerayTriadicFalseGates

trueLerayTriadicFalseGateCountIs6 :
  trueLerayTriadicFalseGateCount ≡ 6
trueLerayTriadicFalseGateCountIs6 =
  refl

record TrueLerayTriadicDefectSymbolBoundary : Set where
  constructor trueLerayTriadicDefectSymbolBoundary
  field
    resonantTriadCarrier :
      ResonantTriad
    resonantTriadCarrierIsCanonical :
      resonantTriadCarrier ≡ canonicalResonantTriad
    lerayProjector :
      LerayProjector
    lerayProjectorIsCanonical :
      lerayProjector ≡ canonicalLerayProjector
    bilinearSymbol :
      TrueNSBilinearSymbol
    bilinearSymbolIsCanonical :
      bilinearSymbol ≡ canonicalTrueNSBilinearSymbol
    stretchingProjection :
      StretchingProjection
    stretchingProjectionIsCanonical :
      stretchingProjection ≡ canonicalStretchingProjection
    triadicDefectLaplacian :
      TriadicDefectLaplacian
    triadicDefectLaplacianIsCanonical :
      triadicDefectLaplacian ≡ canonicalTriadicDefectLaplacian
    zeroModeEquationTarget :
      TriadicZeroModeEquation
    zeroModeEquationTargetIsCanonical :
      zeroModeEquationTarget ≡ canonicalTriadicZeroModeEquationTarget
    zeroModeFamilyTargets :
      List ZeroModeFamilyTarget
    zeroModeFamilyTargetsAreCanonical :
      zeroModeFamilyTargets ≡ canonicalZeroModeFamilyTargets
    zeroModeFamilyTargetCountField :
      Nat
    zeroModeFamilyTargetCountIs3Field :
      zeroModeFamilyTargetCountField ≡ 3
    averagingGuardStatuses :
      List AveragingGuardStatus
    averagingGuardStatusesAreCanonical :
      averagingGuardStatuses ≡ canonicalAveragingGuardStatuses
    averagingGuardStatusCountField :
      Nat
    averagingGuardStatusCountIs4Field :
      averagingGuardStatusCountField ≡ 4
    ledgerRows :
      List TrueLerayTriadicSymbolRow
    ledgerRowsAreCanonical :
      ledgerRows ≡ canonicalTrueLerayTriadicSymbolRows
    ledgerRowCount :
      Nat
    ledgerRowCountIs11 :
      ledgerRowCount ≡ 11
    falseGates :
      List TrueLerayTriadicFalseGate
    falseGatesAreCanonical :
      falseGates ≡ canonicalTrueLerayTriadicFalseGates
    falseGateCount :
      Nat
    falseGateCountIs6 :
      falseGateCount ≡ 6
    exactSymbolRecorded :
      Bool
    exactSymbolRecordedIsTrue :
      exactSymbolRecorded ≡ true
    taoGuardRecorded :
      Bool
    taoGuardRecordedIsTrue :
      taoGuardRecorded ≡ true
    widthProved :
      Bool
    widthProvedIsFalse :
      widthProved ≡ false
    leakageTransferProved :
      Bool
    leakageTransferProvedIsFalse :
      leakageTransferProved ≡ false
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

open TrueLerayTriadicDefectSymbolBoundary public

canonicalTrueLerayTriadicDefectSymbolBoundary :
  TrueLerayTriadicDefectSymbolBoundary
canonicalTrueLerayTriadicDefectSymbolBoundary =
  trueLerayTriadicDefectSymbolBoundary
    canonicalResonantTriad
    refl
    canonicalLerayProjector
    refl
    canonicalTrueNSBilinearSymbol
    refl
    canonicalStretchingProjection
    refl
    canonicalTriadicDefectLaplacian
    refl
    canonicalTriadicZeroModeEquationTarget
    refl
    canonicalZeroModeFamilyTargets
    refl
    zeroModeFamilyTargetCount
    refl
    canonicalAveragingGuardStatuses
    refl
    averagingGuardStatusCount
    refl
    canonicalTrueLerayTriadicSymbolRows
    refl
    trueLerayTriadicSymbolRowCount
    refl
    canonicalTrueLerayTriadicFalseGates
    refl
    trueLerayTriadicFalseGateCount
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

exactSymbolRecordedFlag : Bool
exactSymbolRecordedFlag =
  exactSymbolRecorded canonicalTrueLerayTriadicDefectSymbolBoundary

taoGuardRecordedFlag : Bool
taoGuardRecordedFlag =
  taoGuardRecorded canonicalTrueLerayTriadicDefectSymbolBoundary

widthProvedFlag : Bool
widthProvedFlag =
  widthProved canonicalTrueLerayTriadicDefectSymbolBoundary

leakageTransferProvedFlag : Bool
leakageTransferProvedFlag =
  leakageTransferProved canonicalTrueLerayTriadicDefectSymbolBoundary

clayNavierStokesPromotedFlag : Bool
clayNavierStokesPromotedFlag =
  clayNavierStokesPromoted canonicalTrueLerayTriadicDefectSymbolBoundary

exactSymbolRecordedFlagIsTrue :
  exactSymbolRecordedFlag ≡ true
exactSymbolRecordedFlagIsTrue =
  refl

taoGuardRecordedFlagIsTrue :
  taoGuardRecordedFlag ≡ true
taoGuardRecordedFlagIsTrue =
  refl

widthProvedFlagIsFalse :
  widthProvedFlag ≡ false
widthProvedFlagIsFalse =
  refl

leakageTransferProvedFlagIsFalse :
  leakageTransferProvedFlag ≡ false
leakageTransferProvedFlagIsFalse =
  refl

clayNavierStokesPromotedFlagIsFalse :
  clayNavierStokesPromotedFlag ≡ false
clayNavierStokesPromotedFlagIsFalse =
  refl

data TrueLerayTriadicDefectSymbolBlocker : Set where
  missingCascadeClosedZeroModeOutputWidth :
    TrueLerayTriadicDefectSymbolBlocker
  missingAbelTriadicDefectMeasure :
    TrueLerayTriadicDefectSymbolBlocker
  missingTriadicLeakageSquareFunctionCoercivity :
    TrueLerayTriadicDefectSymbolBlocker
  missingFullLocalDefectMonotonicityFromTriadicLeakage :
    TrueLerayTriadicDefectSymbolBlocker

canonicalTrueLerayTriadicDefectSymbolBlockers :
  List TrueLerayTriadicDefectSymbolBlocker
canonicalTrueLerayTriadicDefectSymbolBlockers =
  missingCascadeClosedZeroModeOutputWidth
  ∷ missingAbelTriadicDefectMeasure
  ∷ missingTriadicLeakageSquareFunctionCoercivity
  ∷ missingFullLocalDefectMonotonicityFromTriadicLeakage
  ∷ []

trueLerayTriadicDefectSymbolBlockerCount : Nat
trueLerayTriadicDefectSymbolBlockerCount =
  listLength canonicalTrueLerayTriadicDefectSymbolBlockers

trueLerayTriadicDefectSymbolBlockerCountIs4 :
  trueLerayTriadicDefectSymbolBlockerCount ≡ 4
trueLerayTriadicDefectSymbolBlockerCountIs4 =
  refl

-- No contradiction eliminator is supplied for the false gates.  This type is
-- present only to make the non-promotion boundary explicit.
clayNavierStokesPromotionContradictionBoundary :
  clayNavierStokesPromotedFlag ≡ true →
  ⊥
clayNavierStokesPromotionContradictionBoundary ()

summary : String
summary =
  "True non-averaged Leray triadic NS defect symbol recorded; width, leakage transfer, and Clay NS remain false."
