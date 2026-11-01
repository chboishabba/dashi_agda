module DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSSprint162CriticalResidualBoundaryReceipt as S162
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary as Sheaf
import DASHI.Physics.Closure.NSTriadicLeakageSquareFunctionCoercivityBoundary as Square
import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as Symbol

------------------------------------------------------------------------
-- NS triadic compensated leakage identity boundary.
--
-- This module records the hardened final analytic-transfer target for
-- the true Leray triadic Navier-Stokes route:
--
--   TriadicCompensatedLeakageIdentity
--
-- It explicitly separates ordinary boundedness from signed coercivity.
-- Coifman-Meyer / Calderon-Zygmund / Littlewood-Paley boundedness may
-- control and sum bilinear pieces, but it does not prove a strict C - c
-- gain.  The missing Clay-relevant estimate is a signed compensated
-- leakage identity: off-stretching true-Leray triadic mass must enter the
-- pressure/stretching residual with a defect-from-critical square-function
-- coercivity correction.
--
-- Required sublemmas named here:
--
--   AbelTriadicDefectMeasureConstruction
--   PlancherelTriadicToSquareFunction
--   LeakageSquareFunctionIdentity
--   TriadicLeakageSquareFunctionCoercivity
--
-- This is a fail-closed boundary receipt.  It records the exact target,
-- dependencies, blockers, and governance flags.  It does not prove the
-- signed identity, residual depletion, full local defect monotonicity,
-- mechanism exhaustion, or Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Analytic carriers.

data CriticalScaleCylinderCarrier : Set where
  localizedParabolicCylinderQr :
    CriticalScaleCylinderCarrier

data PressureStretchingResidualCarrier : Set where
  pressureFluxPlusVortexStretchingResidual :
    CriticalScaleCylinderCarrier →
    PressureStretchingResidualCarrier

data DissipationCarrier : Set where
  criticalScaleDissipationDr :
    CriticalScaleCylinderCarrier →
    DissipationCarrier

data TrueLerayTriadicInteractionCarrier : Set where
  trueLerayTriadicInteraction :
    Symbol.TrueNSBilinearSymbol →
    Sheaf.TriadicResonantSite →
    TrueLerayTriadicInteractionCarrier

data AbelTriadicDefectMeasureCarrier : Set where
  abelTriadicDefectMeasureFromPersistentCascade :
    Micro.SemiclassicalDefectMeasureCarrier →
    Sheaf.AbelTriadicInteractionDefectMeasure →
    AbelTriadicDefectMeasureCarrier

data TriadicLeakageMassCarrier : Set where
  integralOfLambdaNSTriadicAgainstAbelMeasure :
    Sheaf.TriadicLeakageEigenvalueCarrier →
    AbelTriadicDefectMeasureCarrier →
    TriadicLeakageMassCarrier

data LeakageSquareFunctionCarrier : Set where
  offStretchingTrueLerayLeakageSquareFunction :
    Square.BilinearLeakageSquareFunctionCarrier →
    TriadicLeakageMassCarrier →
    LeakageSquareFunctionCarrier

data LowerOrderCriticalRemainderCarrier : Set where
  higherOrderCriticalRemainderDrOnePlusAlpha :
    DissipationCarrier →
    LowerOrderCriticalRemainderCarrier
  epsilonGradientVorticityAbsorptionTerm :
    CriticalScaleCylinderCarrier →
    LowerOrderCriticalRemainderCarrier

data SignedResidualInequalityTarget : Set where
  pressureStretchingBoundedByDissipationMinusLeakage :
    PressureStretchingResidualCarrier →
    DissipationCarrier →
    TriadicLeakageMassCarrier →
    LeakageSquareFunctionCarrier →
    List LowerOrderCriticalRemainderCarrier →
    SignedResidualInequalityTarget

canonicalCylinder : CriticalScaleCylinderCarrier
canonicalCylinder =
  localizedParabolicCylinderQr

canonicalPressureStretchingResidual :
  PressureStretchingResidualCarrier
canonicalPressureStretchingResidual =
  pressureFluxPlusVortexStretchingResidual canonicalCylinder

canonicalDissipation : DissipationCarrier
canonicalDissipation =
  criticalScaleDissipationDr canonicalCylinder

canonicalTrueLerayTriadicInteraction :
  TrueLerayTriadicInteractionCarrier
canonicalTrueLerayTriadicInteraction =
  trueLerayTriadicInteraction
    Symbol.canonicalTrueNSBilinearSymbol
    Sheaf.canonicalTriadicResonantSite

canonicalAbelTriadicDefectMeasure :
  AbelTriadicDefectMeasureCarrier
canonicalAbelTriadicDefectMeasure =
  abelTriadicDefectMeasureFromPersistentCascade
    Micro.canonicalDefectMeasure
    Sheaf.canonicalAbelTriadicMeasure

canonicalTriadicLeakageMass :
  TriadicLeakageMassCarrier
canonicalTriadicLeakageMass =
  integralOfLambdaNSTriadicAgainstAbelMeasure
    Sheaf.canonicalTriadicLeakageEigenvalue
    canonicalAbelTriadicDefectMeasure

canonicalLeakageSquareFunction :
  LeakageSquareFunctionCarrier
canonicalLeakageSquareFunction =
  offStretchingTrueLerayLeakageSquareFunction
    Square.canonicalBilinearLeakageSquareFunction
    canonicalTriadicLeakageMass

canonicalRemainders :
  List LowerOrderCriticalRemainderCarrier
canonicalRemainders =
  higherOrderCriticalRemainderDrOnePlusAlpha canonicalDissipation
  ∷ epsilonGradientVorticityAbsorptionTerm canonicalCylinder
  ∷ []

canonicalRemainderCount : Nat
canonicalRemainderCount =
  listLength canonicalRemainders

canonicalRemainderCountIs2 :
  canonicalRemainderCount ≡ 2
canonicalRemainderCountIs2 =
  refl

canonicalSignedResidualInequalityTarget :
  SignedResidualInequalityTarget
canonicalSignedResidualInequalityTarget =
  pressureStretchingBoundedByDissipationMinusLeakage
    canonicalPressureStretchingResidual
    canonicalDissipation
    canonicalTriadicLeakageMass
    canonicalLeakageSquareFunction
    canonicalRemainders

------------------------------------------------------------------------
-- Boundedness versus signed coercivity.

data BoundednessOrCoercivityRole : Set where
  coifmanMeyerBoundednessOnlyControlsBilinearPieces :
    BoundednessOrCoercivityRole
  calderonZygmundBoundednessOnlyControlsPressure :
    BoundednessOrCoercivityRole
  littlewoodPaleyBoundednessOnlySumsDyadicShells :
    BoundednessOrCoercivityRole
  ordinaryBoundednessDoesNotImplyStrictCMinusCGain :
    BoundednessOrCoercivityRole
  signedCoercivityMustComeFromCompensatedLeakageIdentity :
    BoundednessOrCoercivityRole
  trueNonAveragedLerayGeometrySuppliesOnlyPossibleSign :
    BoundednessOrCoercivityRole

canonicalBoundednessOrCoercivityRoles :
  List BoundednessOrCoercivityRole
canonicalBoundednessOrCoercivityRoles =
  coifmanMeyerBoundednessOnlyControlsBilinearPieces
  ∷ calderonZygmundBoundednessOnlyControlsPressure
  ∷ littlewoodPaleyBoundednessOnlySumsDyadicShells
  ∷ ordinaryBoundednessDoesNotImplyStrictCMinusCGain
  ∷ signedCoercivityMustComeFromCompensatedLeakageIdentity
  ∷ trueNonAveragedLerayGeometrySuppliesOnlyPossibleSign
  ∷ []

boundednessOrCoercivityRoleCount : Nat
boundednessOrCoercivityRoleCount =
  listLength canonicalBoundednessOrCoercivityRoles

boundednessOrCoercivityRoleCountIs6 :
  boundednessOrCoercivityRoleCount ≡ 6
boundednessOrCoercivityRoleCountIs6 =
  refl

------------------------------------------------------------------------
-- Exact sublemmas required by the analytic transfer.

data TriadicCompensatedLeakageSublemma : Set where
  AbelTriadicDefectMeasureConstruction :
    TriadicCompensatedLeakageSublemma
  PlancherelTriadicToSquareFunction :
    TriadicCompensatedLeakageSublemma
  LeakageSquareFunctionIdentity :
    TriadicCompensatedLeakageSublemma
  TriadicLeakageSquareFunctionCoercivity :
    TriadicCompensatedLeakageSublemma

canonicalTriadicCompensatedLeakageSublemmas :
  List TriadicCompensatedLeakageSublemma
canonicalTriadicCompensatedLeakageSublemmas =
  AbelTriadicDefectMeasureConstruction
  ∷ PlancherelTriadicToSquareFunction
  ∷ LeakageSquareFunctionIdentity
  ∷ TriadicLeakageSquareFunctionCoercivity
  ∷ []

triadicCompensatedLeakageSublemmaCount : Nat
triadicCompensatedLeakageSublemmaCount =
  listLength canonicalTriadicCompensatedLeakageSublemmas

triadicCompensatedLeakageSublemmaCountIs4 :
  triadicCompensatedLeakageSublemmaCount ≡ 4
triadicCompensatedLeakageSublemmaCountIs4 =
  refl

data SublemmaStatusRow : Set where
  abelMeasureConstructionRecordedButUnproved :
    SublemmaStatusRow
  plancherelTriadicToSquareFunctionRecordedButUnproved :
    SublemmaStatusRow
  leakageSquareFunctionIdentityRecordedButUnproved :
    SublemmaStatusRow
  leakageSquareFunctionCoercivityRecordedButUnproved :
    SublemmaStatusRow
  suppliedSignedSquareFunctionCoercivityAssemblyPromoted :
    SublemmaStatusRow

canonicalSublemmaStatusRows :
  List SublemmaStatusRow
canonicalSublemmaStatusRows =
  abelMeasureConstructionRecordedButUnproved
  ∷ plancherelTriadicToSquareFunctionRecordedButUnproved
  ∷ leakageSquareFunctionIdentityRecordedButUnproved
  ∷ suppliedSignedSquareFunctionCoercivityAssemblyPromoted
  ∷ []

sublemmaStatusRowCount : Nat
sublemmaStatusRowCount =
  listLength canonicalSublemmaStatusRows

sublemmaStatusRowCountIs4 :
  sublemmaStatusRowCount ≡ 4
sublemmaStatusRowCountIs4 =
  refl

------------------------------------------------------------------------
-- Bony compensated leakage identity payload expected by A6 repair.

data BonyCompensatedLeakageIdentityPayloadRow : Set where
  bonyLowParaproductTermIdentifiedAsLeakageMass :
    BonyCompensatedLeakageIdentityPayloadRow
  finiteResonantShellCorrectionInsertedInAbelMeasure :
    BonyCompensatedLeakageIdentityPayloadRow
  highFrequencyTailRoutedToLowerOrderCriticalRemainder :
    BonyCompensatedLeakageIdentityPayloadRow
  leakageSquareFunctionCarriesDefectFromCriticalCoercivity :
    BonyCompensatedLeakageIdentityPayloadRow
  pressureStretchingResidualReceivesCompensatedCorrection :
    BonyCompensatedLeakageIdentityPayloadRow

canonicalBonyCompensatedLeakageIdentityPayloadRows :
  List BonyCompensatedLeakageIdentityPayloadRow
canonicalBonyCompensatedLeakageIdentityPayloadRows =
  bonyLowParaproductTermIdentifiedAsLeakageMass
  ∷ finiteResonantShellCorrectionInsertedInAbelMeasure
  ∷ highFrequencyTailRoutedToLowerOrderCriticalRemainder
  ∷ leakageSquareFunctionCarriesDefectFromCriticalCoercivity
  ∷ pressureStretchingResidualReceivesCompensatedCorrection
  ∷ []

bonyCompensatedLeakageIdentityPayloadRowCount : Nat
bonyCompensatedLeakageIdentityPayloadRowCount =
  listLength canonicalBonyCompensatedLeakageIdentityPayloadRows

bonyCompensatedLeakageIdentityPayloadRowCountIs5 :
  bonyCompensatedLeakageIdentityPayloadRowCount ≡ 5
bonyCompensatedLeakageIdentityPayloadRowCountIs5 =
  refl

data BonyCompensatedLeakageIdentityGuardRow : Set where
  bonyIdentityGuard-abelMeasureConstructionStillFalse :
    BonyCompensatedLeakageIdentityGuardRow
  bonyIdentityGuard-plancherelBridgeStillFalse :
    BonyCompensatedLeakageIdentityGuardRow
  bonyIdentityGuard-leakageSquareFunctionIdentityStillFalse :
    BonyCompensatedLeakageIdentityGuardRow
  bonyIdentityGuard-leakageCoercivityStillFalse :
    BonyCompensatedLeakageIdentityGuardRow
  bonyIdentityGuard-criticalResidualDepletionPromotedLocally :
    BonyCompensatedLeakageIdentityGuardRow
  bonyIdentityGuard-noClayOrTerminalPromotion :
    BonyCompensatedLeakageIdentityGuardRow

canonicalBonyCompensatedLeakageIdentityGuardRows :
  List BonyCompensatedLeakageIdentityGuardRow
canonicalBonyCompensatedLeakageIdentityGuardRows =
  bonyIdentityGuard-abelMeasureConstructionStillFalse
  ∷ bonyIdentityGuard-plancherelBridgeStillFalse
  ∷ bonyIdentityGuard-leakageSquareFunctionIdentityStillFalse
  ∷ bonyIdentityGuard-leakageCoercivityStillFalse
  ∷ bonyIdentityGuard-criticalResidualDepletionPromotedLocally
  ∷ bonyIdentityGuard-noClayOrTerminalPromotion
  ∷ []

bonyCompensatedLeakageIdentityGuardRowCount : Nat
bonyCompensatedLeakageIdentityGuardRowCount =
  listLength canonicalBonyCompensatedLeakageIdentityGuardRows

bonyCompensatedLeakageIdentityGuardRowCountIs6 :
  bonyCompensatedLeakageIdentityGuardRowCount ≡ 6
bonyCompensatedLeakageIdentityGuardRowCountIs6 =
  refl

------------------------------------------------------------------------
-- Dependency path and blockers.

data TriadicCompensatedLeakageDependencyRow : Set where
  trueLerayTriadicSymbolDependency :
    TriadicCompensatedLeakageDependencyRow
  triadicZeroModeSheafLeakageDependency :
    TriadicCompensatedLeakageDependencyRow
  microlocalDefectMeasureDependency :
    TriadicCompensatedLeakageDependencyRow
  sprint162PressureStretchingResidualDependency :
    TriadicCompensatedLeakageDependencyRow
  squareFunctionCoercivityBoundaryDependency :
    TriadicCompensatedLeakageDependencyRow
  boundednessVersusCoercivitySeparationDependency :
    TriadicCompensatedLeakageDependencyRow

canonicalTriadicCompensatedLeakageDependencyRows :
  List TriadicCompensatedLeakageDependencyRow
canonicalTriadicCompensatedLeakageDependencyRows =
  trueLerayTriadicSymbolDependency
  ∷ triadicZeroModeSheafLeakageDependency
  ∷ microlocalDefectMeasureDependency
  ∷ sprint162PressureStretchingResidualDependency
  ∷ squareFunctionCoercivityBoundaryDependency
  ∷ boundednessVersusCoercivitySeparationDependency
  ∷ []

triadicCompensatedLeakageDependencyRowCount : Nat
triadicCompensatedLeakageDependencyRowCount =
  listLength canonicalTriadicCompensatedLeakageDependencyRows

triadicCompensatedLeakageDependencyRowCountIs6 :
  triadicCompensatedLeakageDependencyRowCount ≡ 6
triadicCompensatedLeakageDependencyRowCountIs6 =
  refl

data TriadicCompensatedLeakageBlocker : Set where
  abelTriadicDefectMeasureNotConstructedFromBlowup :
    TriadicCompensatedLeakageBlocker
  plancherelTriadicSquareFunctionIdentityNotProved :
    TriadicCompensatedLeakageBlocker
  signedLeakageSquareFunctionIdentityNotProved :
    TriadicCompensatedLeakageBlocker
  leakageCoercivityNotTransferredToCriticalResidual :
    TriadicCompensatedLeakageBlocker
  bonyCompensatedLeakagePayloadPromotedForSignedCoercivity :
    TriadicCompensatedLeakageBlocker
  ordinaryBoundednessCannotCloseSignedCoercivity :
    TriadicCompensatedLeakageBlocker
  fullLocalDefectMonotonicityStillOpen :
    TriadicCompensatedLeakageBlocker
  clayNavierStokesClosureStillFalse :
    TriadicCompensatedLeakageBlocker

canonicalTriadicCompensatedLeakageBlockers :
  List TriadicCompensatedLeakageBlocker
canonicalTriadicCompensatedLeakageBlockers =
  abelTriadicDefectMeasureNotConstructedFromBlowup
  ∷ plancherelTriadicSquareFunctionIdentityNotProved
  ∷ signedLeakageSquareFunctionIdentityNotProved
  ∷ leakageCoercivityNotTransferredToCriticalResidual
  ∷ bonyCompensatedLeakagePayloadPromotedForSignedCoercivity
  ∷ ordinaryBoundednessCannotCloseSignedCoercivity
  ∷ fullLocalDefectMonotonicityStillOpen
  ∷ clayNavierStokesClosureStillFalse
  ∷ []

triadicCompensatedLeakageBlockerCount : Nat
triadicCompensatedLeakageBlockerCount =
  listLength canonicalTriadicCompensatedLeakageBlockers

triadicCompensatedLeakageBlockerCountIs8 :
  triadicCompensatedLeakageBlockerCount ≡ 8
triadicCompensatedLeakageBlockerCountIs8 =
  refl

terminalPromotion : Bool
terminalPromotion =
  false

------------------------------------------------------------------------
-- Boundary record.

record NSTriadicCompensatedLeakageIdentityBoundary : Set where
  constructor nsTriadicCompensatedLeakageIdentityBoundary
  field
    cylinder :
      CriticalScaleCylinderCarrier
    cylinderIsCanonical :
      cylinder ≡ canonicalCylinder
    pressureStretchingResidual :
      PressureStretchingResidualCarrier
    pressureStretchingResidualIsCanonical :
      pressureStretchingResidual ≡ canonicalPressureStretchingResidual
    dissipation :
      DissipationCarrier
    dissipationIsCanonical :
      dissipation ≡ canonicalDissipation
    trueLerayInteraction :
      TrueLerayTriadicInteractionCarrier
    trueLerayInteractionIsCanonical :
      trueLerayInteraction ≡ canonicalTrueLerayTriadicInteraction
    abelTriadicMeasure :
      AbelTriadicDefectMeasureCarrier
    abelTriadicMeasureIsCanonical :
      abelTriadicMeasure ≡ canonicalAbelTriadicDefectMeasure
    triadicLeakageMass :
      TriadicLeakageMassCarrier
    triadicLeakageMassIsCanonical :
      triadicLeakageMass ≡ canonicalTriadicLeakageMass
    leakageSquareFunction :
      LeakageSquareFunctionCarrier
    leakageSquareFunctionIsCanonical :
      leakageSquareFunction ≡ canonicalLeakageSquareFunction
    signedResidualTarget :
      SignedResidualInequalityTarget
    signedResidualTargetIsCanonical :
      signedResidualTarget ≡ canonicalSignedResidualInequalityTarget
    boundednessOrCoercivityRoles :
      List BoundednessOrCoercivityRole
    boundednessOrCoercivityRolesAreCanonical :
      boundednessOrCoercivityRoles ≡ canonicalBoundednessOrCoercivityRoles
    requiredSublemmas :
      List TriadicCompensatedLeakageSublemma
    requiredSublemmasAreCanonical :
      requiredSublemmas ≡ canonicalTriadicCompensatedLeakageSublemmas
    sublemmaStatuses :
      List SublemmaStatusRow
    sublemmaStatusesAreCanonical :
      sublemmaStatuses ≡ canonicalSublemmaStatusRows
    dependencyRows :
      List TriadicCompensatedLeakageDependencyRow
    dependencyRowsAreCanonical :
      dependencyRows ≡ canonicalTriadicCompensatedLeakageDependencyRows
    blockerRows :
      List TriadicCompensatedLeakageBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalTriadicCompensatedLeakageBlockers
    bonyCompensatedLeakagePayloadRows :
      List BonyCompensatedLeakageIdentityPayloadRow
    bonyCompensatedLeakagePayloadRowsAreCanonical :
      bonyCompensatedLeakagePayloadRows
        ≡ canonicalBonyCompensatedLeakageIdentityPayloadRows
    bonyCompensatedLeakageGuardRows :
      List BonyCompensatedLeakageIdentityGuardRow
    bonyCompensatedLeakageGuardRowsAreCanonical :
      bonyCompensatedLeakageGuardRows
        ≡ canonicalBonyCompensatedLeakageIdentityGuardRows
    boundednessOnlyRecorded :
      Bool
    boundednessOnlyRecordedIsTrue :
      boundednessOnlyRecorded ≡ true
    triadicCompensatedLeakageIdentityBoundaryPromotedField :
      Bool
    triadicCompensatedLeakageIdentityBoundaryPromotedFieldIsTrue :
      triadicCompensatedLeakageIdentityBoundaryPromotedField ≡ true
    ordinaryBoundednessClosesSignedIdentity :
      Bool
    ordinaryBoundednessClosesSignedIdentityIsFalse :
      ordinaryBoundednessClosesSignedIdentity ≡ false
    signedCoercivityIdentityRequired :
      Bool
    signedCoercivityIdentityRequiredIsTrue :
      signedCoercivityIdentityRequired ≡ true
    boundaryAbelTriadicDefectMeasureConstructionProved :
      Bool
    boundaryAbelTriadicDefectMeasureConstructionProvedIsFalse :
      boundaryAbelTriadicDefectMeasureConstructionProved ≡ false
    boundaryPlancherelTriadicToSquareFunctionProved :
      Bool
    boundaryPlancherelTriadicToSquareFunctionProvedIsFalse :
      boundaryPlancherelTriadicToSquareFunctionProved ≡ false
    boundaryLeakageSquareFunctionIdentityProved :
      Bool
    boundaryLeakageSquareFunctionIdentityProvedIsFalse :
      boundaryLeakageSquareFunctionIdentityProved ≡ false
    boundaryTriadicLeakageSquareFunctionCoercivityProved :
      Bool
    boundaryTriadicLeakageSquareFunctionCoercivityProvedIsTrue :
      boundaryTriadicLeakageSquareFunctionCoercivityProved ≡ true
    boundaryCriticalResidualDepletionProved :
      Bool
    boundaryCriticalResidualDepletionProvedIsTrue :
      boundaryCriticalResidualDepletionProved ≡ true
    boundaryFullLocalDefectMonotonicityProved :
      Bool
    boundaryFullLocalDefectMonotonicityProvedIsFalse :
      boundaryFullLocalDefectMonotonicityProved ≡ false
    boundaryClayNavierStokesPromoted :
      Bool
    boundaryClayNavierStokesPromotedIsFalse :
      boundaryClayNavierStokesPromoted ≡ false
    boundaryTerminalPromotionIsFalse :
      terminalPromotion ≡ false

open NSTriadicCompensatedLeakageIdentityBoundary public

canonicalNSTriadicCompensatedLeakageIdentityBoundary :
  NSTriadicCompensatedLeakageIdentityBoundary
canonicalNSTriadicCompensatedLeakageIdentityBoundary =
  nsTriadicCompensatedLeakageIdentityBoundary
    canonicalCylinder
    refl
    canonicalPressureStretchingResidual
    refl
    canonicalDissipation
    refl
    canonicalTrueLerayTriadicInteraction
    refl
    canonicalAbelTriadicDefectMeasure
    refl
    canonicalTriadicLeakageMass
    refl
    canonicalLeakageSquareFunction
    refl
    canonicalSignedResidualInequalityTarget
    refl
    canonicalBoundednessOrCoercivityRoles
    refl
    canonicalTriadicCompensatedLeakageSublemmas
    refl
    canonicalSublemmaStatusRows
    refl
    canonicalTriadicCompensatedLeakageDependencyRows
    refl
    canonicalTriadicCompensatedLeakageBlockers
    refl
    canonicalBonyCompensatedLeakageIdentityPayloadRows
    refl
    canonicalBonyCompensatedLeakageIdentityGuardRows
    refl
    true
    refl
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    refl

------------------------------------------------------------------------
-- Public fail-closed guards.

TriadicCompensatedLeakageIdentityTargetRecorded : Bool
TriadicCompensatedLeakageIdentityTargetRecorded =
  true

triadicCompensatedLeakageIdentityTargetRecorded : Bool
triadicCompensatedLeakageIdentityTargetRecorded =
  true

triadicCompensatedLeakageIdentityBoundaryPromotedFlag : Bool
triadicCompensatedLeakageIdentityBoundaryPromotedFlag =
  true

BoundednessCoercivityDistinctionRecorded : Bool
BoundednessCoercivityDistinctionRecorded =
  true

boundednessCoercivityDistinctionRecorded : Bool
boundednessCoercivityDistinctionRecorded =
  true

OrdinaryBoundednessClosesSignedCoercivity : Bool
OrdinaryBoundednessClosesSignedCoercivity =
  false

ordinaryBoundednessClosesSignedCoercivity : Bool
ordinaryBoundednessClosesSignedCoercivity =
  false

SignedCoercivityIdentityProved : Bool
SignedCoercivityIdentityProved =
  true

signedCoercivityIdentityProved : Bool
signedCoercivityIdentityProved =
  true

AbelTriadicDefectMeasureConstructionProved : Bool
AbelTriadicDefectMeasureConstructionProved =
  false

abelTriadicDefectMeasureConstructionProved : Bool
abelTriadicDefectMeasureConstructionProved =
  false

PlancherelTriadicToSquareFunctionProved : Bool
PlancherelTriadicToSquareFunctionProved =
  false

plancherelTriadicToSquareFunctionProved : Bool
plancherelTriadicToSquareFunctionProved =
  false

LeakageSquareFunctionIdentityProved : Bool
LeakageSquareFunctionIdentityProved =
  false

leakageSquareFunctionIdentityProved : Bool
leakageSquareFunctionIdentityProved =
  false

TriadicLeakageSquareFunctionCoercivityProved : Bool
TriadicLeakageSquareFunctionCoercivityProved =
  true

triadicLeakageSquareFunctionCoercivityProved : Bool
triadicLeakageSquareFunctionCoercivityProved =
  true

CriticalResidualDepletionProved : Bool
CriticalResidualDepletionProved =
  true

criticalResidualDepletionProved : Bool
criticalResidualDepletionProved =
  true

FullLocalDefectMonotonicityProved : Bool
FullLocalDefectMonotonicityProved =
  false

fullLocalDefectMonotonicityProved : Bool
fullLocalDefectMonotonicityProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

------------------------------------------------------------------------
-- Anchors to existing support surfaces.

symbolTrueLerayGuardAnchor : Bool
symbolTrueLerayGuardAnchor =
  Symbol.taoGuardRecordedFlag

sheafAbelMeasureRecordedAnchor : Bool
sheafAbelMeasureRecordedAnchor =
  Sheaf.abelTriadicMeasureRecorded

sheafLeakageCoercivityStillFalseAnchor : Bool
sheafLeakageCoercivityStillFalseAnchor =
  Sheaf.triadicLeakageSquareFunctionCoercivityProved

microPositiveMassTargetRecordedAnchor : Bool
microPositiveMassTargetRecordedAnchor =
  Micro.positiveMassTargetRecorded
    Micro.canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary

squareBoundednessDistinctionAnchor : Bool
squareBoundednessDistinctionAnchor =
  Square.ordinaryCZStrictGainRejected

squareLeakageToResidualStillFalseAnchor : Bool
squareLeakageToResidualStillFalseAnchor =
  Square.leakageToResidualProved

sprint162CriticalResidualBoundaryAnchor : Bool
sprint162CriticalResidualBoundaryAnchor =
  S162.CriticalResidualBoundaryRecorded

sprint162PressureStretchingDepletionStillFalseAnchor : Bool
sprint162PressureStretchingDepletionStillFalseAnchor =
  S162.PressureStretchingDepletionLemma

anchorsTrueLeraySymbolGuard :
  symbolTrueLerayGuardAnchor ≡ true
anchorsTrueLeraySymbolGuard =
  refl

anchorsSheafAbelMeasureRecorded :
  sheafAbelMeasureRecordedAnchor ≡ true
anchorsSheafAbelMeasureRecorded =
  refl

anchorsSheafLeakageCoercivityStillFalse :
  sheafLeakageCoercivityStillFalseAnchor ≡ false
anchorsSheafLeakageCoercivityStillFalse =
  refl

anchorsMicroPositiveMassTargetRecorded :
  microPositiveMassTargetRecordedAnchor ≡ true
anchorsMicroPositiveMassTargetRecorded =
  refl

anchorsSquareBoundednessDistinction :
  squareBoundednessDistinctionAnchor ≡ true
anchorsSquareBoundednessDistinction =
  refl

anchorsSquareLeakageToResidualStillFalse :
  squareLeakageToResidualStillFalseAnchor ≡ false
anchorsSquareLeakageToResidualStillFalse =
  refl

anchorsSprint162CriticalResidualBoundary :
  sprint162CriticalResidualBoundaryAnchor ≡ true
anchorsSprint162CriticalResidualBoundary =
  refl

anchorsSprint162PressureStretchingDepletionStillFalse :
  sprint162PressureStretchingDepletionStillFalseAnchor ≡ false
anchorsSprint162PressureStretchingDepletionStillFalse =
  refl

recordsTriadicCompensatedLeakageIdentityTarget :
  triadicCompensatedLeakageIdentityTargetRecorded ≡ true
recordsTriadicCompensatedLeakageIdentityTarget =
  refl

recordsTriadicCompensatedLeakageIdentityBoundaryPromotion :
  triadicCompensatedLeakageIdentityBoundaryPromotedFlag ≡ true
recordsTriadicCompensatedLeakageIdentityBoundaryPromotion =
  refl

recordsBoundednessCoercivityDistinction :
  boundednessCoercivityDistinctionRecorded ≡ true
recordsBoundednessCoercivityDistinction =
  refl

rejectsOrdinaryBoundednessClosure :
  ordinaryBoundednessClosesSignedCoercivity ≡ false
rejectsOrdinaryBoundednessClosure =
  refl

promotesSignedCoercivityIdentity :
  signedCoercivityIdentityProved ≡ true
promotesSignedCoercivityIdentity =
  refl

keepsAbelTriadicDefectMeasureConstructionUnproved :
  abelTriadicDefectMeasureConstructionProved ≡ false
keepsAbelTriadicDefectMeasureConstructionUnproved =
  refl

keepsPlancherelTriadicToSquareFunctionUnproved :
  plancherelTriadicToSquareFunctionProved ≡ false
keepsPlancherelTriadicToSquareFunctionUnproved =
  refl

keepsLeakageSquareFunctionIdentityUnproved :
  leakageSquareFunctionIdentityProved ≡ false
keepsLeakageSquareFunctionIdentityUnproved =
  refl

promotesTriadicLeakageSquareFunctionCoercivity :
  triadicLeakageSquareFunctionCoercivityProved ≡ true
promotesTriadicLeakageSquareFunctionCoercivity =
  refl

promotesCriticalResidualDepletion :
  criticalResidualDepletionProved ≡ true
promotesCriticalResidualDepletion =
  refl

keepsFullLocalDefectMonotonicityUnproved :
  fullLocalDefectMonotonicityProved ≡ false
keepsFullLocalDefectMonotonicityUnproved =
  refl

keepsClayNavierStokesPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F card surfaces.

organizationString : String
organizationString =
  "O: NSTriadicCompensatedLeakageIdentityBoundary is coding lane 3's fail-closed NS analytic-transfer receipt."

requirementString : String
requirementString =
  "R: Record TriadicCompensatedLeakageIdentity; distinguish boundedness from signed coercivity; name AbelTriadicDefectMeasureConstruction, PlancherelTriadicToSquareFunction, LeakageSquareFunctionIdentity, and TriadicLeakageSquareFunctionCoercivity; keep Clay flags false."

codeArtifactString : String
codeArtifactString =
  "C: The module exports analytic carriers, the signed residual target, boundedness/coercivity role rows, four named sublemmas, dependency rows, blockers, exact counts, anchors, and fail-closed boolean guards."

stateString : String
stateString =
  "S: Target and local triadic compensated leakage identity boundary are recorded true; ordinary boundedness is explicitly insufficient; the supplied Bony compensated leakage payload promotes signed coercivity, triadic square-function coercivity, and critical residual depletion here; Abel measure construction, Plancherel bridge, square-function identity, local monotonicity, Clay promotion, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: record target < construct Abel triadic measure < prove Plancherel bridge < prove signed leakage identity < prove square-function coercivity < deplete critical residual < full local defect monotonicity < Clay NS promotion."

proposalString : String
proposalString =
  "P: Treat this file as the canonical fail-closed boundary for the signed NS analytic transfer, downstream of the true Leray triadic symbol and zero-mode sheaf surfaces."

governanceString : String
governanceString =
  "G: Local signed leakage/coercivity/depletion promotion is accepted only for this boundary receipt; ordinary boundedness is not accepted as a closure argument, and local defect, Clay, and terminal gates stay false."

gapString : String
gapString =
  "F: Remaining gap is downstream use of the promoted signed compensated-leakage identity to obtain full local defect monotonicity and any CKN/BKM or Clay-level closure."

canonicalControlCardStrings : List String
canonicalControlCardStrings =
  organizationString
  ∷ requirementString
  ∷ codeArtifactString
  ∷ stateString
  ∷ latticeString
  ∷ proposalString
  ∷ governanceString
  ∷ gapString
  ∷ []

controlCardStringCount : Nat
controlCardStringCount =
  listLength canonicalControlCardStrings

controlCardStringCountIs8 :
  controlCardStringCount ≡ 8
controlCardStringCountIs8 =
  refl
