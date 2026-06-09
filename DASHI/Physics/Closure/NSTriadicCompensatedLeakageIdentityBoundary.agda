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
-- pressure/stretching residual with a dissipative negative square-function
-- correction.
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

canonicalSublemmaStatusRows :
  List SublemmaStatusRow
canonicalSublemmaStatusRows =
  abelMeasureConstructionRecordedButUnproved
  ∷ plancherelTriadicToSquareFunctionRecordedButUnproved
  ∷ leakageSquareFunctionIdentityRecordedButUnproved
  ∷ leakageSquareFunctionCoercivityRecordedButUnproved
  ∷ []

sublemmaStatusRowCount : Nat
sublemmaStatusRowCount =
  listLength canonicalSublemmaStatusRows

sublemmaStatusRowCountIs4 :
  sublemmaStatusRowCount ≡ 4
sublemmaStatusRowCountIs4 =
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
  ∷ ordinaryBoundednessCannotCloseSignedCoercivity
  ∷ fullLocalDefectMonotonicityStillOpen
  ∷ clayNavierStokesClosureStillFalse
  ∷ []

triadicCompensatedLeakageBlockerCount : Nat
triadicCompensatedLeakageBlockerCount =
  listLength canonicalTriadicCompensatedLeakageBlockers

triadicCompensatedLeakageBlockerCountIs7 :
  triadicCompensatedLeakageBlockerCount ≡ 7
triadicCompensatedLeakageBlockerCountIs7 =
  refl

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
    boundednessOnlyRecorded :
      Bool
    boundednessOnlyRecordedIsTrue :
      boundednessOnlyRecorded ≡ true
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
    boundaryTriadicLeakageSquareFunctionCoercivityProvedIsFalse :
      boundaryTriadicLeakageSquareFunctionCoercivityProved ≡ false
    boundaryCriticalResidualDepletionProved :
      Bool
    boundaryCriticalResidualDepletionProvedIsFalse :
      boundaryCriticalResidualDepletionProved ≡ false
    boundaryFullLocalDefectMonotonicityProved :
      Bool
    boundaryFullLocalDefectMonotonicityProvedIsFalse :
      boundaryFullLocalDefectMonotonicityProved ≡ false
    boundaryClayNavierStokesPromoted :
      Bool
    boundaryClayNavierStokesPromotedIsFalse :
      boundaryClayNavierStokesPromoted ≡ false

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
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Public fail-closed guards.

TriadicCompensatedLeakageIdentityTargetRecorded : Bool
TriadicCompensatedLeakageIdentityTargetRecorded =
  true

triadicCompensatedLeakageIdentityTargetRecorded : Bool
triadicCompensatedLeakageIdentityTargetRecorded =
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
  false

signedCoercivityIdentityProved : Bool
signedCoercivityIdentityProved =
  false

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
  false

triadicLeakageSquareFunctionCoercivityProved : Bool
triadicLeakageSquareFunctionCoercivityProved =
  false

CriticalResidualDepletionProved : Bool
CriticalResidualDepletionProved =
  false

criticalResidualDepletionProved : Bool
criticalResidualDepletionProved =
  false

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

terminalPromotion : Bool
terminalPromotion =
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

recordsBoundednessCoercivityDistinction :
  boundednessCoercivityDistinctionRecorded ≡ true
recordsBoundednessCoercivityDistinction =
  refl

rejectsOrdinaryBoundednessClosure :
  ordinaryBoundednessClosesSignedCoercivity ≡ false
rejectsOrdinaryBoundednessClosure =
  refl

keepsSignedCoercivityIdentityUnproved :
  signedCoercivityIdentityProved ≡ false
keepsSignedCoercivityIdentityUnproved =
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

keepsTriadicLeakageSquareFunctionCoercivityUnproved :
  triadicLeakageSquareFunctionCoercivityProved ≡ false
keepsTriadicLeakageSquareFunctionCoercivityUnproved =
  refl

keepsCriticalResidualDepletionUnproved :
  criticalResidualDepletionProved ≡ false
keepsCriticalResidualDepletionUnproved =
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
  "S: Target recorded; ordinary boundedness is explicitly insufficient; signed compensated leakage identity, Abel measure construction, Plancherel bridge, square-function identity, coercivity, residual depletion, local monotonicity, and Clay promotion remain false."

latticeString : String
latticeString =
  "L: record target < construct Abel triadic measure < prove Plancherel bridge < prove signed leakage identity < prove square-function coercivity < deplete critical residual < full local defect monotonicity < Clay NS promotion."

proposalString : String
proposalString =
  "P: Treat this file as the canonical fail-closed boundary for the signed NS analytic transfer, downstream of the true Leray triadic symbol and zero-mode sheaf surfaces."

governanceString : String
governanceString =
  "G: Promotion is blocked until all four named sublemmas and the residual-depletion transfer are proved; ordinary boundedness is not accepted as a closure argument."

gapString : String
gapString =
  "F: Gap is the missing signed compensated-leakage identity connecting triadic leakage mass to a negative pressure/stretching residual correction."

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
