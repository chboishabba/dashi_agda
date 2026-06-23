module DASHI.Biology.RelationalChartDynamicsInterfaceResidualMachine where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyMemoryCompiledInverseBridge as CompiledInverse
import DASHI.Biology.FormalLayerExplanationBoundary as Boundary
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Biology.RelationalChartResidualMachine as Chart

------------------------------------------------------------------------
-- Typed dynamics / compiled-interface residual machine.
--
-- This module closes the compiler/interface gap without adding authority.
-- It composes the existing candidate-only chart residual machine, the
-- compiled-inverse surface, the explanation boundary, and the longitudinal
-- residual dynamics into one fail-closed typed interface surface.

data Never : Set where

data TypedInterfaceRoute : Set where
  candidateOnlyTypedInterfaceRoute : TypedInterfaceRoute
  guideCollapseRoute : TypedInterfaceRoute
  proofCollapseRoute : TypedInterfaceRoute
  compiledInversePromotionRoute : TypedInterfaceRoute
  residualPromotionRoute : TypedInterfaceRoute
  authorityPromotionRoute : TypedInterfaceRoute
  diagnosisRoute : TypedInterfaceRoute
  forceRoute : TypedInterfaceRoute

AdmissibleTypedInterfaceRoute : TypedInterfaceRoute → Set
AdmissibleTypedInterfaceRoute candidateOnlyTypedInterfaceRoute = ⊤
AdmissibleTypedInterfaceRoute guideCollapseRoute = Never
AdmissibleTypedInterfaceRoute proofCollapseRoute = Never
AdmissibleTypedInterfaceRoute compiledInversePromotionRoute = Never
AdmissibleTypedInterfaceRoute residualPromotionRoute = Never
AdmissibleTypedInterfaceRoute authorityPromotionRoute = Never
AdmissibleTypedInterfaceRoute diagnosisRoute = Never
AdmissibleTypedInterfaceRoute forceRoute = Never

guideCollapseRouteRejected :
  AdmissibleTypedInterfaceRoute guideCollapseRoute →
  Never
guideCollapseRouteRejected impossible = impossible

proofCollapseRouteRejected :
  AdmissibleTypedInterfaceRoute proofCollapseRoute →
  Never
proofCollapseRouteRejected impossible = impossible

compiledInversePromotionRouteRejected :
  AdmissibleTypedInterfaceRoute compiledInversePromotionRoute →
  Never
compiledInversePromotionRouteRejected impossible = impossible

residualPromotionRouteRejected :
  AdmissibleTypedInterfaceRoute residualPromotionRoute →
  Never
residualPromotionRouteRejected impossible = impossible

authorityPromotionRouteRejected :
  AdmissibleTypedInterfaceRoute authorityPromotionRoute →
  Never
authorityPromotionRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleTypedInterfaceRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

forceRouteRejected :
  AdmissibleTypedInterfaceRoute forceRoute →
  Never
forceRouteRejected impossible = impossible

data InterfaceStage : Set where
  explanationGuideStage : InterfaceStage
  typedProofStage : InterfaceStage
  compiledReceiptStage : InterfaceStage
  residualMachineStage : InterfaceStage
  empiricalCheckStage : InterfaceStage

data InterfaceResidualKind : Set where
  guideResidualKind : InterfaceResidualKind
  typedProofResidualKind : InterfaceResidualKind
  compiledReceiptResidualKind : InterfaceResidualKind
  residualMachineResidualKind : InterfaceResidualKind
  empiricalCheckResidualKind : InterfaceResidualKind

data InterfaceGateKind : Set where
  candidateOnlyInterfaceGate : InterfaceGateKind
  noPromotionInterfaceGate : InterfaceGateKind
  noForceInterfaceGate : InterfaceGateKind
  noAuthorityInterfaceGate : InterfaceGateKind
  noDiagnosisInterfaceGate : InterfaceGateKind
  noMindReadingInterfaceGate : InterfaceGateKind
  noHiddenChartRecoveryInterfaceGate : InterfaceGateKind

canonicalInterfaceStages : List InterfaceStage
canonicalInterfaceStages =
  explanationGuideStage
  ∷ typedProofStage
  ∷ compiledReceiptStage
  ∷ residualMachineStage
  ∷ empiricalCheckStage
  ∷ []

canonicalInterfaceResidualKinds : List InterfaceResidualKind
canonicalInterfaceResidualKinds =
  guideResidualKind
  ∷ typedProofResidualKind
  ∷ compiledReceiptResidualKind
  ∷ residualMachineResidualKind
  ∷ empiricalCheckResidualKind
  ∷ []

canonicalInterfaceGateKinds : List InterfaceGateKind
canonicalInterfaceGateKinds =
  candidateOnlyInterfaceGate
  ∷ noPromotionInterfaceGate
  ∷ noForceInterfaceGate
  ∷ noAuthorityInterfaceGate
  ∷ noDiagnosisInterfaceGate
  ∷ noMindReadingInterfaceGate
  ∷ noHiddenChartRecoveryInterfaceGate
  ∷ []

canonicalTypedInterfaceNotes : List String
canonicalTypedInterfaceNotes =
  "The interface remains candidate-only and does not promote authority"
  ∷ "Guide text may help readers reach the typed proof surface without collapsing layers"
  ∷ "The compiled inverse surface is a local receipt, not a promoted claim"
  ∷ "Residual machine readings stay chart-local and longitudinally indexed"
  ∷ "Diagnosis, force, mind-reading, and hidden-chart recovery stay blocked"
  ∷ []

record TypedInterfaceTranslationRow : Setω where
  constructor mkTypedInterfaceTranslationRow
  field
    rowIndex :
      Nat

    rowStage :
      InterfaceStage

    rowRouteKind :
      Boundary.RouteKind

    rowSourceLayer :
      Boundary.ExplanationLayer

    rowTargetLayer :
      Boundary.ExplanationLayer

    rowResidualKind :
      InterfaceResidualKind

    rowGateKinds :
      List InterfaceGateKind

    rowCompiledInverseSurface :
      CompiledInverse.BodyMemoryCompiledInverseBridgeSurface

    rowResidualMachine :
      Chart.RelationalChartResidualMachine

    rowResidualDynamics :
      Longitudinal.IntersectionalLongitudinalResidualDynamics

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowNoPromotion :
      Bool

    rowNoPromotionIsFalse :
      rowNoPromotion ≡ false

    rowNoForce :
      Bool

    rowNoForceIsFalse :
      rowNoForce ≡ false

    rowNoAuthority :
      Bool

    rowNoAuthorityIsFalse :
      rowNoAuthority ≡ false

    rowNoDiagnosis :
      Bool

    rowNoDiagnosisIsFalse :
      rowNoDiagnosis ≡ false

    rowReading :
      String

open TypedInterfaceTranslationRow public

mkTypedInterfaceTranslationRowOf :
  Nat →
  InterfaceStage →
  Boundary.RouteKind →
  InterfaceResidualKind →
  String →
  TypedInterfaceTranslationRow
mkTypedInterfaceTranslationRowOf index stage routeKind residualKind reading =
  mkTypedInterfaceTranslationRow
    index
    stage
    routeKind
    (Boundary.routeKindSourceLayer routeKind)
    (Boundary.routeKindTargetLayer routeKind)
    residualKind
    canonicalInterfaceGateKinds
    CompiledInverse.bodyMemoryCompiledInverseBridgeSurface
    Chart.canonicalRelationalChartResidualMachine
    Longitudinal.canonicalIntersectionalLongitudinalResidualDynamics
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
    reading

canonicalGuideTranslationRow : TypedInterfaceTranslationRow
canonicalGuideTranslationRow =
  mkTypedInterfaceTranslationRowOf
    zero
    explanationGuideStage
    Boundary.intuitiveGuideRoute
    guideResidualKind
    "guide-side explanation stays a guide while the typed proof surface remains ahead"

canonicalTypedProofTranslationRow : TypedInterfaceTranslationRow
canonicalTypedProofTranslationRow =
  mkTypedInterfaceTranslationRowOf
    (suc zero)
    typedProofStage
    Boundary.typedProofSurfaceRoute
    typedProofResidualKind
    "typed proof names the structure without turning it into authority"

canonicalCompiledReceiptTranslationRow : TypedInterfaceTranslationRow
canonicalCompiledReceiptTranslationRow =
  mkTypedInterfaceTranslationRowOf
    (suc (suc zero))
    compiledReceiptStage
    Boundary.typedProofSurfaceRoute
    compiledReceiptResidualKind
    "compiled inverse and chart residual receipts remain local and candidate-only"

canonicalResidualMachineTranslationRow : TypedInterfaceTranslationRow
canonicalResidualMachineTranslationRow =
  mkTypedInterfaceTranslationRowOf
    (suc (suc (suc zero)))
    residualMachineStage
    Boundary.typedProofSurfaceRoute
    residualMachineResidualKind
    "residual machine readings stay typed and fail-closed"

canonicalEmpiricalCheckTranslationRow : TypedInterfaceTranslationRow
canonicalEmpiricalCheckTranslationRow =
  mkTypedInterfaceTranslationRowOf
    (suc (suc (suc (suc zero))))
    empiricalCheckStage
    Boundary.typedProofSurfaceRoute
    empiricalCheckResidualKind
    "empirical checks can constrain the atlas but do not become a new authority"

record TypedInterfaceTranslationRows : Setω where
  constructor mkTypedInterfaceTranslationRows
  field
    guideTranslationRow :
      TypedInterfaceTranslationRow

    typedProofTranslationRow :
      TypedInterfaceTranslationRow

    compiledReceiptTranslationRow :
      TypedInterfaceTranslationRow

    residualMachineTranslationRow :
      TypedInterfaceTranslationRow

    empiricalCheckTranslationRow :
      TypedInterfaceTranslationRow

open TypedInterfaceTranslationRows public

canonicalTypedInterfaceTranslationRows : TypedInterfaceTranslationRows
canonicalTypedInterfaceTranslationRows =
  mkTypedInterfaceTranslationRows
    canonicalGuideTranslationRow
    canonicalTypedProofTranslationRow
    canonicalCompiledReceiptTranslationRow
    canonicalResidualMachineTranslationRow
    canonicalEmpiricalCheckTranslationRow

record RelationalChartDynamicsInterfaceResidualMachine : Setω where
  constructor mkRelationalChartDynamicsInterfaceResidualMachine
  field
    machineLabel :
      String

    machineRoute :
      TypedInterfaceRoute

    machineRouteIsCandidateOnly :
      machineRoute ≡ candidateOnlyTypedInterfaceRoute

    machineRouteAdmissible :
      AdmissibleTypedInterfaceRoute machineRoute

    machineBoundary :
      Boundary.FormalLayerExplanationBoundary

    machineCompiledInverseSurface :
      CompiledInverse.BodyMemoryCompiledInverseBridgeSurface

    machineResidualMachine :
      Chart.RelationalChartResidualMachine

    machineResidualDynamics :
      Longitudinal.IntersectionalLongitudinalResidualDynamics

    machineTranslationRows :
      TypedInterfaceTranslationRows

    machineCandidateOnly :
      Bool

    machineCandidateOnlyIsTrue :
      machineCandidateOnly ≡ true

    machineNoPromotion :
      Bool

    machineNoPromotionIsFalse :
      machineNoPromotion ≡ false

    machineNoForce :
      Bool

    machineNoForceIsFalse :
      machineNoForce ≡ false

    machineNoAuthority :
      Bool

    machineNoAuthorityIsFalse :
      machineNoAuthority ≡ false

    machineNoDiagnosis :
      Bool

    machineNoDiagnosisIsFalse :
      machineNoDiagnosis ≡ false

    machineReading :
      String

    machineNotes :
      List String

open RelationalChartDynamicsInterfaceResidualMachine public

canonicalRelationalChartDynamicsInterfaceResidualMachine :
  RelationalChartDynamicsInterfaceResidualMachine
canonicalRelationalChartDynamicsInterfaceResidualMachine =
  mkRelationalChartDynamicsInterfaceResidualMachine
    "typed dynamics / compiled-interface residual machine"
    candidateOnlyTypedInterfaceRoute
    refl
    tt
    Boundary.canonicalFormalLayerExplanationBoundary
    CompiledInverse.bodyMemoryCompiledInverseBridgeSurface
    Chart.canonicalRelationalChartResidualMachine
    Longitudinal.canonicalIntersectionalLongitudinalResidualDynamics
    canonicalTypedInterfaceTranslationRows
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
    "Candidate-only compiler/interface dynamics: guide, typed proof, compiled inverse, residual machine, and empirical check stay typed while authority stays blocked."
    canonicalTypedInterfaceNotes

canonicalMachineRouteIsCandidateOnly :
  machineRoute canonicalRelationalChartDynamicsInterfaceResidualMachine ≡
  candidateOnlyTypedInterfaceRoute
canonicalMachineRouteIsCandidateOnly =
  machineRouteIsCandidateOnly
    canonicalRelationalChartDynamicsInterfaceResidualMachine

canonicalMachineCandidateOnlyIsTrue :
  machineCandidateOnly
    canonicalRelationalChartDynamicsInterfaceResidualMachine
  ≡
  true
canonicalMachineCandidateOnlyIsTrue =
  machineCandidateOnlyIsTrue
    canonicalRelationalChartDynamicsInterfaceResidualMachine

canonicalMachineNoPromotionIsFalse :
  machineNoPromotion
    canonicalRelationalChartDynamicsInterfaceResidualMachine
  ≡
  false
canonicalMachineNoPromotionIsFalse =
  machineNoPromotionIsFalse
    canonicalRelationalChartDynamicsInterfaceResidualMachine

canonicalMachineNoForceIsFalse :
  machineNoForce
    canonicalRelationalChartDynamicsInterfaceResidualMachine
  ≡
  false
canonicalMachineNoForceIsFalse =
  machineNoForceIsFalse
    canonicalRelationalChartDynamicsInterfaceResidualMachine

canonicalMachineNoAuthorityIsFalse :
  machineNoAuthority
    canonicalRelationalChartDynamicsInterfaceResidualMachine
  ≡
  false
canonicalMachineNoAuthorityIsFalse =
  machineNoAuthorityIsFalse
    canonicalRelationalChartDynamicsInterfaceResidualMachine

canonicalMachineNoDiagnosisIsFalse :
  machineNoDiagnosis
    canonicalRelationalChartDynamicsInterfaceResidualMachine
  ≡
  false
canonicalMachineNoDiagnosisIsFalse =
  machineNoDiagnosisIsFalse
    canonicalRelationalChartDynamicsInterfaceResidualMachine

record RelationalChartDynamicsInterfaceResidualMachineSurface : Setω where
  field
    candidateRoute :
      TypedInterfaceRoute

    candidateRouteIsAdmissible :
      AdmissibleTypedInterfaceRoute candidateRoute

    machine :
      RelationalChartDynamicsInterfaceResidualMachine

    surfaceReading :
      String

canonicalRelationalChartDynamicsInterfaceResidualMachineSurface :
  RelationalChartDynamicsInterfaceResidualMachineSurface
canonicalRelationalChartDynamicsInterfaceResidualMachineSurface = record
  { candidateRoute = candidateOnlyTypedInterfaceRoute
  ; candidateRouteIsAdmissible = tt
  ; machine = canonicalRelationalChartDynamicsInterfaceResidualMachine
  ; surfaceReading =
      "Typed dynamics / compiled-interface residual machine: candidate-only guide, typed proof, compiled inverse, residual machine, and empirical check surfaces remain fail-closed with no promotion, no force, and no authority."
  }
