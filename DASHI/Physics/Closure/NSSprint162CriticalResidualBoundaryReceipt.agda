module DASHI.Physics.Closure.NSSprint162CriticalResidualBoundaryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSSprint161MechanismExhaustionAnalyticAttemptBoundaryReceipt as S161

------------------------------------------------------------------------
-- Sprint 162 critical-residual boundary receipt.
--
-- Anchor:
--
--   Sprint 161 records the mechanism-exhaustion analytic attempt as a
--   scoped research map and keeps MechanismExhaustionForFullClayNS=false
--   plus all full Clay Navier-Stokes promotion flags false.
--
-- Purpose:
--
--   Sharpen the NSCriticalResidual boundary: the local-defect iteration
--   route is scoped, pressure-flux and stretching-alignment residuals are
--   typed as explicit residual terms, but no persistent-positive critical
--   residual removal, pressure/stretching depletion lemma, mechanism
--   exhaustion, or full Clay promotion is asserted.

sprint162CriticalResidualBoundaryLedgerClosed : Bool
sprint162CriticalResidualBoundaryLedgerClosed = true

sprint161MechanismExhaustionAnalyticAttemptBoundaryAnchor : Bool
sprint161MechanismExhaustionAnalyticAttemptBoundaryAnchor =
  S161.sprint161MechanismExhaustionAnalyticAttemptBoundaryLedgerClosed

sprint161MechanismExhaustionFalseAnchor : Bool
sprint161MechanismExhaustionFalseAnchor =
  S161.MechanismExhaustionForFullClayNS

CriticalResidualBoundaryRecorded : Bool
CriticalResidualBoundaryRecorded = true

LocalDefectIterationRouteScoped : Bool
LocalDefectIterationRouteScoped = true

PressureFluxResidualTyped : Bool
PressureFluxResidualTyped = true

StretchingAlignmentResidualTyped : Bool
StretchingAlignmentResidualTyped = true

NoPersistentPositiveNSCriticalResidual : Bool
NoPersistentPositiveNSCriticalResidual = false

PressureStretchingDepletionLemma : Bool
PressureStretchingDepletionLemma = false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  S161.MechanismExhaustionForFullClayNS

full_clay_ns_solved : Bool
full_clay_ns_solved = false

fullClayNSSolved : Bool
fullClayNSSolved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint162AnchorsSprint161Boundary :
  sprint161MechanismExhaustionAnalyticAttemptBoundaryAnchor ≡ true
sprint162AnchorsSprint161Boundary = refl

sprint162AnchorsSprint161MechanismExhaustionFalse :
  sprint161MechanismExhaustionFalseAnchor ≡ false
sprint162AnchorsSprint161MechanismExhaustionFalse = refl

sprint162RecordsCriticalResidualBoundary :
  CriticalResidualBoundaryRecorded ≡ true
sprint162RecordsCriticalResidualBoundary = refl

sprint162ScopesLocalDefectIterationRoute :
  LocalDefectIterationRouteScoped ≡ true
sprint162ScopesLocalDefectIterationRoute = refl

sprint162TypesPressureFluxResidual :
  PressureFluxResidualTyped ≡ true
sprint162TypesPressureFluxResidual = refl

sprint162TypesStretchingAlignmentResidual :
  StretchingAlignmentResidualTyped ≡ true
sprint162TypesStretchingAlignmentResidual = refl

sprint162KeepsNoPersistentPositiveResidualFalse :
  NoPersistentPositiveNSCriticalResidual ≡ false
sprint162KeepsNoPersistentPositiveResidualFalse = refl

sprint162KeepsPressureStretchingDepletionLemmaFalse :
  PressureStretchingDepletionLemma ≡ false
sprint162KeepsPressureStretchingDepletionLemmaFalse = refl

sprint162KeepsMechanismExhaustionFalse :
  MechanismExhaustionForFullClayNS ≡ false
sprint162KeepsMechanismExhaustionFalse = refl

sprint162KeepsFullClayNSSolvedSnakeFalse :
  full_clay_ns_solved ≡ false
sprint162KeepsFullClayNSSolvedSnakeFalse = refl

sprint162KeepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
sprint162KeepsFullClayNSSolvedFalse = refl

sprint162KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint162KeepsClayPromotionFalse = refl

data Sprint162ResidualTermRow : Set where
  pressureFluxCriticalResidual :
    Sprint162ResidualTermRow
  stretchingAlignmentCriticalResidual :
    Sprint162ResidualTermRow
  localDefectIterationResidual :
    Sprint162ResidualTermRow
  persistentPositiveCriticalResidualRemainder :
    Sprint162ResidualTermRow

canonicalSprint162ResidualTermRows :
  List Sprint162ResidualTermRow
canonicalSprint162ResidualTermRows =
  pressureFluxCriticalResidual
  ∷ stretchingAlignmentCriticalResidual
  ∷ localDefectIterationResidual
  ∷ persistentPositiveCriticalResidualRemainder
  ∷ []

sprint162ResidualTermRowCount : Nat
sprint162ResidualTermRowCount = 4

sprint162ResidualTermRowCountIsFour :
  sprint162ResidualTermRowCount ≡ 4
sprint162ResidualTermRowCountIsFour = refl

data Sprint162RouteRow : Set where
  anchorSprint161MechanismExhaustionBoundary :
    Sprint162RouteRow
  recordNSCriticalResidualBoundary :
    Sprint162RouteRow
  scopeLocalDefectIterationRoute :
    Sprint162RouteRow
  typePressureFluxResidualTerm :
    Sprint162RouteRow
  typeStretchingAlignmentResidualTerm :
    Sprint162RouteRow
  failCloseFullClayNavierStokes :
    Sprint162RouteRow

canonicalSprint162RouteRows :
  List Sprint162RouteRow
canonicalSprint162RouteRows =
  anchorSprint161MechanismExhaustionBoundary
  ∷ recordNSCriticalResidualBoundary
  ∷ scopeLocalDefectIterationRoute
  ∷ typePressureFluxResidualTerm
  ∷ typeStretchingAlignmentResidualTerm
  ∷ failCloseFullClayNavierStokes
  ∷ []

sprint162RouteRowCount : Nat
sprint162RouteRowCount = 6

sprint162RouteRowCountIsSix :
  sprint162RouteRowCount ≡ 6
sprint162RouteRowCountIsSix = refl

data Sprint162ObstructionRow : Set where
  noPersistentPositiveCriticalResidualRemoval :
    Sprint162ObstructionRow
  noPressureStretchingDepletionLemma :
    Sprint162ObstructionRow
  noMechanismExhaustionForFullClayNS :
    Sprint162ObstructionRow
  noFullClayNavierStokesSolution :
    Sprint162ObstructionRow
  noClayNavierStokesPromotion :
    Sprint162ObstructionRow

canonicalSprint162ObstructionRows :
  List Sprint162ObstructionRow
canonicalSprint162ObstructionRows =
  noPersistentPositiveCriticalResidualRemoval
  ∷ noPressureStretchingDepletionLemma
  ∷ noMechanismExhaustionForFullClayNS
  ∷ noFullClayNavierStokesSolution
  ∷ noClayNavierStokesPromotion
  ∷ []

sprint162ObstructionRowCount : Nat
sprint162ObstructionRowCount = 5

sprint162ObstructionRowCountIsFive :
  sprint162ObstructionRowCount ≡ 5
sprint162ObstructionRowCountIsFive = refl

data ChainACriticalResidualMathRow : Set where
  vorticityEnstrophyProductionIdentityRow :
    ChainACriticalResidualMathRow
  strainEvolutionIdentityRow :
    ChainACriticalResidualMathRow
  lambdaEigenvalueVariablesRow :
    ChainACriticalResidualMathRow
  tracefreeConstraintRow :
    ChainACriticalResidualMathRow
  qcritDirectionalPressureHessianRow :
    ChainACriticalResidualMathRow
  pressureStretchingDepletionImplicationRow :
    ChainACriticalResidualMathRow
  lambdaTwoDominanceInequalityRow :
    ChainACriticalResidualMathRow
  compressiveEigenvalueFailureRow :
    ChainACriticalResidualMathRow
  epsilonCritFunctionalRow :
    ChainACriticalResidualMathRow
  lyapunovInequalityRow :
    ChainACriticalResidualMathRow
  nonlinearRieszPressureBlockerRow :
    ChainACriticalResidualMathRow
  biotSavartStrainVorticityBlockerRow :
    ChainACriticalResidualMathRow

canonicalChainACriticalResidualMathRows :
  List ChainACriticalResidualMathRow
canonicalChainACriticalResidualMathRows =
  vorticityEnstrophyProductionIdentityRow
  ∷ strainEvolutionIdentityRow
  ∷ lambdaEigenvalueVariablesRow
  ∷ tracefreeConstraintRow
  ∷ qcritDirectionalPressureHessianRow
  ∷ pressureStretchingDepletionImplicationRow
  ∷ lambdaTwoDominanceInequalityRow
  ∷ compressiveEigenvalueFailureRow
  ∷ epsilonCritFunctionalRow
  ∷ lyapunovInequalityRow
  ∷ nonlinearRieszPressureBlockerRow
  ∷ biotSavartStrainVorticityBlockerRow
  ∷ []

sprint162ChainAMathRowCount : Nat
sprint162ChainAMathRowCount = 12

sprint162ChainAMathRowCountIsTwelve :
  sprint162ChainAMathRowCount ≡ 12
sprint162ChainAMathRowCountIsTwelve = refl

vorticityEnstrophyProductionText : String
vorticityEnstrophyProductionText =
  "Chain A production row: omega_t + u dot grad omega = S omega + nu Delta omega, hence the local enstrophy source is omega dot S omega before viscosity and flux terms."

strainEvolutionText : String
strainEvolutionText =
  "Chain A strain row: D_t S + S^2 + A^2 + Hess p = nu Delta S, with trace S = 0 and pressure Hessian coupled nonlocally to u tensor u."

lambdaEigenvalueVariablesText : String
lambdaEigenvalueVariablesText =
  "Variables row: lambda1 >= lambda2 >= lambda3 are the ordered eigenvalues of the symmetric strain tensor S at the critical point or localized packet."

tracefreeConstraintText : String
tracefreeConstraintText =
  "Tracefree constraint row: lambda1 + lambda2 + lambda3 = 0, so persistent positive stretching must be reconciled with one compressive eigenvalue."

qcritDirectionalPressureHessianText : String
qcritDirectionalPressureHessianText =
  "Qcrit pressure Hessian row: at the critical direction e_i, the pressure contribution is e_i dot Hess p e_i; no sign is available without a nonlinear Riesz estimate."

depletionImplicationText : String
depletionImplicationText =
  "Depletion implication row: PressureStretchingDepletionLemma would have to convert pressure-Hessian/strain coupling into a strict negative margin against omega dot S omega at every persistent-positive critical packet."

lambdaTwoDominanceInequalityText : String
lambdaTwoDominanceInequalityText =
  "lambda2 dominance inequality row: the needed shape is lambda2-positive stretching <= pressure-depletion margin + viscous/localization absorbable errors, uniformly at the critical scale."

compressiveEigenvalueFailureText : String
compressiveEigenvalueFailureText =
  "Compressive-eigenvalue failure row: lambda3 < 0 from tracefree strain does not by itself force depletion of omega dot S omega, because omega may align with the lambda1 direction."

epsilonCritFunctionalText : String
epsilonCritFunctionalText =
  "epsilon_crit functional row: epsilon_crit must be a positive functional of the localized strain spectrum, pressure Hessian directional deficit, viscosity scale, and commutator margins."

lyapunovInequalityText : String
lyapunovInequalityText =
  "Lyapunov inequality row: NoPersistentPositiveNSCriticalResidual would require d/dt Phi_crit <= - epsilon_crit Phi_crit + absorbable lower-order terms on all persistent-positive residual windows."

nonlinearRieszPressureBlockerText : String
nonlinearRieszPressureBlockerText =
  "Open nonlinear Riesz blocker row: Hess p = R_i R_j of nonlinear velocity products is nonlocal and sign-indefinite, so the directional pressure-depletion estimate is still missing."

biotSavartStrainVorticityBlockerText : String
biotSavartStrainVorticityBlockerText =
  "Open Biot-Savart blocker row: S recovered from omega through singular integral Biot-Savart geometry does not yet give a closed alignment/depletion inequality for omega dot S omega."

canonicalChainACriticalResidualMathTexts : List String
canonicalChainACriticalResidualMathTexts =
  vorticityEnstrophyProductionText
  ∷ strainEvolutionText
  ∷ lambdaEigenvalueVariablesText
  ∷ tracefreeConstraintText
  ∷ qcritDirectionalPressureHessianText
  ∷ depletionImplicationText
  ∷ lambdaTwoDominanceInequalityText
  ∷ compressiveEigenvalueFailureText
  ∷ epsilonCritFunctionalText
  ∷ lyapunovInequalityText
  ∷ nonlinearRieszPressureBlockerText
  ∷ biotSavartStrainVorticityBlockerText
  ∷ []

record PressureStretchingDepletionLemmaExactShape : Set where
  constructor pressureStretchingDepletionLemmaExactShape
  field
    lemmaName :
      String
    lemmaNameIsCanonical :
      lemmaName ≡ "PressureStretchingDepletionLemma"
    lemmaPromoted :
      Bool
    lemmaPromotedIsFalse :
      lemmaPromoted ≡ false
    depletionMathRows :
      List ChainACriticalResidualMathRow
    depletionMathRowsAreCanonical :
      depletionMathRows ≡ canonicalChainACriticalResidualMathRows
    depletionMathTexts :
      List String
    depletionMathTextsAreCanonical :
      depletionMathTexts ≡ canonicalChainACriticalResidualMathTexts
    targetImplication :
      String
    targetImplicationIsCanonical :
      targetImplication ≡ depletionImplicationText
    lambdaDominanceInequality :
      String
    lambdaDominanceInequalityIsCanonical :
      lambdaDominanceInequality ≡ lambdaTwoDominanceInequalityText
    epsilonCritFunctional :
      String
    epsilonCritFunctionalIsCanonical :
      epsilonCritFunctional ≡ epsilonCritFunctionalText
    pressureHessianBlocker :
      String
    pressureHessianBlockerIsCanonical :
      pressureHessianBlocker ≡ nonlinearRieszPressureBlockerText
    biotSavartBlocker :
      String
    biotSavartBlockerIsCanonical :
      biotSavartBlocker ≡ biotSavartStrainVorticityBlockerText
    gateFalseField :
      PressureStretchingDepletionLemma ≡ false

open PressureStretchingDepletionLemmaExactShape public

canonicalPressureStretchingDepletionLemmaExactShape :
  PressureStretchingDepletionLemmaExactShape
canonicalPressureStretchingDepletionLemmaExactShape =
  pressureStretchingDepletionLemmaExactShape
    "PressureStretchingDepletionLemma"
    refl
    false
    refl
    canonicalChainACriticalResidualMathRows
    refl
    canonicalChainACriticalResidualMathTexts
    refl
    depletionImplicationText
    refl
    lambdaTwoDominanceInequalityText
    refl
    epsilonCritFunctionalText
    refl
    nonlinearRieszPressureBlockerText
    refl
    biotSavartStrainVorticityBlockerText
    refl
    refl

record NoPersistentPositiveNSCriticalResidualExactShape : Set where
  constructor noPersistentPositiveNSCriticalResidualExactShape
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ "NoPersistentPositiveNSCriticalResidual"
    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false
    residualMathRows :
      List ChainACriticalResidualMathRow
    residualMathRowsAreCanonical :
      residualMathRows ≡ canonicalChainACriticalResidualMathRows
    residualMathTexts :
      List String
    residualMathTextsAreCanonical :
      residualMathTexts ≡ canonicalChainACriticalResidualMathTexts
    productionRowText :
      String
    productionRowTextIsCanonical :
      productionRowText ≡ vorticityEnstrophyProductionText
    strainRowText :
      String
    strainRowTextIsCanonical :
      strainRowText ≡ strainEvolutionText
    eigenvalueVariables :
      String
    eigenvalueVariablesAreCanonical :
      eigenvalueVariables ≡ lambdaEigenvalueVariablesText
    tracefreeConstraint :
      String
    tracefreeConstraintIsCanonical :
      tracefreeConstraint ≡ tracefreeConstraintText
    qcritDirectionalPressureHessian :
      String
    qcritDirectionalPressureHessianIsCanonical :
      qcritDirectionalPressureHessian ≡ qcritDirectionalPressureHessianText
    compressiveEigenvalueFailure :
      String
    compressiveEigenvalueFailureIsCanonical :
      compressiveEigenvalueFailure ≡ compressiveEigenvalueFailureText
    lyapunovInequality :
      String
    lyapunovInequalityIsCanonical :
      lyapunovInequality ≡ lyapunovInequalityText
    requiredDepletionShape :
      PressureStretchingDepletionLemmaExactShape
    requiredDepletionShapeIsCanonical :
      requiredDepletionShape ≡
        canonicalPressureStretchingDepletionLemmaExactShape
    gateFalseField :
      NoPersistentPositiveNSCriticalResidual ≡ false

open NoPersistentPositiveNSCriticalResidualExactShape public

canonicalNoPersistentPositiveNSCriticalResidualExactShape :
  NoPersistentPositiveNSCriticalResidualExactShape
canonicalNoPersistentPositiveNSCriticalResidualExactShape =
  noPersistentPositiveNSCriticalResidualExactShape
    "NoPersistentPositiveNSCriticalResidual"
    refl
    false
    refl
    canonicalChainACriticalResidualMathRows
    refl
    canonicalChainACriticalResidualMathTexts
    refl
    vorticityEnstrophyProductionText
    refl
    strainEvolutionText
    refl
    lambdaEigenvalueVariablesText
    refl
    tracefreeConstraintText
    refl
    qcritDirectionalPressureHessianText
    refl
    compressiveEigenvalueFailureText
    refl
    lyapunovInequalityText
    refl
    canonicalPressureStretchingDepletionLemmaExactShape
    refl
    refl

organizationString : String
organizationString =
  "O: Sprint162 is a Chain A critical-residual boundary receipt anchored to Sprint161 mechanism-exhaustion analytic-attempt boundary."

requirementString : String
requirementString =
  "R: Record the sharpened NSCriticalResidual boundary, scope local-defect iteration, type pressure-flux and stretching-alignment residuals, and expose exact fail-closed shapes for PressureStretchingDepletionLemma and NoPersistentPositiveNSCriticalResidual."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports requested booleans, residual term rows, route rows, obstruction rows, Chain A math rows/texts, exact-shape records, counts, proofs, and a canonical receipt record."

stateString : String
stateString =
  "S: CriticalResidualBoundaryRecorded=true; Chain A rows are importable; LocalDefectIterationRouteScoped=true; PressureFluxResidualTyped=true; StretchingAlignmentResidualTyped=true; all Clay promotion and depletion flags remain false."

latticeString : String
latticeString =
  "L: Sprint161 analytic boundary -> Sprint162 NSCriticalResidual boundary -> vorticity/strain/eigenvalue rows -> pressure-stretching depletion target -> scoped local-defect iteration route -> explicit obstruction ledger."

proposalString : String
proposalString =
  "P: Treat the lambda-spectrum, Qcrit pressure Hessian, epsilon_crit, and Lyapunov rows as exact proof obligations only; do not infer depletion or full Clay closure."

governanceString : String
governanceString =
  "G: The Chain A critical-residual receipt is fail-closed: NoPersistentPositiveNSCriticalResidual=false, PressureStretchingDepletionLemma=false, MechanismExhaustionForFullClayNS=false, and Clay promotion flags stay false."

gapString : String
gapString =
  "F: The remaining gap is the open nonlinear Riesz/Biot-Savart pressure-stretching depletion estimate eliminating persistent positive NS critical residuals."

record Sprint162ORCSLPGF : Set where
  constructor sprint162ORCSLPGF
  field
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

open Sprint162ORCSLPGF public

canonicalSprint162ORCSLPGF : Sprint162ORCSLPGF
canonicalSprint162ORCSLPGF =
  sprint162ORCSLPGF
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

record NSSprint162CriticalResidualBoundaryReceipt : Set where
  constructor nsSprint162CriticalResidualBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "CriticalResidualBoundary"
    anchorName :
      String
    anchorNameIsCanonical :
      anchorName ≡
        "NSSprint161MechanismExhaustionAnalyticAttemptBoundaryReceipt"
    orcslpgf :
      Sprint162ORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalSprint162ORCSLPGF
    residualTerms :
      List Sprint162ResidualTermRow
    residualTermsAreCanonical :
      residualTerms ≡ canonicalSprint162ResidualTermRows
    routes :
      List Sprint162RouteRow
    routesAreCanonical :
      routes ≡ canonicalSprint162RouteRows
    obstructions :
      List Sprint162ObstructionRow
    obstructionsAreCanonical :
      obstructions ≡ canonicalSprint162ObstructionRows
    chainAMathRows :
      List ChainACriticalResidualMathRow
    chainAMathRowsAreCanonical :
      chainAMathRows ≡ canonicalChainACriticalResidualMathRows
    chainAMathTexts :
      List String
    chainAMathTextsAreCanonical :
      chainAMathTexts ≡ canonicalChainACriticalResidualMathTexts
    pressureStretchingDepletionShape :
      PressureStretchingDepletionLemmaExactShape
    pressureStretchingDepletionShapeIsCanonical :
      pressureStretchingDepletionShape ≡
        canonicalPressureStretchingDepletionLemmaExactShape
    noPersistentPositiveResidualShape :
      NoPersistentPositiveNSCriticalResidualExactShape
    noPersistentPositiveResidualShapeIsCanonical :
      noPersistentPositiveResidualShape ≡
        canonicalNoPersistentPositiveNSCriticalResidualExactShape
    criticalResidualBoundaryRecordedField :
      CriticalResidualBoundaryRecorded ≡ true
    localDefectIterationRouteScopedField :
      LocalDefectIterationRouteScoped ≡ true
    pressureFluxResidualTypedField :
      PressureFluxResidualTyped ≡ true
    stretchingAlignmentResidualTypedField :
      StretchingAlignmentResidualTyped ≡ true
    noPersistentPositiveNSCriticalResidualFalseField :
      NoPersistentPositiveNSCriticalResidual ≡ false
    pressureStretchingDepletionLemmaFalseField :
      PressureStretchingDepletionLemma ≡ false
    mechanismExhaustionForFullClayNSFalseField :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedSnakeFalseField :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalseField :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalseField :
      clayNavierStokesPromoted ≡ false
    residualTermRowCountField :
      sprint162ResidualTermRowCount ≡ 4
    routeRowCountField :
      sprint162RouteRowCount ≡ 6
    obstructionRowCountField :
      sprint162ObstructionRowCount ≡ 5
    chainAMathRowCountField :
      sprint162ChainAMathRowCount ≡ 12

open NSSprint162CriticalResidualBoundaryReceipt public

canonicalNSSprint162CriticalResidualBoundaryReceipt :
  NSSprint162CriticalResidualBoundaryReceipt
canonicalNSSprint162CriticalResidualBoundaryReceipt =
  nsSprint162CriticalResidualBoundaryReceipt
    "CriticalResidualBoundary"
    refl
    "NSSprint161MechanismExhaustionAnalyticAttemptBoundaryReceipt"
    refl
    canonicalSprint162ORCSLPGF
    refl
    canonicalSprint162ResidualTermRows
    refl
    canonicalSprint162RouteRows
    refl
    canonicalSprint162ObstructionRows
    refl
    canonicalChainACriticalResidualMathRows
    refl
    canonicalChainACriticalResidualMathTexts
    refl
    canonicalPressureStretchingDepletionLemmaExactShape
    refl
    canonicalNoPersistentPositiveNSCriticalResidualExactShape
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
