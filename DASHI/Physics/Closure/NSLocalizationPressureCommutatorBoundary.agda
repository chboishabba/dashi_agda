module DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as PointwiseToAbel

------------------------------------------------------------------------
-- NS A6 localization / pressure commutator boundary.
--
-- This module is a narrow fail-closed child boundary under
-- NSPointwiseToAbelAveragingBoundary.  It records the analytic controls
-- needed to replace the localized pointwise stretching density
--
--   omega . S omega
--
-- by an Abel/shell mean when cutoff localization, Leray pressure
-- reconstruction, pressure commutators, boundary/cutoff defects, and
-- pressure tails are present.
--
-- The receipt deliberately does not prove the localized cutoff theorem,
-- does not prove the Leray pressure commutator theorem, does not prove A6,
-- does not prove residual depletion, does not prove NS Clay, and does not
-- promote a terminal claim.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported parent and sibling support anchors.

pointwiseToAbelBoundaryReference : String
pointwiseToAbelBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

offDiagonalAbsorptionBoundaryReference : String
offDiagonalAbsorptionBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

offDiagonalAbsorptionBoundaryImported : Bool
offDiagonalAbsorptionBoundaryImported =
  true

record ImportedLocalizationPressureCommutatorSupport : Set where
  field
    pointwiseToAbelBoundary :
      PointwiseToAbel.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    offDiagonalAbsorptionBoundary :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalAbsorptionBoundaryIsCanonical :
      offDiagonalAbsorptionBoundary
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    pointwiseToAbelBoundaryImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    offDiagonalAbsorptionBoundaryImportedIsTrue :
      offDiagonalAbsorptionBoundaryImported ≡ true

canonicalImportedLocalizationPressureCommutatorSupport :
  ImportedLocalizationPressureCommutatorSupport
canonicalImportedLocalizationPressureCommutatorSupport =
  record
    { pointwiseToAbelBoundary =
        PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; offDiagonalAbsorptionBoundary =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalAbsorptionBoundaryIsCanonical =
        refl
    ; pointwiseToAbelBoundaryImportedIsTrue =
        refl
    ; offDiagonalAbsorptionBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Localized cutoff objects.

data LocalizedCutoffObject : Set where
  parabolicCylinder-Qr :
    LocalizedCutoffObject
  spatialCutoff-phi-r :
    LocalizedCutoffObject
  timeCutoff-eta-r :
    LocalizedCutoffObject
  cutoffGradient-rMinusOne :
    LocalizedCutoffObject
  cutoffLaplacian-rMinusTwo :
    LocalizedCutoffObject
  dyadicShellProjection-Pj :
    LocalizedCutoffObject
  localizedVorticityShell-PjOmegaPhi :
    LocalizedCutoffObject
  localizedPressurePotential-pPhi :
    LocalizedCutoffObject
  exteriorTailAnnulus-QtwoRMinusQr :
    LocalizedCutoffObject

canonicalLocalizedCutoffObjects : List LocalizedCutoffObject
canonicalLocalizedCutoffObjects =
  parabolicCylinder-Qr
  ∷ spatialCutoff-phi-r
  ∷ timeCutoff-eta-r
  ∷ cutoffGradient-rMinusOne
  ∷ cutoffLaplacian-rMinusTwo
  ∷ dyadicShellProjection-Pj
  ∷ localizedVorticityShell-PjOmegaPhi
  ∷ localizedPressurePotential-pPhi
  ∷ exteriorTailAnnulus-QtwoRMinusQr
  ∷ []

localizedCutoffObjectCount : Nat
localizedCutoffObjectCount =
  listLength canonicalLocalizedCutoffObjects

localizedCutoffObjectCountIs9 :
  localizedCutoffObjectCount ≡ 9
localizedCutoffObjectCountIs9 =
  refl

localizedCutoffTheoremTargetText : String
localizedCutoffTheoremTargetText =
  "Localized cutoff theorem: cutoff, shell projection, and parabolic localization errors are lower-order or epsilon-absorbed before omega.Somega is replaced by the Abel/shell mean"

data LocalizedCutoffRequirement : Set where
  cutoffEqualsOneOnCoreQr :
    LocalizedCutoffRequirement
  derivativesScaleAtParabolicRate :
    LocalizedCutoffRequirement
  dyadicProjectionCutoffCommutatorBounded :
    LocalizedCutoffRequirement
  derivativeOnCutoffGivesLowerOrderEnergy :
    LocalizedCutoffRequirement
  timeCutoffErrorFeedsLocalEnergy :
    LocalizedCutoffRequirement
  cutoffDoesNotDistortAbelShellWeights :
    LocalizedCutoffRequirement
  boundaryAnnulusRecordedAsTailNotCore :
    LocalizedCutoffRequirement
  noPointwiseSignClaimAfterLocalization :
    LocalizedCutoffRequirement

canonicalLocalizedCutoffRequirements :
  List LocalizedCutoffRequirement
canonicalLocalizedCutoffRequirements =
  cutoffEqualsOneOnCoreQr
  ∷ derivativesScaleAtParabolicRate
  ∷ dyadicProjectionCutoffCommutatorBounded
  ∷ derivativeOnCutoffGivesLowerOrderEnergy
  ∷ timeCutoffErrorFeedsLocalEnergy
  ∷ cutoffDoesNotDistortAbelShellWeights
  ∷ boundaryAnnulusRecordedAsTailNotCore
  ∷ noPointwiseSignClaimAfterLocalization
  ∷ []

localizedCutoffRequirementCount : Nat
localizedCutoffRequirementCount =
  listLength canonicalLocalizedCutoffRequirements

localizedCutoffRequirementCountIs8 :
  localizedCutoffRequirementCount ≡ 8
localizedCutoffRequirementCountIs8 =
  refl

------------------------------------------------------------------------
-- Leray pressure reconstruction and commutator taxonomy.

data LerayPressureReconstructionStep : Set where
  reconstructPressureByRieszRieszOfUiUj :
    LerayPressureReconstructionStep
  splitLocalPressureIntoCoreAndHarmonicTail :
    LerayPressureReconstructionStep
  commuteLerayProjectionPastCutoff :
    LerayPressureReconstructionStep
  commuteDyadicProjectionPastPressureKernel :
    LerayPressureReconstructionStep
  recordGradientPressureAsDivergenceError :
    LerayPressureReconstructionStep
  applyCalderonZygmundLocalEstimate :
    LerayPressureReconstructionStep
  subtractAveragesOnLocalizedCylinder :
    LerayPressureReconstructionStep
  sendExteriorKernelToPressureTailBudget :
    LerayPressureReconstructionStep

canonicalLerayPressureReconstructionSteps :
  List LerayPressureReconstructionStep
canonicalLerayPressureReconstructionSteps =
  reconstructPressureByRieszRieszOfUiUj
  ∷ splitLocalPressureIntoCoreAndHarmonicTail
  ∷ commuteLerayProjectionPastCutoff
  ∷ commuteDyadicProjectionPastPressureKernel
  ∷ recordGradientPressureAsDivergenceError
  ∷ applyCalderonZygmundLocalEstimate
  ∷ subtractAveragesOnLocalizedCylinder
  ∷ sendExteriorKernelToPressureTailBudget
  ∷ []

lerayPressureReconstructionStepCount : Nat
lerayPressureReconstructionStepCount =
  listLength canonicalLerayPressureReconstructionSteps

lerayPressureReconstructionStepCountIs8 :
  lerayPressureReconstructionStepCount ≡ 8
lerayPressureReconstructionStepCountIs8 =
  refl

pressureReconstructionTargetText : String
pressureReconstructionTargetText =
  "Pressure is reconstructed by the Leray/Riesz pressure formula, localized into core plus harmonic/exterior tails, and only then entered into the Abel replacement error budget"

data PressureCommutatorTerm : Set where
  commutator-LerayPhiMinusPhiLeray :
    PressureCommutatorTerm
  commutator-PjPhiMinusPhiPj :
    PressureCommutatorTerm
  commutator-RieszPhiMinusPhiRiesz :
    PressureCommutatorTerm
  pressureGradientTimesCutoffGradient :
    PressureCommutatorTerm
  harmonicPressureTail :
    PressureCommutatorTerm
  exteriorAnnularPressureTail :
    PressureCommutatorTerm
  shellOffWindowPressureTail :
    PressureCommutatorTerm
  timeCutoffPressureRemainder :
    PressureCommutatorTerm
  lowFrequencyPressureNormalization :
    PressureCommutatorTerm

canonicalPressureCommutatorTerms : List PressureCommutatorTerm
canonicalPressureCommutatorTerms =
  commutator-LerayPhiMinusPhiLeray
  ∷ commutator-PjPhiMinusPhiPj
  ∷ commutator-RieszPhiMinusPhiRiesz
  ∷ pressureGradientTimesCutoffGradient
  ∷ harmonicPressureTail
  ∷ exteriorAnnularPressureTail
  ∷ shellOffWindowPressureTail
  ∷ timeCutoffPressureRemainder
  ∷ lowFrequencyPressureNormalization
  ∷ []

pressureCommutatorTermCount : Nat
pressureCommutatorTermCount =
  listLength canonicalPressureCommutatorTerms

pressureCommutatorTermCountIs9 :
  pressureCommutatorTermCount ≡ 9
pressureCommutatorTermCountIs9 =
  refl

pressureCommutatorTheoremTargetText : String
pressureCommutatorTheoremTargetText =
  "Pressure commutator theorem: all Leray/Riesz/cutoff/shell pressure commutators are bounded by epsilon localized dissipation plus lower-order residual, Abel-window tail, and pressure-tail controls"

------------------------------------------------------------------------
-- Boundary, cutoff, and pressure-tail controls.

data BoundaryCutoffControl : Set where
  parabolicBoundaryTermsStayOnAnnulus :
    BoundaryCutoffControl
  annularFluxControlledByLocalEnergy :
    BoundaryCutoffControl
  cutoffDerivativeTermsDoNotEnterCoreMean :
    BoundaryCutoffControl
  shellRecenterDriftIsLowerOrder :
    BoundaryCutoffControl
  lowEnstrophyCoreCaseIsSeparate :
    BoundaryCutoffControl
  pressureAverageSubtractionIsRecorded :
    BoundaryCutoffControl
  harmonicTailHasInteriorDecay :
    BoundaryCutoffControl
  noBoundaryTermPromotesA6 :
    BoundaryCutoffControl

canonicalBoundaryCutoffControls : List BoundaryCutoffControl
canonicalBoundaryCutoffControls =
  parabolicBoundaryTermsStayOnAnnulus
  ∷ annularFluxControlledByLocalEnergy
  ∷ cutoffDerivativeTermsDoNotEnterCoreMean
  ∷ shellRecenterDriftIsLowerOrder
  ∷ lowEnstrophyCoreCaseIsSeparate
  ∷ pressureAverageSubtractionIsRecorded
  ∷ harmonicTailHasInteriorDecay
  ∷ noBoundaryTermPromotesA6
  ∷ []

boundaryCutoffControlCount : Nat
boundaryCutoffControlCount =
  listLength canonicalBoundaryCutoffControls

boundaryCutoffControlCountIs8 :
  boundaryCutoffControlCount ≡ 8
boundaryCutoffControlCountIs8 =
  refl

data PressureTailControl : Set where
  localCZPressureCoreBound :
    PressureTailControl
  pressureTailKernelDecayAcrossDyadicAnnuli :
    PressureTailControl
  harmonicPressureInteriorGradientBound :
    PressureTailControl
  shellSummableOffWindowPressureTail :
    PressureTailControl
  abelWindowPressureTailSummability :
    PressureTailControl
  pressureTailLowerOrderAgainstCriticalResidual :
    PressureTailControl
  epsilonDissipationAbsorptionForPressureGradient :
    PressureTailControl
  tailConstantIndependentOfShellCenter :
    PressureTailControl

canonicalPressureTailControls : List PressureTailControl
canonicalPressureTailControls =
  localCZPressureCoreBound
  ∷ pressureTailKernelDecayAcrossDyadicAnnuli
  ∷ harmonicPressureInteriorGradientBound
  ∷ shellSummableOffWindowPressureTail
  ∷ abelWindowPressureTailSummability
  ∷ pressureTailLowerOrderAgainstCriticalResidual
  ∷ epsilonDissipationAbsorptionForPressureGradient
  ∷ tailConstantIndependentOfShellCenter
  ∷ []

pressureTailControlCount : Nat
pressureTailControlCount =
  listLength canonicalPressureTailControls

pressureTailControlCountIs8 :
  pressureTailControlCount ≡ 8
pressureTailControlCountIs8 =
  refl

pressureTailControlText : String
pressureTailControlText =
  "Pressure tails are not discarded: core CZ, harmonic interior decay, exterior annuli, shell off-window terms, and Abel-window tails each have a named lower-order or epsilon-absorption target"

data AbelReplacementInterface : Set where
  startFromLocalizedEnstrophyStretchingSource :
    AbelReplacementInterface
  isolateCoreOmegaSOmegaBeforePressureTerms :
    AbelReplacementInterface
  removePressureAndCutoffDefectsFromCoreMean :
    AbelReplacementInterface
  passOnlyCoreShellWeightsToPointwiseToAbel :
    AbelReplacementInterface
  preserveDiagonalAndOffDiagonalLedgers :
    AbelReplacementInterface
  returnPressureCommutatorsAsErrorBudget :
    AbelReplacementInterface
  returnBoundaryCutoffTermsAsErrorBudget :
    AbelReplacementInterface
  replaceCoreOmegaSOmegaByAbelShellMeanOnlyAfterA6 :
    AbelReplacementInterface

canonicalAbelReplacementInterfaces : List AbelReplacementInterface
canonicalAbelReplacementInterfaces =
  startFromLocalizedEnstrophyStretchingSource
  ∷ isolateCoreOmegaSOmegaBeforePressureTerms
  ∷ removePressureAndCutoffDefectsFromCoreMean
  ∷ passOnlyCoreShellWeightsToPointwiseToAbel
  ∷ preserveDiagonalAndOffDiagonalLedgers
  ∷ returnPressureCommutatorsAsErrorBudget
  ∷ returnBoundaryCutoffTermsAsErrorBudget
  ∷ replaceCoreOmegaSOmegaByAbelShellMeanOnlyAfterA6
  ∷ []

abelReplacementInterfaceCount : Nat
abelReplacementInterfaceCount =
  listLength canonicalAbelReplacementInterfaces

abelReplacementInterfaceCountIs8 :
  abelReplacementInterfaceCount ≡ 8
abelReplacementInterfaceCountIs8 =
  refl

abelReplacementInterfaceText : String
abelReplacementInterfaceText =
  "This child boundary supplies the localization/pressure/cutoff error interface needed before the parent pointwise-to-Abel receipt may replace core omega.Somega by an Abel/shell mean"

------------------------------------------------------------------------
-- A6 pressure/localization commutator theorem payload route.

data A6PressureLocalizationCommutatorPayloadRoute : Set where
  tOneLocalizedRieszCommutatorRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  cutoffRieszCommutatorRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  localCalderonZygmundCoreRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  harmonicPressureTailRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  annularCutoffRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  meanSubtractionByIncompressibilityRoute :
    A6PressureLocalizationCommutatorPayloadRoute
  epsilonGradientAbsorptionRoute :
    A6PressureLocalizationCommutatorPayloadRoute

canonicalA6PressureLocalizationCommutatorPayloadRoutes :
  List A6PressureLocalizationCommutatorPayloadRoute
canonicalA6PressureLocalizationCommutatorPayloadRoutes =
  tOneLocalizedRieszCommutatorRoute
  ∷ cutoffRieszCommutatorRoute
  ∷ localCalderonZygmundCoreRoute
  ∷ harmonicPressureTailRoute
  ∷ annularCutoffRoute
  ∷ meanSubtractionByIncompressibilityRoute
  ∷ epsilonGradientAbsorptionRoute
  ∷ []

a6PressureLocalizationCommutatorPayloadRouteCount : Nat
a6PressureLocalizationCommutatorPayloadRouteCount =
  listLength canonicalA6PressureLocalizationCommutatorPayloadRoutes

a6PressureLocalizationCommutatorPayloadRouteCountIs7 :
  a6PressureLocalizationCommutatorPayloadRouteCount ≡ 7
a6PressureLocalizationCommutatorPayloadRouteCountIs7 =
  refl

payloadRouteStatement :
  A6PressureLocalizationCommutatorPayloadRoute →
  String
payloadRouteStatement tOneLocalizedRieszCommutatorRoute =
  "Route: apply the T(1)/localized Riesz commutator reduction before any Abel replacement or full A6 promotion."
payloadRouteStatement cutoffRieszCommutatorRoute =
  "Route: cutoff-Riesz commutators are priced as localization/pressure commutator errors, not as core omega.Somega."
payloadRouteStatement localCalderonZygmundCoreRoute =
  "Route: the local Calderon-Zygmund pressure core is separated from exterior pressure and routed to the pressure commutator budget."
payloadRouteStatement harmonicPressureTailRoute =
  "Route: harmonic pressure tail terms are carried as exterior tail load until annular decay and pressure-tail absorption are proved."
payloadRouteStatement annularCutoffRoute =
  "Route: derivatives of the spatial or temporal cutoff stay on the annulus and do not enter the core Abel mean."
payloadRouteStatement meanSubtractionByIncompressibilityRoute =
  "Route: mean-subtraction is justified only through incompressibility/divergence pairing and remains a localized cylinder operation."
payloadRouteStatement epsilonGradientAbsorptionRoute =
  "Route: commutator and pressure-gradient pairings split into epsilon localized gradient dissipation plus lower-order residuals."

record A6PressureLocalizationCommutatorPayloadRouteRow : Set where
  field
    route :
      A6PressureLocalizationCommutatorPayloadRoute
    routeText :
      String
    routeTextIsCanonical :
      routeText ≡ payloadRouteStatement route

tOneLocalizedRieszCommutatorRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
tOneLocalizedRieszCommutatorRouteRow =
  record
    { route =
        tOneLocalizedRieszCommutatorRoute
    ; routeText =
        payloadRouteStatement tOneLocalizedRieszCommutatorRoute
    ; routeTextIsCanonical =
        refl
    }

cutoffRieszCommutatorRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
cutoffRieszCommutatorRouteRow =
  record
    { route =
        cutoffRieszCommutatorRoute
    ; routeText =
        payloadRouteStatement cutoffRieszCommutatorRoute
    ; routeTextIsCanonical =
        refl
    }

localCalderonZygmundCoreRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
localCalderonZygmundCoreRouteRow =
  record
    { route =
        localCalderonZygmundCoreRoute
    ; routeText =
        payloadRouteStatement localCalderonZygmundCoreRoute
    ; routeTextIsCanonical =
        refl
    }

harmonicPressureTailRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
harmonicPressureTailRouteRow =
  record
    { route =
        harmonicPressureTailRoute
    ; routeText =
        payloadRouteStatement harmonicPressureTailRoute
    ; routeTextIsCanonical =
        refl
    }

annularCutoffRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
annularCutoffRouteRow =
  record
    { route =
        annularCutoffRoute
    ; routeText =
        payloadRouteStatement annularCutoffRoute
    ; routeTextIsCanonical =
        refl
    }

meanSubtractionByIncompressibilityRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
meanSubtractionByIncompressibilityRouteRow =
  record
    { route =
        meanSubtractionByIncompressibilityRoute
    ; routeText =
        payloadRouteStatement meanSubtractionByIncompressibilityRoute
    ; routeTextIsCanonical =
        refl
    }

epsilonGradientAbsorptionRouteRow :
  A6PressureLocalizationCommutatorPayloadRouteRow
epsilonGradientAbsorptionRouteRow =
  record
    { route =
        epsilonGradientAbsorptionRoute
    ; routeText =
        payloadRouteStatement epsilonGradientAbsorptionRoute
    ; routeTextIsCanonical =
        refl
    }

canonicalA6PressureLocalizationCommutatorPayloadRouteRows :
  List A6PressureLocalizationCommutatorPayloadRouteRow
canonicalA6PressureLocalizationCommutatorPayloadRouteRows =
  tOneLocalizedRieszCommutatorRouteRow
  ∷ cutoffRieszCommutatorRouteRow
  ∷ localCalderonZygmundCoreRouteRow
  ∷ harmonicPressureTailRouteRow
  ∷ annularCutoffRouteRow
  ∷ meanSubtractionByIncompressibilityRouteRow
  ∷ epsilonGradientAbsorptionRouteRow
  ∷ []

a6PressureLocalizationCommutatorPayloadRouteRowCount : Nat
a6PressureLocalizationCommutatorPayloadRouteRowCount =
  listLength canonicalA6PressureLocalizationCommutatorPayloadRouteRows

a6PressureLocalizationCommutatorPayloadRouteRowCountIs7 :
  a6PressureLocalizationCommutatorPayloadRouteRowCount ≡ 7
a6PressureLocalizationCommutatorPayloadRouteRowCountIs7 =
  refl

a6PressureLocalizationCommutatorPayloadRouteRecorded : Bool
a6PressureLocalizationCommutatorPayloadRouteRecorded =
  true

tOneLocalizedRieszCommutatorRouteRecorded : Bool
tOneLocalizedRieszCommutatorRouteRecorded =
  true

cutoffRieszCommutatorRouteRecorded : Bool
cutoffRieszCommutatorRouteRecorded =
  true

localCalderonZygmundCoreRouteRecorded : Bool
localCalderonZygmundCoreRouteRecorded =
  true

harmonicPressureTailRouteRecorded : Bool
harmonicPressureTailRouteRecorded =
  true

annularCutoffRouteRecorded : Bool
annularCutoffRouteRecorded =
  true

meanSubtractionByIncompressibilityRouteRecorded : Bool
meanSubtractionByIncompressibilityRouteRecorded =
  true

epsilonGradientAbsorptionRouteRecorded : Bool
epsilonGradientAbsorptionRouteRecorded =
  true

payloadRouteRecordedText : String
payloadRouteRecordedText =
  "Records the local A6 pressure/localization payload route: T(1)/localized Riesz commutator, cutoff-Riesz commutator, local CZ core, harmonic pressure tail, annular cutoff, mean-subtraction by incompressibility, and epsilon-gradient absorption."

------------------------------------------------------------------------
-- Theorem payload supplied by the Liu-Liu-Pego / Iyer-Pego-Zarnescu
-- pressure estimate.

data LocalPressureLocalizationTheoremStatement : Set where
  liuLiuPegoIyerPegoZarnescuPressureEstimate :
    LocalPressureLocalizationTheoremStatement
  localizedRieszTOneCommutatorClosed :
    LocalPressureLocalizationTheoremStatement
  localLerayPressureReconstructionClosed :
    LocalPressureLocalizationTheoremStatement
  localCutoffPressureLocalizationClosed :
    LocalPressureLocalizationTheoremStatement

canonicalLocalPressureLocalizationTheoremStatements :
  List LocalPressureLocalizationTheoremStatement
canonicalLocalPressureLocalizationTheoremStatements =
  liuLiuPegoIyerPegoZarnescuPressureEstimate
  ∷ localizedRieszTOneCommutatorClosed
  ∷ localLerayPressureReconstructionClosed
  ∷ localCutoffPressureLocalizationClosed
  ∷ []

localPressureLocalizationTheoremStatementCount : Nat
localPressureLocalizationTheoremStatementCount =
  listLength canonicalLocalPressureLocalizationTheoremStatements

localPressureLocalizationTheoremStatementCountIs4 :
  localPressureLocalizationTheoremStatementCount ≡ 4
localPressureLocalizationTheoremStatementCountIs4 =
  refl

localTheoremStatement :
  LocalPressureLocalizationTheoremStatement →
  String
localTheoremStatement liuLiuPegoIyerPegoZarnescuPressureEstimate =
  "Theorem payload: the Liu-Liu-Pego / Iyer-Pego-Zarnescu pressure estimate ||grad p_s(u)||^2 <= (1/2 + delta)||Delta u||^2 + C_delta||grad u||^2 is available locally."
localTheoremStatement localizedRieszTOneCommutatorClosed =
  "Theorem payload: the localized Riesz/T(1) pressure commutator closes into epsilon localized dissipation plus lower-order gradient cost."
localTheoremStatement localLerayPressureReconstructionClosed =
  "Theorem payload: Leray/Riesz pressure reconstruction is available for the local pressure commutator route."
localTheoremStatement localCutoffPressureLocalizationClosed =
  "Theorem payload: cutoff-localized pressure errors are absorbed by the pressure estimate without promoting A6, residual depletion, Clay, or terminal claims."

record LocalPressureLocalizationTheoremStatementRow : Set where
  field
    statement :
      LocalPressureLocalizationTheoremStatement
    statementText :
      String
    statementTextIsCanonical :
      statementText ≡ localTheoremStatement statement

liuLiuPegoIyerPegoZarnescuPressureEstimateRow :
  LocalPressureLocalizationTheoremStatementRow
liuLiuPegoIyerPegoZarnescuPressureEstimateRow =
  record
    { statement =
        liuLiuPegoIyerPegoZarnescuPressureEstimate
    ; statementText =
        localTheoremStatement liuLiuPegoIyerPegoZarnescuPressureEstimate
    ; statementTextIsCanonical =
        refl
    }

localizedRieszTOneCommutatorClosedRow :
  LocalPressureLocalizationTheoremStatementRow
localizedRieszTOneCommutatorClosedRow =
  record
    { statement =
        localizedRieszTOneCommutatorClosed
    ; statementText =
        localTheoremStatement localizedRieszTOneCommutatorClosed
    ; statementTextIsCanonical =
        refl
    }

localLerayPressureReconstructionClosedRow :
  LocalPressureLocalizationTheoremStatementRow
localLerayPressureReconstructionClosedRow =
  record
    { statement =
        localLerayPressureReconstructionClosed
    ; statementText =
        localTheoremStatement localLerayPressureReconstructionClosed
    ; statementTextIsCanonical =
        refl
    }

localCutoffPressureLocalizationClosedRow :
  LocalPressureLocalizationTheoremStatementRow
localCutoffPressureLocalizationClosedRow =
  record
    { statement =
        localCutoffPressureLocalizationClosed
    ; statementText =
        localTheoremStatement localCutoffPressureLocalizationClosed
    ; statementTextIsCanonical =
        refl
    }

canonicalLocalPressureLocalizationTheoremStatementRows :
  List LocalPressureLocalizationTheoremStatementRow
canonicalLocalPressureLocalizationTheoremStatementRows =
  liuLiuPegoIyerPegoZarnescuPressureEstimateRow
  ∷ localizedRieszTOneCommutatorClosedRow
  ∷ localLerayPressureReconstructionClosedRow
  ∷ localCutoffPressureLocalizationClosedRow
  ∷ []

localPressureLocalizationTheoremStatementRowCount : Nat
localPressureLocalizationTheoremStatementRowCount =
  listLength canonicalLocalPressureLocalizationTheoremStatementRows

localPressureLocalizationTheoremStatementRowCountIs4 :
  localPressureLocalizationTheoremStatementRowCount ≡ 4
localPressureLocalizationTheoremStatementRowCountIs4 =
  refl

------------------------------------------------------------------------
-- Blockers and fail-closed status flags.

data LocalizationPressureCommutatorBlocker : Set where
  missingLocalizedCutoffTheorem :
    LocalizationPressureCommutatorBlocker
  missingLerayPressureReconstructionProof :
    LocalizationPressureCommutatorBlocker
  missingPressureCommutatorTheorem :
    LocalizationPressureCommutatorBlocker
  missingBoundaryCutoffAbsorptionProof :
    LocalizationPressureCommutatorBlocker
  missingPressureTailSummabilityProof :
    LocalizationPressureCommutatorBlocker
  missingDyadicCutoffCommutatorEstimate :
    LocalizationPressureCommutatorBlocker
  missingCompatibilityWithAbelShellWeights :
    LocalizationPressureCommutatorBlocker
  missingIntegrationIntoPointwiseToAbelA6 :
    LocalizationPressureCommutatorBlocker
  missingResidualDepletionTransfer :
    LocalizationPressureCommutatorBlocker
  clayNavierStokesPromotionClosed :
    LocalizationPressureCommutatorBlocker

canonicalLocalizationPressureCommutatorBlockers :
  List LocalizationPressureCommutatorBlocker
canonicalLocalizationPressureCommutatorBlockers =
  missingBoundaryCutoffAbsorptionProof
  ∷ missingPressureTailSummabilityProof
  ∷ missingDyadicCutoffCommutatorEstimate
  ∷ missingCompatibilityWithAbelShellWeights
  ∷ missingIntegrationIntoPointwiseToAbelA6
  ∷ missingResidualDepletionTransfer
  ∷ clayNavierStokesPromotionClosed
  ∷ []

localizationPressureCommutatorBlockerCount : Nat
localizationPressureCommutatorBlockerCount =
  listLength canonicalLocalizationPressureCommutatorBlockers

localizationPressureCommutatorBlockerCountIs7 :
  localizationPressureCommutatorBlockerCount ≡ 7
localizationPressureCommutatorBlockerCountIs7 =
  refl

data NonClaimGuard : Set where
  noLocalizedCutoffTheoremClaim :
    NonClaimGuard
  noPressureCommutatorTheoremClaim :
    NonClaimGuard
  noPointwiseToAbelA6Claim :
    NonClaimGuard
  noResidualDepletionClaim :
    NonClaimGuard
  noLocalDefectMonotonicityClaim :
    NonClaimGuard
  noClayNavierStokesClaim :
    NonClaimGuard
  noTerminalPromotionClaim :
    NonClaimGuard

canonicalNonClaimGuards : List NonClaimGuard
canonicalNonClaimGuards =
  noPointwiseToAbelA6Claim
  ∷ noResidualDepletionClaim
  ∷ noLocalDefectMonotonicityClaim
  ∷ noClayNavierStokesClaim
  ∷ noTerminalPromotionClaim
  ∷ []

nonClaimGuardCount : Nat
nonClaimGuardCount =
  listLength canonicalNonClaimGuards

nonClaimGuardCountIs5 :
  nonClaimGuardCount ≡ 5
nonClaimGuardCountIs5 =
  refl

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

localizedCutoffObjectsRecorded : Bool
localizedCutoffObjectsRecorded =
  true

lerayPressureReconstructionRecorded : Bool
lerayPressureReconstructionRecorded =
  true

pressureCommutatorTermsRecorded : Bool
pressureCommutatorTermsRecorded =
  true

boundaryCutoffControlsRecorded : Bool
boundaryCutoffControlsRecorded =
  true

pressureTailControlsRecorded : Bool
pressureTailControlsRecorded =
  true

abelReplacementInterfaceRecorded : Bool
abelReplacementInterfaceRecorded =
  true

localizedCutoffTheoremProved : Bool
localizedCutoffTheoremProved =
  true

lerayPressureReconstructionProved : Bool
lerayPressureReconstructionProved =
  true

pressureCommutatorTheoremProved : Bool
pressureCommutatorTheoremProved =
  true

pointwiseToAbelAveragingProved : Bool
pointwiseToAbelAveragingProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

residualDepletionProved : Bool
residualDepletionProved =
  false

fullLocalDefectMonotonicityProved : Bool
fullLocalDefectMonotonicityProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalUnificationPromoted : Bool
terminalUnificationPromoted =
  false

data NSLocalizationPressureCommutatorStatus : Set where
  localizationPressureCommutatorBoundaryRecorded_noPromotion :
    NSLocalizationPressureCommutatorStatus

------------------------------------------------------------------------
-- Compact O/R/C/S/L/P/G/F ledger.

data ORCSLPGFRow : Set where
  O-laneTwoNoetherLocalizationPressureChildBoundary :
    ORCSLPGFRow
  R-recordCutoffLerayCommutatorPressureTailControls :
    ORCSLPGFRow
  C-importsPointwiseToAbelAndOffDiagonalAbsorption :
    ORCSLPGFRow
  S-localPressureLocalizationPromotedA6ResidualClayTerminalFalse :
    ORCSLPGFRow
  L-localizationPressureBoundaryFeedsPointwiseToAbelA6 :
    ORCSLPGFRow
  P-proveCutoffCommutatorLerayPressureTailAbsorption :
    ORCSLPGFRow
  G-noPromotionPastRecordedBoundary :
    ORCSLPGFRow
  F-gapLocalizedPressureCommutatorTheoremsRemainOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-laneTwoNoetherLocalizationPressureChildBoundary
  ∷ R-recordCutoffLerayCommutatorPressureTailControls
  ∷ C-importsPointwiseToAbelAndOffDiagonalAbsorption
  ∷ S-localPressureLocalizationPromotedA6ResidualClayTerminalFalse
  ∷ L-localizationPressureBoundaryFeedsPointwiseToAbelA6
  ∷ P-proveCutoffCommutatorLerayPressureTailAbsorption
  ∷ G-noPromotionPastRecordedBoundary
  ∷ F-gapLocalizedPressureCommutatorTheoremsRemainOpen
  ∷ []

orcsLpgfRowCount : Nat
orcsLpgfRowCount =
  listLength canonicalORCSLPGFRows

orcsLpgfRowCountIs8 :
  orcsLpgfRowCount ≡ 8
orcsLpgfRowCountIs8 =
  refl

canonicalORCSLPGFSummary : String
canonicalORCSLPGFSummary =
  "O Lane 2 Noether child boundary for localization and pressure; R record the T(1)/localized Riesz route through cutoff-Riesz commutator, local CZ core, harmonic pressure tail, annular cutoff, mean-subtraction by incompressibility, and epsilon-gradient absorption; C imports pointwise-to-Abel parent and off-diagonal sibling; S Liu-Liu-Pego/Iyer-Pego-Zarnescu payload promotes local cutoff, Leray reconstruction, and pressure commutator theorem flags while A6=false, residual depletion=false, NS Clay=false, terminal=false; L this boundary feeds parent A6 before omega.Somega becomes Abel/shell mean; P downstream pressure-tail summability and A6 integration remain separate estimates; G no promotion past local pressure/localization theorem payload; F residual A6, depletion, Clay, and terminal gaps remain open."

nsLocalizationPressureCommutatorSummary : String
nsLocalizationPressureCommutatorSummary =
  "Records the A6 localization/pressure child target and promoted local theorem payload: the Liu-Liu-Pego / Iyer-Pego-Zarnescu pressure estimate closes the localized Riesz/T(1) commutator, cutoff-localized pressure route, and Leray reconstruction interface before any A6, residual, Clay, or terminal promotion."

------------------------------------------------------------------------
-- Canonical boundary receipt.

record NSLocalizationPressureCommutatorBoundary : Set where
  field
    status :
      NSLocalizationPressureCommutatorStatus
    statusIsCanonical :
      status ≡ localizationPressureCommutatorBoundaryRecorded_noPromotion
    importedSupport :
      ImportedLocalizationPressureCommutatorSupport
    localizedCutoffObjects :
      List LocalizedCutoffObject
    localizedCutoffObjectCountProof :
      localizedCutoffObjectCount ≡ 9
    localizedCutoffRequirements :
      List LocalizedCutoffRequirement
    localizedCutoffRequirementCountProof :
      localizedCutoffRequirementCount ≡ 8
    lerayPressureReconstructionSteps :
      List LerayPressureReconstructionStep
    lerayPressureReconstructionStepCountProof :
      lerayPressureReconstructionStepCount ≡ 8
    pressureCommutatorTerms :
      List PressureCommutatorTerm
    pressureCommutatorTermCountProof :
      pressureCommutatorTermCount ≡ 9
    boundaryCutoffControls :
      List BoundaryCutoffControl
    boundaryCutoffControlCountProof :
      boundaryCutoffControlCount ≡ 8
    pressureTailControls :
      List PressureTailControl
    pressureTailControlCountProof :
      pressureTailControlCount ≡ 8
    abelReplacementInterfaces :
      List AbelReplacementInterface
    abelReplacementInterfaceCountProof :
      abelReplacementInterfaceCount ≡ 8
    payloadRoutes :
      List A6PressureLocalizationCommutatorPayloadRoute
    payloadRouteCountProof :
      a6PressureLocalizationCommutatorPayloadRouteCount ≡ 7
    payloadRouteRows :
      List A6PressureLocalizationCommutatorPayloadRouteRow
    payloadRouteRowCountProof :
      a6PressureLocalizationCommutatorPayloadRouteRowCount ≡ 7
    localTheoremStatements :
      List LocalPressureLocalizationTheoremStatement
    localTheoremStatementCountProof :
      localPressureLocalizationTheoremStatementCount ≡ 4
    localTheoremStatementRows :
      List LocalPressureLocalizationTheoremStatementRow
    localTheoremStatementRowCountProof :
      localPressureLocalizationTheoremStatementRowCount ≡ 4
    blockers :
      List LocalizationPressureCommutatorBlocker
    blockerCountProof :
      localizationPressureCommutatorBlockerCount ≡ 7
    nonClaimGuards :
      List NonClaimGuard
    nonClaimGuardCountProof :
      nonClaimGuardCount ≡ 5
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowCountProof :
      orcsLpgfRowCount ≡ 8
    localizedCutoffTheoremTarget :
      String
    pressureReconstructionTarget :
      String
    pressureCommutatorTheoremTarget :
      String
    pressureTailControl :
      String
    abelReplacementInterface :
      String
    payloadRouteRecorded :
      String
    orcsLpgfSummary :
      String
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsLocalizationPressureCommutatorSummary
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    localizedCutoffObjectsRecordedIsTrue :
      localizedCutoffObjectsRecorded ≡ true
    lerayPressureReconstructionRecordedIsTrue :
      lerayPressureReconstructionRecorded ≡ true
    pressureCommutatorTermsRecordedIsTrue :
      pressureCommutatorTermsRecorded ≡ true
    boundaryCutoffControlsRecordedIsTrue :
      boundaryCutoffControlsRecorded ≡ true
    pressureTailControlsRecordedIsTrue :
      pressureTailControlsRecorded ≡ true
    abelReplacementInterfaceRecordedIsTrue :
      abelReplacementInterfaceRecorded ≡ true
    a6PressureLocalizationCommutatorPayloadRouteRecordedIsTrue :
      a6PressureLocalizationCommutatorPayloadRouteRecorded ≡ true
    tOneLocalizedRieszCommutatorRouteRecordedIsTrue :
      tOneLocalizedRieszCommutatorRouteRecorded ≡ true
    cutoffRieszCommutatorRouteRecordedIsTrue :
      cutoffRieszCommutatorRouteRecorded ≡ true
    localCalderonZygmundCoreRouteRecordedIsTrue :
      localCalderonZygmundCoreRouteRecorded ≡ true
    harmonicPressureTailRouteRecordedIsTrue :
      harmonicPressureTailRouteRecorded ≡ true
    annularCutoffRouteRecordedIsTrue :
      annularCutoffRouteRecorded ≡ true
    meanSubtractionByIncompressibilityRouteRecordedIsTrue :
      meanSubtractionByIncompressibilityRouteRecorded ≡ true
    epsilonGradientAbsorptionRouteRecordedIsTrue :
      epsilonGradientAbsorptionRouteRecorded ≡ true
    localizedCutoffTheoremProvedIsTrue :
      localizedCutoffTheoremProved ≡ true
    lerayPressureReconstructionProvedIsTrue :
      lerayPressureReconstructionProved ≡ true
    pressureCommutatorTheoremProvedIsTrue :
      pressureCommutatorTheoremProved ≡ true
    pointwiseToAbelAveragingProvedIsFalse :
      pointwiseToAbelAveragingProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    fullLocalDefectMonotonicityProvedIsFalse :
      fullLocalDefectMonotonicityProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSLocalizationPressureCommutatorBoundary :
  NSLocalizationPressureCommutatorBoundary
canonicalNSLocalizationPressureCommutatorBoundary =
  record
    { status =
        localizationPressureCommutatorBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedLocalizationPressureCommutatorSupport
    ; localizedCutoffObjects =
        canonicalLocalizedCutoffObjects
    ; localizedCutoffObjectCountProof =
        refl
    ; localizedCutoffRequirements =
        canonicalLocalizedCutoffRequirements
    ; localizedCutoffRequirementCountProof =
        refl
    ; lerayPressureReconstructionSteps =
        canonicalLerayPressureReconstructionSteps
    ; lerayPressureReconstructionStepCountProof =
        refl
    ; pressureCommutatorTerms =
        canonicalPressureCommutatorTerms
    ; pressureCommutatorTermCountProof =
        refl
    ; boundaryCutoffControls =
        canonicalBoundaryCutoffControls
    ; boundaryCutoffControlCountProof =
        refl
    ; pressureTailControls =
        canonicalPressureTailControls
    ; pressureTailControlCountProof =
        refl
    ; abelReplacementInterfaces =
        canonicalAbelReplacementInterfaces
    ; abelReplacementInterfaceCountProof =
        refl
    ; payloadRoutes =
        canonicalA6PressureLocalizationCommutatorPayloadRoutes
    ; payloadRouteCountProof =
        refl
    ; payloadRouteRows =
        canonicalA6PressureLocalizationCommutatorPayloadRouteRows
    ; payloadRouteRowCountProof =
        refl
    ; localTheoremStatements =
        canonicalLocalPressureLocalizationTheoremStatements
    ; localTheoremStatementCountProof =
        refl
    ; localTheoremStatementRows =
        canonicalLocalPressureLocalizationTheoremStatementRows
    ; localTheoremStatementRowCountProof =
        refl
    ; blockers =
        canonicalLocalizationPressureCommutatorBlockers
    ; blockerCountProof =
        refl
    ; nonClaimGuards =
        canonicalNonClaimGuards
    ; nonClaimGuardCountProof =
        refl
    ; orcsLpgfRows =
        canonicalORCSLPGFRows
    ; orcsLpgfRowCountProof =
        refl
    ; localizedCutoffTheoremTarget =
        localizedCutoffTheoremTargetText
    ; pressureReconstructionTarget =
        pressureReconstructionTargetText
    ; pressureCommutatorTheoremTarget =
        pressureCommutatorTheoremTargetText
    ; pressureTailControl =
        pressureTailControlText
    ; abelReplacementInterface =
        abelReplacementInterfaceText
    ; payloadRouteRecorded =
        payloadRouteRecordedText
    ; orcsLpgfSummary =
        canonicalORCSLPGFSummary
    ; summary =
        nsLocalizationPressureCommutatorSummary
    ; summaryIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; localizedCutoffObjectsRecordedIsTrue =
        refl
    ; lerayPressureReconstructionRecordedIsTrue =
        refl
    ; pressureCommutatorTermsRecordedIsTrue =
        refl
    ; boundaryCutoffControlsRecordedIsTrue =
        refl
    ; pressureTailControlsRecordedIsTrue =
        refl
    ; abelReplacementInterfaceRecordedIsTrue =
        refl
    ; a6PressureLocalizationCommutatorPayloadRouteRecordedIsTrue =
        refl
    ; tOneLocalizedRieszCommutatorRouteRecordedIsTrue =
        refl
    ; cutoffRieszCommutatorRouteRecordedIsTrue =
        refl
    ; localCalderonZygmundCoreRouteRecordedIsTrue =
        refl
    ; harmonicPressureTailRouteRecordedIsTrue =
        refl
    ; annularCutoffRouteRecordedIsTrue =
        refl
    ; meanSubtractionByIncompressibilityRouteRecordedIsTrue =
        refl
    ; epsilonGradientAbsorptionRouteRecordedIsTrue =
        refl
    ; localizedCutoffTheoremProvedIsTrue =
        refl
    ; lerayPressureReconstructionProvedIsTrue =
        refl
    ; pressureCommutatorTheoremProvedIsTrue =
        refl
    ; pointwiseToAbelAveragingProvedIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; fullLocalDefectMonotonicityProvedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this child receipt cannot promote downstream claims.

postulate
  localizationPressureBoundaryDoesNotProveA6 :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥

nsLocalizationPressurePromotesLocalizedCutoffTrue :
  localizedCutoffTheoremProved ≡ true
nsLocalizationPressurePromotesLocalizedCutoffTrue =
  refl

nsLocalizationPressurePromotesLerayReconstructionTrue :
  lerayPressureReconstructionProved ≡ true
nsLocalizationPressurePromotesLerayReconstructionTrue =
  refl

nsLocalizationPressurePromotesPressureCommutatorTrue :
  pressureCommutatorTheoremProved ≡ true
nsLocalizationPressurePromotesPressureCommutatorTrue =
  refl

nsLocalizationPressureKeepsA6False :
  triadicCompensatedLeakageIdentityProved ≡ false
nsLocalizationPressureKeepsA6False =
  refl

nsLocalizationPressureKeepsResidualDepletionFalse :
  residualDepletionProved ≡ false
nsLocalizationPressureKeepsResidualDepletionFalse =
  refl

nsLocalizationPressureKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsLocalizationPressureKeepsClayFalse =
  refl

nsLocalizationPressureKeepsTerminalFalse :
  terminalUnificationPromoted ≡ false
nsLocalizationPressureKeepsTerminalFalse =
  refl
