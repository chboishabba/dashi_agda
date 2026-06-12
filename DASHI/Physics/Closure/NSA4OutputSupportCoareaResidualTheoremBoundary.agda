module DASHI.Physics.Closure.NSA4OutputSupportCoareaResidualTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSOutputGreatCircleStripSlicingBoundary
  as StripSlicing
import DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary
  as UniformNormal

------------------------------------------------------------------------
-- NS A4 output-support coarea/residual theorem boundary.
--
-- This is a lightweight, fail-closed receipt for the four-part A4 proof
-- content:
--
--   A4.1 direction-map regularity,
--   A4.2 Jacobian lower-bound / nondegeneracy route,
--   A4.3 coarea propagation,
--   A4.4 strip-hitting / pushforward richness for every output normal,
--   A4.5 uniformity across the Type-I rescaling family.
--
-- It is intentionally standalone so the direct validation target can run
-- under the 10s sprint cap.  It now records only the candidate proof chain
-- and the exact open lower-bound/uniformity gaps.  It does not promote A5,
-- A6, A7, CKN/BKM, Navier-Stokes Clay, or terminal authority.

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
-- Imported fail-closed chain support.

record ImportedA4CoareaCandidateChainSupport : Set where
  field
    outputSupportBoundary :
      OutputSupport.NSLeiRenTianOutputSupportTransferBoundary
    outputSupportBoundaryIsCanonical :
      outputSupportBoundary
        ≡ OutputSupport.canonicalNSLeiRenTianOutputSupportTransferBoundary
    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    phiJacobianBoundaryIsCanonical :
      phiJacobianBoundary
        ≡ PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    stripSlicingBoundary :
      StripSlicing.NSOutputGreatCircleStripSlicingBoundary
    stripSlicingBoundaryIsCanonical :
      stripSlicingBoundary
        ≡ StripSlicing.canonicalNSOutputGreatCircleStripSlicingBoundary
    uniformNormalBoundary :
      UniformNormal.NSA4UniformInNormalConstantsBoundary
    uniformNormalBoundaryIsCanonical :
      uniformNormalBoundary
        ≡ UniformNormal.canonicalNSA4UniformInNormalConstantsBoundary
    outputSupportStillFalse :
      OutputSupport.leiRenTianOutputSupportTransferProved ≡ false
    phiJacobianStillFalse :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ false
    stripSlicingStillFalse :
      StripSlicing.OutputGreatCircleStripSlicingProved ≡ false
    uniformNormalStillFalse :
      UniformNormal.uniformInNormalConstantsTheoremProved ≡ false

canonicalImportedA4CoareaCandidateChainSupport :
  ImportedA4CoareaCandidateChainSupport
canonicalImportedA4CoareaCandidateChainSupport =
  record
    { outputSupportBoundary =
        OutputSupport.canonicalNSLeiRenTianOutputSupportTransferBoundary
    ; outputSupportBoundaryIsCanonical =
        refl
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; phiJacobianBoundaryIsCanonical =
        refl
    ; stripSlicingBoundary =
        StripSlicing.canonicalNSOutputGreatCircleStripSlicingBoundary
    ; stripSlicingBoundaryIsCanonical =
        refl
    ; uniformNormalBoundary =
        UniformNormal.canonicalNSA4UniformInNormalConstantsBoundary
    ; uniformNormalBoundaryIsCanonical =
        refl
    ; outputSupportStillFalse =
        refl
    ; phiJacobianStillFalse =
        refl
    ; stripSlicingStillFalse =
        refl
    ; uniformNormalStillFalse =
        refl
    }

------------------------------------------------------------------------
-- A4 proof content.

data A4ProofPart : Set where
  partA4-1-directionMapRegularity :
    A4ProofPart
  partA4-2-jacobianLowerBoundNondegeneracyRoute :
    A4ProofPart
  partA4-3-coareaPropagation :
    A4ProofPart
  partA4-4-stripHittingPushforwardRichness :
    A4ProofPart
  partA4-5-uniformityAcrossTypeIRescalingFamily :
    A4ProofPart

canonicalA4ProofParts :
  List A4ProofPart
canonicalA4ProofParts =
  partA4-1-directionMapRegularity
  ∷ partA4-2-jacobianLowerBoundNondegeneracyRoute
  ∷ partA4-3-coareaPropagation
  ∷ partA4-4-stripHittingPushforwardRichness
  ∷ partA4-5-uniformityAcrossTypeIRescalingFamily
  ∷ []

A4ProofPartCount : Nat
A4ProofPartCount =
  listLength canonicalA4ProofParts

A4ProofPartCountIs5 :
  A4ProofPartCount ≡ 5
A4ProofPartCountIs5 =
  refl

data A4CandidateChainStage : Set where
  stageA4-1-directionMapRegularity :
    A4CandidateChainStage
  stageA4-2-jacobianLowerBoundNondegeneracyRoute :
    A4CandidateChainStage
  stageA4-3-coareaPropagation :
    A4CandidateChainStage
  stageA4-4-stripHittingPushforwardRichness :
    A4CandidateChainStage
  stageA4-5-uniformityAcrossTypeIRescalingFamily :
    A4CandidateChainStage

canonicalA4CandidateChainStages :
  List A4CandidateChainStage
canonicalA4CandidateChainStages =
  stageA4-1-directionMapRegularity
  ∷ stageA4-2-jacobianLowerBoundNondegeneracyRoute
  ∷ stageA4-3-coareaPropagation
  ∷ stageA4-4-stripHittingPushforwardRichness
  ∷ stageA4-5-uniformityAcrossTypeIRescalingFamily
  ∷ []

A4CandidateChainStageCount : Nat
A4CandidateChainStageCount =
  listLength canonicalA4CandidateChainStages

A4CandidateChainStageCountIs5 :
  A4CandidateChainStageCount ≡ 5
A4CandidateChainStageCountIs5 =
  refl

data A4UnresolvedRouteStep : Set where
  unresolvedA4-1DirectionMapRegularityUpgrade :
    A4UnresolvedRouteStep
  unresolvedA4-2JacobianLowerBoundNondegeneracyBridge :
    A4UnresolvedRouteStep
  unresolvedA4-3CoareaPropagationBridge :
    A4UnresolvedRouteStep
  unresolvedA4-4StripHittingPushforwardRichnessForEveryNormal :
    A4UnresolvedRouteStep
  unresolvedA4-5UniformityAcrossTypeIRescalingFamily :
    A4UnresolvedRouteStep

canonicalA4UnresolvedRouteSteps :
  List A4UnresolvedRouteStep
canonicalA4UnresolvedRouteSteps =
  unresolvedA4-1DirectionMapRegularityUpgrade
  ∷ unresolvedA4-2JacobianLowerBoundNondegeneracyBridge
  ∷ unresolvedA4-3CoareaPropagationBridge
  ∷ unresolvedA4-4StripHittingPushforwardRichnessForEveryNormal
  ∷ unresolvedA4-5UniformityAcrossTypeIRescalingFamily
  ∷ []

A4UnresolvedRouteStepCount : Nat
A4UnresolvedRouteStepCount =
  listLength canonicalA4UnresolvedRouteSteps

A4UnresolvedRouteStepCountIs5 :
  A4UnresolvedRouteStepCount ≡ 5
A4UnresolvedRouteStepCountIs5 =
  refl

data A4LocalDerivativeClause : Set where
  directionMapDifferentiableAwayFromAntipodalDegeneracy :
    A4LocalDerivativeClause
  normalizeSumEquatorDerivativeFormula :
    A4LocalDerivativeClause
  equatorSecondFactorVanishes :
    A4LocalDerivativeClause
  derivativeScaleIsOneOverSqrtTwoCosHalfGamma :
    A4LocalDerivativeClause
  tangentDirectionFieldVariesContinuouslyAlongRouteA4-1 :
    A4LocalDerivativeClause

canonicalA4LocalDerivativeClauses :
  List A4LocalDerivativeClause
canonicalA4LocalDerivativeClauses =
  directionMapDifferentiableAwayFromAntipodalDegeneracy
  ∷ normalizeSumEquatorDerivativeFormula
  ∷ equatorSecondFactorVanishes
  ∷ derivativeScaleIsOneOverSqrtTwoCosHalfGamma
  ∷ tangentDirectionFieldVariesContinuouslyAlongRouteA4-1
  ∷ []

A4LocalDerivativeClauseCount : Nat
A4LocalDerivativeClauseCount =
  listLength canonicalA4LocalDerivativeClauses

A4LocalDerivativeClauseCountIs5 :
  A4LocalDerivativeClauseCount ≡ 5
A4LocalDerivativeClauseCountIs5 =
  refl

data A4CoareaDensityClause : Set where
  sardCriticalValuesNull :
    A4CoareaDensityClause
  jacobianLowerBoundAttemptAwayFromRankDropSet :
    A4CoareaDensityClause
  offAntipodalGradientInverseUniformlyBounded :
    A4CoareaDensityClause
  coareaPropagationFeedsRescaledStripBudget :
    A4CoareaDensityClause
  stripDensityPositiveForRegularValues :
    A4CoareaDensityClause
  jacobianAttemptStillNeedsQuantitativeClosure :
    A4CoareaDensityClause

canonicalA4CoareaDensityClauses :
  List A4CoareaDensityClause
canonicalA4CoareaDensityClauses =
  sardCriticalValuesNull
  ∷ jacobianLowerBoundAttemptAwayFromRankDropSet
  ∷ offAntipodalGradientInverseUniformlyBounded
  ∷ coareaPropagationFeedsRescaledStripBudget
  ∷ stripDensityPositiveForRegularValues
  ∷ jacobianAttemptStillNeedsQuantitativeClosure
  ∷ []

A4CoareaDensityClauseCount : Nat
A4CoareaDensityClauseCount =
  listLength canonicalA4CoareaDensityClauses

A4CoareaDensityClauseCountIs6 :
  A4CoareaDensityClauseCount ≡ 6
A4CoareaDensityClauseCountIs6 =
  refl

data A4LRTTransferClause : Set where
  outputGreatCircleStripPulledBackForEveryNormal :
    A4LRTTransferClause
  stripHittingAlternativeRecordedAsRichnessDemand :
    A4LRTTransferClause
  bothOpenHemispheresCarryPositiveMass :
    A4LRTTransferClause
  weightedCoareaDensityAtZeroIsPositive :
    A4LRTTransferClause
  pushforwardRichnessStillDependsOnUnprovedTransferWall :
    A4LRTTransferClause
  cA4DefinedAsPositiveLRTSquaredConstant :
    A4LRTTransferClause

canonicalA4LRTTransferClauses :
  List A4LRTTransferClause
canonicalA4LRTTransferClauses =
  outputGreatCircleStripPulledBackForEveryNormal
  ∷ stripHittingAlternativeRecordedAsRichnessDemand
  ∷ bothOpenHemispheresCarryPositiveMass
  ∷ weightedCoareaDensityAtZeroIsPositive
  ∷ pushforwardRichnessStillDependsOnUnprovedTransferWall
  ∷ cA4DefinedAsPositiveLRTSquaredConstant
  ∷ []

A4LRTTransferClauseCount : Nat
A4LRTTransferClauseCount =
  listLength canonicalA4LRTTransferClauses

A4LRTTransferClauseCountIs6 :
  A4LRTTransferClauseCount ≡ 6
A4LRTTransferClauseCountIs6 =
  refl

data A4ErrorSubtractionClause : Set where
  antipodalTubeErrorAbsorbed :
    A4ErrorSubtractionClause
  lowVorticityMassErrorAbsorbed :
    A4ErrorSubtractionClause
  nearAntipodalNullOutputErrorAbsorbed :
    A4ErrorSubtractionClause
  bonyPerturbationErrorAbsorbed :
    A4ErrorSubtractionClause
  residualPositiveForSmallScale :
    A4ErrorSubtractionClause

canonicalA4ErrorSubtractionClauses :
  List A4ErrorSubtractionClause
canonicalA4ErrorSubtractionClauses =
  antipodalTubeErrorAbsorbed
  ∷ lowVorticityMassErrorAbsorbed
  ∷ nearAntipodalNullOutputErrorAbsorbed
  ∷ bonyPerturbationErrorAbsorbed
  ∷ residualPositiveForSmallScale
  ∷ []

A4ErrorSubtractionClauseCount : Nat
A4ErrorSubtractionClauseCount =
  listLength canonicalA4ErrorSubtractionClauses

A4ErrorSubtractionClauseCountIs5 :
  A4ErrorSubtractionClauseCount ≡ 5
A4ErrorSubtractionClauseCountIs5 =
  refl

------------------------------------------------------------------------
-- Downstream blockers.

data DownstreamA4Blocker : Set where
  blockerA5-kappaBiasVanishingFromA4Stationarity :
    DownstreamA4Blocker
  blockerA6-triadicCompensatedLeakageIdentity :
    DownstreamA4Blocker
  blockerA7-residualDepletionGronwall :
    DownstreamA4Blocker
  blockerA8-fullLocalDefectMonotonicity :
    DownstreamA4Blocker
  blockerA9-CKNBKMClosure :
    DownstreamA4Blocker
  blockerClayAuthority :
    DownstreamA4Blocker

canonicalDownstreamA4Blockers :
  List DownstreamA4Blocker
canonicalDownstreamA4Blockers =
  blockerA5-kappaBiasVanishingFromA4Stationarity
  ∷ blockerA6-triadicCompensatedLeakageIdentity
  ∷ blockerA7-residualDepletionGronwall
  ∷ blockerA8-fullLocalDefectMonotonicity
  ∷ blockerA9-CKNBKMClosure
  ∷ blockerClayAuthority
  ∷ []

DownstreamA4BlockerCount : Nat
DownstreamA4BlockerCount =
  listLength canonicalDownstreamA4Blockers

DownstreamA4BlockerCountIs6 :
  DownstreamA4BlockerCount ≡ 6
DownstreamA4BlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Fail-closed flags.

data A4OutputSupportCoareaResidualPromotion : Set where

A4OutputSupportCoareaResidualPromotionImpossibleHere :
  A4OutputSupportCoareaResidualPromotion →
  ⊥
A4OutputSupportCoareaResidualPromotionImpossibleHere ()

NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded : Bool
NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded =
  true

A4ProofContentCompleteReceipt : Bool
A4ProofContentCompleteReceipt =
  false

A4PromotesA5KappaBiasVanishing : Bool
A4PromotesA5KappaBiasVanishing =
  false

A4PromotesA6TriadicCompensatedLeakage : Bool
A4PromotesA6TriadicCompensatedLeakage =
  false

A4PromotesA7ResidualDepletion : Bool
A4PromotesA7ResidualDepletion =
  false

A4PromotesCKNBKMClosure : Bool
A4PromotesCKNBKMClosure =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsNSA4OutputSupportCoareaResidualTheoremBoundary :
  NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded ≡ true
recordsNSA4OutputSupportCoareaResidualTheoremBoundary =
  refl

keepsA4ProofContentIncomplete :
  A4ProofContentCompleteReceipt ≡ false
keepsA4ProofContentIncomplete =
  refl

keepsA5False :
  A4PromotesA5KappaBiasVanishing ≡ false
keepsA5False =
  refl

keepsA6False :
  A4PromotesA6TriadicCompensatedLeakage ≡ false
keepsA6False =
  refl

keepsA7False :
  A4PromotesA7ResidualDepletion ≡ false
keepsA7False =
  refl

keepsCKNBKMFalse :
  A4PromotesCKNBKMClosure ≡ false
keepsCKNBKMFalse =
  refl

keepsClayFalse :
  clayNavierStokesPromoted ≡ false
keepsClayFalse =
  refl

keepsTerminalFalse :
  terminalPromotion ≡ false
keepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker-3 A4 theorem-ladder receipt owns the output-support coarea/Jacobian surfaces while keeping direct validation standalone and 10s-safe."

requirementString : String
requirementString =
  "R: Record the exact theorem-facing ladder A4.1 direction-map regularity -> A4.2 Jacobian lower-bound / nondegeneracy -> A4.3 coarea propagation -> A4.4 strip-hitting/pushforward richness -> A4.5 uniformity across the Type-I rescaling family, while keeping every unresolved transfer wall explicit."

codeArtifactString : String
codeArtifactString =
  "C: NSA4OutputSupportCoareaResidualTheoremBoundary.agda imports the child A4 surfaces, exports an explicit A4.1-A4.5 candidate ladder with sharper clause names, and keeps all theorem/promotion flags fail-closed."

stateString : String
stateString =
  "S: The receipt is recorded but not complete: the A4.2 Jacobian/nondegeneracy bridge, A4.3 coarea propagation wall, A4.4 strip-hitting/pushforward richness wall, and A4.5 Type-I-rescaling-family uniformity wall remain unresolved, so A4 proof completeness and every downstream promotion stay false."

latticeString : String
latticeString =
  "L: A4.1 direction-map regularity -> A4.2 Jacobian lower-bound / nondegeneracy -> A4.3 coarea propagation -> A4.4 strip-hitting/pushforward richness -> A4.5 uniformity across the Type-I rescaling family -> downstream A5/A6/A7 blockers."

proposalString : String
proposalString =
  "P: Use this as the honest lightweight A4 receipt until the A4.1-A4.5 ladder is discharged quantitatively, especially the A4.2 Jacobian/nondegeneracy route, A4.3 coarea propagation, A4.4 strip-hitting pushforward richness, and A4.5 Type-I-rescaling-family uniformity walls."

governanceString : String
governanceString =
  "G: Fail closed: the receipt may expose the theorem checklist and candidate route, but it cannot hide the exact open A4.1-A4.5 gaps and it does not discharge A5/A6/A7 or external authority."

gapString : String
gapString =
  "F: Exact route gaps are the A4.1 regularity upgrade, the A4.2 Jacobian lower-bound / nondegeneracy route, A4.3 coarea propagation, A4.4 strip-hitting/pushforward richness for every normal, A4.5 uniformity across the Type-I rescaling family, and then the downstream A5/A6/A7/A8/A9/Clay blockers."

record NSA4OutputSupportCoareaResidualTheoremBoundary : Set where
  field
    O :
      String
    OIsCanonical :
      O ≡ organizationString
    R :
      String
    RIsCanonical :
      R ≡ requirementString
    C :
      String
    CIsCanonical :
      C ≡ codeArtifactString
    S :
      String
    SIsCanonical :
      S ≡ stateString
    L :
      String
    LIsCanonical :
      L ≡ latticeString
    P :
      String
    PIsCanonical :
      P ≡ proposalString
    G :
      String
    GIsCanonical :
      G ≡ governanceString
    F :
      String
    FIsCanonical :
      F ≡ gapString
    importedSupport :
      ImportedA4CoareaCandidateChainSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedA4CoareaCandidateChainSupport
    proofParts :
      List A4ProofPart
    proofPartsAreCanonical :
      proofParts ≡ canonicalA4ProofParts
    proofPartCountIsFive :
      A4ProofPartCount ≡ 5
    candidateChainStages :
      List A4CandidateChainStage
    candidateChainStagesAreCanonical :
      candidateChainStages ≡ canonicalA4CandidateChainStages
    candidateChainStageCountIsFive :
      A4CandidateChainStageCount ≡ 5
    unresolvedRouteSteps :
      List A4UnresolvedRouteStep
    unresolvedRouteStepsAreCanonical :
      unresolvedRouteSteps ≡ canonicalA4UnresolvedRouteSteps
    unresolvedRouteStepCountIsFive :
      A4UnresolvedRouteStepCount ≡ 5
    localDerivativeClauses :
      List A4LocalDerivativeClause
    localDerivativeClausesAreCanonical :
      localDerivativeClauses ≡ canonicalA4LocalDerivativeClauses
    localDerivativeClauseCountIsFive :
      A4LocalDerivativeClauseCount ≡ 5
    coareaDensityClauses :
      List A4CoareaDensityClause
    coareaDensityClausesAreCanonical :
      coareaDensityClauses ≡ canonicalA4CoareaDensityClauses
    coareaDensityClauseCountIsSix :
      A4CoareaDensityClauseCount ≡ 6
    lrtTransferClauses :
      List A4LRTTransferClause
    lrtTransferClausesAreCanonical :
      lrtTransferClauses ≡ canonicalA4LRTTransferClauses
    lrtTransferClauseCountIsSix :
      A4LRTTransferClauseCount ≡ 6
    errorSubtractionClauses :
      List A4ErrorSubtractionClause
    errorSubtractionClausesAreCanonical :
      errorSubtractionClauses ≡ canonicalA4ErrorSubtractionClauses
    errorSubtractionClauseCountIsFive :
      A4ErrorSubtractionClauseCount ≡ 5
    downstreamBlockers :
      List DownstreamA4Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA4Blockers
    downstreamBlockerCountIsSix :
      DownstreamA4BlockerCount ≡ 6
    boundaryRecordedTrue :
      NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded ≡ true
    A4ProofContentCompleteReceiptFalse :
      A4ProofContentCompleteReceipt ≡ false
    A5StillFalse :
      A4PromotesA5KappaBiasVanishing ≡ false
    A6StillFalse :
      A4PromotesA6TriadicCompensatedLeakage ≡ false
    A7StillFalse :
      A4PromotesA7ResidualDepletion ≡ false
    CKNBKMStillFalse :
      A4PromotesCKNBKMClosure ≡ false
    clayNavierStokesPromotedStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4OutputSupportCoareaResidualTheoremBoundary :
  NSA4OutputSupportCoareaResidualTheoremBoundary
canonicalNSA4OutputSupportCoareaResidualTheoremBoundary =
  record
    { O =
        organizationString
    ; OIsCanonical =
        refl
    ; R =
        requirementString
    ; RIsCanonical =
        refl
    ; C =
        codeArtifactString
    ; CIsCanonical =
        refl
    ; S =
        stateString
    ; SIsCanonical =
        refl
    ; L =
        latticeString
    ; LIsCanonical =
        refl
    ; P =
        proposalString
    ; PIsCanonical =
        refl
    ; G =
        governanceString
    ; GIsCanonical =
        refl
    ; F =
        gapString
    ; FIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedA4CoareaCandidateChainSupport
    ; importedSupportIsCanonical =
        refl
    ; proofParts =
        canonicalA4ProofParts
    ; proofPartsAreCanonical =
        refl
    ; proofPartCountIsFive =
        refl
    ; candidateChainStages =
        canonicalA4CandidateChainStages
    ; candidateChainStagesAreCanonical =
        refl
    ; candidateChainStageCountIsFive =
        refl
    ; unresolvedRouteSteps =
        canonicalA4UnresolvedRouteSteps
    ; unresolvedRouteStepsAreCanonical =
        refl
    ; unresolvedRouteStepCountIsFive =
        refl
    ; localDerivativeClauses =
        canonicalA4LocalDerivativeClauses
    ; localDerivativeClausesAreCanonical =
        refl
    ; localDerivativeClauseCountIsFive =
        refl
    ; coareaDensityClauses =
        canonicalA4CoareaDensityClauses
    ; coareaDensityClausesAreCanonical =
        refl
    ; coareaDensityClauseCountIsSix =
        refl
    ; lrtTransferClauses =
        canonicalA4LRTTransferClauses
    ; lrtTransferClausesAreCanonical =
        refl
    ; lrtTransferClauseCountIsSix =
        refl
    ; errorSubtractionClauses =
        canonicalA4ErrorSubtractionClauses
    ; errorSubtractionClausesAreCanonical =
        refl
    ; errorSubtractionClauseCountIsFive =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA4Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; downstreamBlockerCountIsSix =
        refl
    ; boundaryRecordedTrue =
        refl
    ; A4ProofContentCompleteReceiptFalse =
        refl
    ; A5StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; A7StillFalse =
        refl
    ; CKNBKMStillFalse =
        refl
    ; clayNavierStokesPromotedStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
