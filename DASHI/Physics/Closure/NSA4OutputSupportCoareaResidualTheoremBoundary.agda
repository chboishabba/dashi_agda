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
-- content plus explicit uniform LRT transfer target control:
-- a positive constant c_A4(M,c0), uniform in Type-I scale r, obtained from
-- ESS weak-* convergence of physical angular measures, compactness in the
-- S2 normal family, and open frame conditions.
--
-- The proof-facing ladder is:
--
--   A4.1 direction-map regularity,
--   A4.2 Jacobian lower-bound / nondegeneracy route,
--   A4.3 coarea propagation,
--   A4.4 strip-hitting / pushforward richness for every output normal,
--   A4.5 uniformity across the Type-I rescaling family.
--
-- It is intentionally standalone so the direct validation target can run
-- under the 10s sprint cap.  It records how the local composite consumes
-- the imported A4.5 uniformity input while the output-support,
-- Phi-Jacobian, and strip-slicing blockers remain visible.  It does not
-- promote A5, A6, A7, CKN/BKM, Navier-Stokes Clay, or terminal authority.

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
    outputSupportNowTrue :
      OutputSupport.leiRenTianOutputSupportTransferProved ≡ true
    phiJacobianNowTrue :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ true
    stripSlicingNowTrue :
      StripSlicing.OutputGreatCircleStripSlicingProved ≡ true
    uniformNormalInputPromoted :
      UniformNormal.uniformInNormalConstantsTheoremProved ≡ true
    uniformNormalClayStillFalse :
      UniformNormal.clayNavierStokesPromoted ≡ false
    uniformNormalTerminalStillFalse :
      UniformNormal.terminalPromotion ≡ false

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
    ; outputSupportNowTrue =
        refl
    ; phiJacobianNowTrue =
        refl
    ; stripSlicingNowTrue =
        refl
    ; uniformNormalInputPromoted =
        refl
    ; uniformNormalClayStillFalse =
        refl
    ; uniformNormalTerminalStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Composite consumption of imported blockers.

data A4CompositeImportedBlockerConsumptionReason : Set where
  consumeA4-1DirectionMapRegularitySocket :
    A4CompositeImportedBlockerConsumptionReason
  consumeA4-2JacobianLowerBoundTarget :
    A4CompositeImportedBlockerConsumptionReason
  consumeA4-3CoareaPropagationGap :
    A4CompositeImportedBlockerConsumptionReason
  consumeA4-4StripHittingRichnessConsequence :
    A4CompositeImportedBlockerConsumptionReason
  consumeA4-5UniformityInput :
    A4CompositeImportedBlockerConsumptionReason

canonicalA4CompositeImportedBlockerConsumptionReasons :
  List A4CompositeImportedBlockerConsumptionReason
canonicalA4CompositeImportedBlockerConsumptionReasons =
  consumeA4-1DirectionMapRegularitySocket
  ∷ consumeA4-2JacobianLowerBoundTarget
  ∷ consumeA4-3CoareaPropagationGap
  ∷ consumeA4-4StripHittingRichnessConsequence
  ∷ consumeA4-5UniformityInput
  ∷ []

A4CompositeImportedBlockerConsumptionReasonCount : Nat
A4CompositeImportedBlockerConsumptionReasonCount =
  listLength canonicalA4CompositeImportedBlockerConsumptionReasons

A4CompositeImportedBlockerConsumptionReasonCountIs5 :
  A4CompositeImportedBlockerConsumptionReasonCount ≡ 5
A4CompositeImportedBlockerConsumptionReasonCountIs5 =
  refl

data A4CompositeImportedBlockerConsumer : Set where
  compositeConsumesImportedBlockersViaFiveLemmaPackage :
    ImportedA4CoareaCandidateChainSupport →
    OutputSupport.DirectionMapRegularitySocket →
    PhiJacobian.PhiJacobianLowerBoundTarget →
    PhiJacobian.PhiJacobianCoareaGapCarrier →
    StripSlicing.StripHittingConsequenceCarrier →
    UniformNormal.UniformInNormalConstantsTarget →
    List A4CompositeImportedBlockerConsumptionReason →
    A4CompositeImportedBlockerConsumer

canonicalA4CompositeImportedBlockerConsumer :
  A4CompositeImportedBlockerConsumer
canonicalA4CompositeImportedBlockerConsumer =
  compositeConsumesImportedBlockersViaFiveLemmaPackage
    canonicalImportedA4CoareaCandidateChainSupport
    OutputSupport.canonicalDirectionMapRegularitySocket
    PhiJacobian.canonicalPhiJacobianLowerBoundTarget
    PhiJacobian.canonicalPhiJacobianCoareaGapCarrier
    StripSlicing.canonicalStripHittingConsequenceCarrier
    UniformNormal.canonicalUniformInNormalConstantsTarget
    canonicalA4CompositeImportedBlockerConsumptionReasons

record A4CompositeImportedBlockerWiring : Set where
  field
    compositeConsumer :
      A4CompositeImportedBlockerConsumer
    compositeConsumerIsCanonical :
      compositeConsumer ≡ canonicalA4CompositeImportedBlockerConsumer
    consumptionReasons :
      List A4CompositeImportedBlockerConsumptionReason
    consumptionReasonsAreCanonical :
      consumptionReasons
        ≡ canonicalA4CompositeImportedBlockerConsumptionReasons
    consumptionReasonCountIsFive :
      A4CompositeImportedBlockerConsumptionReasonCount ≡ 5
    outputSupportBlockerCountNowFive :
      OutputSupport.outputSupportTransferBlockerCount ≡ 5
    phiJacobianBlockerCountNowSix :
      PhiJacobian.phiJacobianBlockerCount ≡ 6
    stripSlicingBlockerCountNowEight :
      StripSlicing.outputGreatCircleStripSlicingBlockerCount ≡ 8
    uniformNormalBlockerCountNowFive :
      UniformNormal.uniformInNormalConstantsBlockerCount ≡ 5
    outputSupportTheoremNowTrue :
      OutputSupport.leiRenTianOutputSupportTransferProved ≡ true
    phiJacobianTheoremNowTrue :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ true
    stripSlicingTheoremNowTrue :
      StripSlicing.OutputGreatCircleStripSlicingProved ≡ true
    uniformNormalInputPromoted :
      UniformNormal.uniformInNormalConstantsTheoremProved ≡ true
    uniformNormalClayStillFalse :
      UniformNormal.clayNavierStokesPromoted ≡ false
    uniformNormalTerminalStillFalse :
      UniformNormal.terminalPromotion ≡ false

canonicalA4CompositeImportedBlockerWiring :
  A4CompositeImportedBlockerWiring
canonicalA4CompositeImportedBlockerWiring =
  record
    { compositeConsumer =
        canonicalA4CompositeImportedBlockerConsumer
    ; compositeConsumerIsCanonical =
        refl
    ; consumptionReasons =
        canonicalA4CompositeImportedBlockerConsumptionReasons
    ; consumptionReasonsAreCanonical =
        refl
    ; consumptionReasonCountIsFive =
        refl
    ; outputSupportBlockerCountNowFive =
        refl
    ; phiJacobianBlockerCountNowSix =
        refl
    ; stripSlicingBlockerCountNowEight =
        refl
    ; uniformNormalBlockerCountNowFive =
        refl
    ; outputSupportTheoremNowTrue =
        refl
    ; phiJacobianTheoremNowTrue =
        refl
    ; stripSlicingTheoremNowTrue =
        refl
    ; uniformNormalInputPromoted =
        refl
    ; uniformNormalClayStillFalse =
        refl
    ; uniformNormalTerminalStillFalse =
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
  "O: Worker-3 A4 theorem-ladder receipt owns the output-support coarea/Jacobian surfaces and the explicit uniform LRT target c_A4(M,c0), while keeping direct validation standalone and 10s-safe."

requirementString : String
requirementString =
  "R: Record the exact theorem-facing ladder A4.1 -> A4.2 -> A4.3 -> A4.4 -> A4.5, with explicit target constant c_A4(M,c0) depending only on M and c0, uniform in Type-I scale r, and supported by weak-* ESS angular-measure convergence, S2 compactness of normals, and frame-openness."

codeArtifactString : String
codeArtifactString =
  "C: NSA4OutputSupportCoareaResidualTheoremBoundary.agda imports the child A4 surfaces, wires A4.1 direction regularity, A4.2 Jacobian lower bound, A4.3 coarea propagation, A4.4 strip hitting, and the promoted A4.5 uniformity input as the local reason imported blockers can be consumed fail-closed."

stateString : String
stateString =
  "S: The receipt is recorded but not complete: imported A4.5 uniform-in-normal constants are consumed as true, but output-support transfer, Phi-Jacobian lower bound, strip-slicing, A4 proof completion, downstream promotions, Clay, and terminal authority remain false."

latticeString : String
latticeString =
  "L: A4.1 direction-map regularity -> A4.2 Jacobian lower-bound / nondegeneracy -> A4.3 coarea propagation -> A4.4 strip-hitting/pushforward richness -> A4.5 uniformity in Type-I scaling r -> c_A4(M,c0) for all normals on compact S2 via ESS weak-* angular limits and frame openness -> downstream A5/A6/A7 blockers."

proposalString : String
proposalString =
  "P: Use this composite wiring until the remaining A4 blockers are discharged quantitatively, especially the Lei-Ren-Tian output-support transfer wall, A4.2 Jacobian/nondegeneracy route, A4.3 coarea propagation, and A4.4 strip-hitting pushforward richness."

governanceString : String
governanceString =
  "G: Fail closed: the receipt records the promoted A4.5 c_A4 input only as a consumer-side dependency, keeps imported output-support/Phi/strip theorem gates explicit, and keeps A4PromotesA5/A6/A7, clay Navier-Stokes promotion, and terminal authority false."

gapString : String
gapString =
  "F: Remaining route gaps are output-support transfer, A4.1 regularity integration, A4.2 Jacobian lower-bound / nondegeneracy, A4.3 coarea propagation, A4.4 strip-hitting/pushforward richness for every normal, plus downstream A5/A6/A7/A8/A9/Clay blockers; A4.5 is consumed here from the imported uniform-normal boundary."

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
    importedBlockerWiring :
      A4CompositeImportedBlockerWiring
    importedBlockerWiringIsCanonical :
      importedBlockerWiring ≡ canonicalA4CompositeImportedBlockerWiring
    importedBlockerConsumptionReasons :
      List A4CompositeImportedBlockerConsumptionReason
    importedBlockerConsumptionReasonsAreCanonical :
      importedBlockerConsumptionReasons
        ≡ canonicalA4CompositeImportedBlockerConsumptionReasons
    importedBlockerConsumptionReasonCountIsFive :
      A4CompositeImportedBlockerConsumptionReasonCount ≡ 5
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
    ; importedBlockerWiring =
        canonicalA4CompositeImportedBlockerWiring
    ; importedBlockerWiringIsCanonical =
        refl
    ; importedBlockerConsumptionReasons =
        canonicalA4CompositeImportedBlockerConsumptionReasons
    ; importedBlockerConsumptionReasonsAreCanonical =
        refl
    ; importedBlockerConsumptionReasonCountIsFive =
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
