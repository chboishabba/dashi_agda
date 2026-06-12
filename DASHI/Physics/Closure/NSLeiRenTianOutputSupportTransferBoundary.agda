module DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary as Stationarity
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary as LRT
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary as Sheaf

------------------------------------------------------------------------
-- NS A4 Lei-Ren-Tian output-support transfer boundary.
--
-- Coupling target:
--
--   physical-space vorticity direction great-circle richness
--     -> Fourier triadic output direction great-circle richness
--     -> uniform output-support transfer constant across Type-I rescalings
--
-- for Abel triadic measures.
--
-- Required assumptions are recorded explicitly: Whitney/frame/localization
-- compatibility, quantitative Jacobian/coarea control on
-- Phi(theta1,theta2), and no angular collapse.  This module is the A4 parent
-- transfer socket.  It does not prove the physical-to-Fourier angular
-- coupling, does not prove the uniform Type-I-rescaling transfer constant,
-- does not lift output-direction support, does not construct the PDE Abel
-- measure support theorem, and does not promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Coupling carriers.

data PhysicalVorticityDirectionRichness : Set where
  physicalVorticityDirectionsHitEveryGreatCircle :
    LRT.HighVorticityDirectionSet →
    LRT.GreatCircleHittingProperty →
    PhysicalVorticityDirectionRichness

data FourierTriadicOutputDirectionRichness : Set where
  fourierTriadicOutputDirectionsHitEveryGreatCircle :
    Sheaf.TriadicDefectMeasureSection →
    Sheaf.OutputProjection →
    Sheaf.LeiRenTianOutputGreatCircleCondition →
    FourierTriadicOutputDirectionRichness

data AbelTriadicOutputMeasureSupport : Set where
  abelTriadicOutputSupportForLRT :
    Sheaf.AbelTriadicInteractionDefectMeasure →
    Sheaf.TriadicDefectMeasureSection →
    Sheaf.OutputProjection →
    AbelTriadicOutputMeasureSupport

data WhitneyFrameLocalizationAssumption : Set where
  whitneyFrameLocalizationCompatible :
    Sheaf.TriadicPatch →
    Sheaf.OutputProjection →
    WhitneyFrameLocalizationAssumption

data NoAngularCollapseAssumption : Set where
  noCollapseFromPhysicalDirectionsToFourierOutputs :
    LRT.GreatCircleHittingProperty →
    Sheaf.OutputProjection →
    NoAngularCollapseAssumption

data PhysicalToFourierAngularCouplingTarget : Set where
  physicalVorticityGreatCircleRichnessTransfersToFourierOutputGreatCircleRichness :
    PhysicalVorticityDirectionRichness →
    AbelTriadicOutputMeasureSupport →
    WhitneyFrameLocalizationAssumption →
    NoAngularCollapseAssumption →
    FourierTriadicOutputDirectionRichness →
    PhysicalToFourierAngularCouplingTarget

data DirectionMapRegularitySocket : Set where
  directionMapRegularityA4-1RequestedFromWhitneyLocalizedTriads :
    WhitneyFrameLocalizationAssumption →
    NoAngularCollapseAssumption →
    DirectionMapRegularitySocket

data CoareaJacobianLowerBoundAttemptSocket : Set where
  jacobianNondegeneracyA4-2AndCoareaA4-3RequestedForOutputDirectionMap :
    DirectionMapRegularitySocket →
    FourierTriadicOutputDirectionRichness →
    CoareaJacobianLowerBoundAttemptSocket

data PushforwardStripHittingConsequenceSocket : Set where
  stripHittingPushforwardRichnessA4-4ShouldHitEveryOutputGreatCircle :
    CoareaJacobianLowerBoundAttemptSocket →
    AbelTriadicOutputMeasureSupport →
    PushforwardStripHittingConsequenceSocket

data UniformInRescalingConstantObligationSocket : Set where
  uniformityA4-5AcrossTypeIRescalingFamilyRemainsExplicitObligation :
    PushforwardStripHittingConsequenceSocket →
    PhysicalToFourierAngularCouplingTarget →
    UniformInRescalingConstantObligationSocket

canonicalPhysicalVorticityDirectionRichness :
  PhysicalVorticityDirectionRichness
canonicalPhysicalVorticityDirectionRichness =
  physicalVorticityDirectionsHitEveryGreatCircle
    LRT.canonicalHighVorticityDirectionSet
    LRT.canonicalGreatCircleHittingProperty

canonicalFourierTriadicOutputDirectionRichness :
  FourierTriadicOutputDirectionRichness
canonicalFourierTriadicOutputDirectionRichness =
  fourierTriadicOutputDirectionsHitEveryGreatCircle
    Sheaf.canonicalGlobalTriadicSection
    Sheaf.canonicalOutputProjection
    Sheaf.canonicalLRTOutputCondition

canonicalAbelTriadicOutputMeasureSupport :
  AbelTriadicOutputMeasureSupport
canonicalAbelTriadicOutputMeasureSupport =
  abelTriadicOutputSupportForLRT
    Sheaf.canonicalAbelTriadicMeasure
    Sheaf.canonicalGlobalTriadicSection
    Sheaf.canonicalOutputProjection

canonicalWhitneyFrameLocalizationAssumption :
  WhitneyFrameLocalizationAssumption
canonicalWhitneyFrameLocalizationAssumption =
  whitneyFrameLocalizationCompatible
    Sheaf.canonicalResonantPatch
    Sheaf.canonicalOutputProjection

canonicalNoAngularCollapseAssumption :
  NoAngularCollapseAssumption
canonicalNoAngularCollapseAssumption =
  noCollapseFromPhysicalDirectionsToFourierOutputs
    LRT.canonicalGreatCircleHittingProperty
    Sheaf.canonicalOutputProjection

canonicalPhysicalToFourierAngularCouplingTarget :
  PhysicalToFourierAngularCouplingTarget
canonicalPhysicalToFourierAngularCouplingTarget =
  physicalVorticityGreatCircleRichnessTransfersToFourierOutputGreatCircleRichness
    canonicalPhysicalVorticityDirectionRichness
    canonicalAbelTriadicOutputMeasureSupport
    canonicalWhitneyFrameLocalizationAssumption
    canonicalNoAngularCollapseAssumption
    canonicalFourierTriadicOutputDirectionRichness

canonicalDirectionMapRegularitySocket :
  DirectionMapRegularitySocket
canonicalDirectionMapRegularitySocket =
  directionMapRegularityA4-1RequestedFromWhitneyLocalizedTriads
    canonicalWhitneyFrameLocalizationAssumption
    canonicalNoAngularCollapseAssumption

canonicalCoareaJacobianLowerBoundAttemptSocket :
  CoareaJacobianLowerBoundAttemptSocket
canonicalCoareaJacobianLowerBoundAttemptSocket =
  jacobianNondegeneracyA4-2AndCoareaA4-3RequestedForOutputDirectionMap
    canonicalDirectionMapRegularitySocket
    canonicalFourierTriadicOutputDirectionRichness

canonicalPushforwardStripHittingConsequenceSocket :
  PushforwardStripHittingConsequenceSocket
canonicalPushforwardStripHittingConsequenceSocket =
  stripHittingPushforwardRichnessA4-4ShouldHitEveryOutputGreatCircle
    canonicalCoareaJacobianLowerBoundAttemptSocket
    canonicalAbelTriadicOutputMeasureSupport

canonicalUniformInRescalingConstantObligationSocket :
  UniformInRescalingConstantObligationSocket
canonicalUniformInRescalingConstantObligationSocket =
  uniformityA4-5AcrossTypeIRescalingFamilyRemainsExplicitObligation
    canonicalPushforwardStripHittingConsequenceSocket
    canonicalPhysicalToFourierAngularCouplingTarget

------------------------------------------------------------------------
-- A4 dependency rows and blockers.

data OutputSupportTransferDependency : Set where
  leiRenTianPhysicalGreatCircleCriterionDependency :
    OutputSupportTransferDependency
  abelTriadicMeasureDependency :
    OutputSupportTransferDependency
  triadicOutputProjectionDependency :
    OutputSupportTransferDependency
  whitneyFrameLocalizationDependency :
    OutputSupportTransferDependency
  A4-1DirectionMapRegularityDependency :
    OutputSupportTransferDependency
  A4-2A4-3QuantitativePhiJacobianCoareaDependency :
    OutputSupportTransferDependency
  A4-4PushforwardStripHittingRichnessDependency :
    OutputSupportTransferDependency
  noAngularCollapseDependency :
    OutputSupportTransferDependency
  A4-5UniformityAcrossTypeIRescalingFamilyDependency :
    OutputSupportTransferDependency
  stationarityA4BoundaryDependency :
    OutputSupportTransferDependency

canonicalOutputSupportTransferDependencies :
  List OutputSupportTransferDependency
canonicalOutputSupportTransferDependencies =
  leiRenTianPhysicalGreatCircleCriterionDependency
  ∷ abelTriadicMeasureDependency
  ∷ triadicOutputProjectionDependency
  ∷ whitneyFrameLocalizationDependency
  ∷ A4-1DirectionMapRegularityDependency
  ∷ A4-2A4-3QuantitativePhiJacobianCoareaDependency
  ∷ A4-4PushforwardStripHittingRichnessDependency
  ∷ noAngularCollapseDependency
  ∷ A4-5UniformityAcrossTypeIRescalingFamilyDependency
  ∷ stationarityA4BoundaryDependency
  ∷ []

outputSupportTransferDependencyCount : Nat
outputSupportTransferDependencyCount =
  listLength canonicalOutputSupportTransferDependencies

outputSupportTransferDependencyCountIs10 :
  outputSupportTransferDependencyCount ≡ 10
outputSupportTransferDependencyCountIs10 =
  refl

data OutputSupportTransferClause : Set where
  clausePhysicalGreatCircleHittingIsTheSeedInput :
    OutputSupportTransferClause
  clauseNoAngularCollapseMustSurviveThePhysicalToFourierMap :
    OutputSupportTransferClause
  clauseDirectionMapRegularityJacobianAndCoareaFormTheMiddleLadder :
    OutputSupportTransferClause
  clausePushforwardStripHittingCreatesFourierGreatCircleRichness :
    OutputSupportTransferClause
  clauseUniformOutputSupportConstantMustPersistAcrossTypeIRescaling :
    OutputSupportTransferClause
  clauseFailClosedPromotionPosture :
    OutputSupportTransferClause

canonicalOutputSupportTransferClauses :
  List OutputSupportTransferClause
canonicalOutputSupportTransferClauses =
  clausePhysicalGreatCircleHittingIsTheSeedInput
  ∷ clauseNoAngularCollapseMustSurviveThePhysicalToFourierMap
  ∷ clauseDirectionMapRegularityJacobianAndCoareaFormTheMiddleLadder
  ∷ clausePushforwardStripHittingCreatesFourierGreatCircleRichness
  ∷ clauseUniformOutputSupportConstantMustPersistAcrossTypeIRescaling
  ∷ clauseFailClosedPromotionPosture
  ∷ []

outputSupportTransferClauseCount : Nat
outputSupportTransferClauseCount =
  listLength canonicalOutputSupportTransferClauses

outputSupportTransferClauseCountIs6 :
  outputSupportTransferClauseCount ≡ 6
outputSupportTransferClauseCountIs6 =
  refl

data OutputSupportTransferBlocker : Set where
  missingPhysicalToFourierGreatCircleTransferTheorem :
    OutputSupportTransferBlocker
  missingA4-1DirectionMapRegularityInput :
    OutputSupportTransferBlocker
  missingA4-2A4-3QuantitativePhiJacobianCoareaInput :
    OutputSupportTransferBlocker
  missingA4-4PushforwardDensityToStripHittingRichnessStep :
    OutputSupportTransferBlocker
  missingA4-5UniformityAcrossTypeIRescalingFamilyConstant :
    OutputSupportTransferBlocker
  missingOutputDirectionSupportLift :
    OutputSupportTransferBlocker
  missingPDEAbelMeasureSupportTheorem :
    OutputSupportTransferBlocker
  missingClayPromotion :
    OutputSupportTransferBlocker

canonicalOutputSupportTransferBlockers :
  List OutputSupportTransferBlocker
canonicalOutputSupportTransferBlockers =
  missingPhysicalToFourierGreatCircleTransferTheorem
  ∷ missingA4-1DirectionMapRegularityInput
  ∷ missingA4-2A4-3QuantitativePhiJacobianCoareaInput
  ∷ missingA4-4PushforwardDensityToStripHittingRichnessStep
  ∷ missingA4-5UniformityAcrossTypeIRescalingFamilyConstant
  ∷ missingOutputDirectionSupportLift
  ∷ missingPDEAbelMeasureSupportTheorem
  ∷ missingClayPromotion
  ∷ []

outputSupportTransferBlockerCount : Nat
outputSupportTransferBlockerCount =
  listLength canonicalOutputSupportTransferBlockers

outputSupportTransferBlockerCountIs8 :
  outputSupportTransferBlockerCount ≡ 8
outputSupportTransferBlockerCountIs8 =
  refl

data OutputSupportTransferStatusRow : Set where
  boundaryRecordedStatus :
    OutputSupportTransferStatusRow
  physicalGreatCircleRichnessTargetRecordedStatus :
    OutputSupportTransferStatusRow
  fourierOutputGreatCircleRichnessTargetRecordedStatus :
    OutputSupportTransferStatusRow
  whitneyFrameLocalizationAssumptionRecordedStatus :
    OutputSupportTransferStatusRow
  A4-1DirectionMapRegularitySocketRecordedStatus :
    OutputSupportTransferStatusRow
  A4-2A4-3QuantitativeJacobianCoareaTransferSocketRecordedStatus :
    OutputSupportTransferStatusRow
  A4-4PushforwardStripHittingSocketRecordedStatus :
    OutputSupportTransferStatusRow
  noAngularCollapseAssumptionRecordedStatus :
    OutputSupportTransferStatusRow
  A4-5UniformityAcrossTypeIRescalingFamilyStillFalseStatus :
    OutputSupportTransferStatusRow
  allProofAndPromotionFlagsFalseStatus :
    OutputSupportTransferStatusRow

canonicalOutputSupportTransferStatusRows :
  List OutputSupportTransferStatusRow
canonicalOutputSupportTransferStatusRows =
  boundaryRecordedStatus
  ∷ physicalGreatCircleRichnessTargetRecordedStatus
  ∷ fourierOutputGreatCircleRichnessTargetRecordedStatus
  ∷ whitneyFrameLocalizationAssumptionRecordedStatus
  ∷ A4-1DirectionMapRegularitySocketRecordedStatus
  ∷ A4-2A4-3QuantitativeJacobianCoareaTransferSocketRecordedStatus
  ∷ A4-4PushforwardStripHittingSocketRecordedStatus
  ∷ noAngularCollapseAssumptionRecordedStatus
  ∷ A4-5UniformityAcrossTypeIRescalingFamilyStillFalseStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

outputSupportTransferStatusRowCount : Nat
outputSupportTransferStatusRowCount =
  listLength canonicalOutputSupportTransferStatusRows

outputSupportTransferStatusRowCountIs10 :
  outputSupportTransferStatusRowCount ≡ 10
outputSupportTransferStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data OutputSupportTransferPromotion : Set where

outputSupportTransferPromotionImpossibleHere :
  OutputSupportTransferPromotion →
  ⊥
outputSupportTransferPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSLeiRenTianOutputSupportTransferBoundaryRecorded : Bool
NSLeiRenTianOutputSupportTransferBoundaryRecorded =
  true

physicalVorticityGreatCircleRichnessRecorded : Bool
physicalVorticityGreatCircleRichnessRecorded =
  true

fourierTriadicOutputGreatCircleRichnessRecorded : Bool
fourierTriadicOutputGreatCircleRichnessRecorded =
  true

abelTriadicOutputMeasureSupportTargetRecorded : Bool
abelTriadicOutputMeasureSupportTargetRecorded =
  true

whitneyFrameLocalizationAssumptionRecorded : Bool
whitneyFrameLocalizationAssumptionRecorded =
  true

noAngularCollapseAssumptionRecorded : Bool
noAngularCollapseAssumptionRecorded =
  true

physicalToFourierAngularCouplingProved : Bool
physicalToFourierAngularCouplingProved =
  false

outputDirectionSupportLiftProved : Bool
outputDirectionSupportLiftProved =
  false

pdeAbelMeasureSupportTheoremProved : Bool
pdeAbelMeasureSupportTheoremProved =
  false

leiRenTianOutputSupportTransferProved : Bool
leiRenTianOutputSupportTransferProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

mechanismExhaustionForFullClayNS : Bool
mechanismExhaustionForFullClayNS =
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

lrtGreatCircleBoundaryAnchor : Bool
lrtGreatCircleBoundaryAnchor =
  LRT.NSLeiRenTianGreatCircleCriterionBoundaryRecorded

stationarityA4BoundaryAnchor : Bool
stationarityA4BoundaryAnchor =
  Stationarity.A4LRTOutputSupportTransferRecorded

stationarityA4ProofStillFalseAnchor : Bool
stationarityA4ProofStillFalseAnchor =
  Stationarity.A4LRTOutputSupportTransferProved

sheafLRTOutputConditionAnchor : Bool
sheafLRTOutputConditionAnchor =
  Sheaf.lrtOutputConditionRecorded

recordsBoundary :
  NSLeiRenTianOutputSupportTransferBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsPhysicalRichness :
  physicalVorticityGreatCircleRichnessRecorded ≡ true
recordsPhysicalRichness =
  refl

recordsFourierOutputRichness :
  fourierTriadicOutputGreatCircleRichnessRecorded ≡ true
recordsFourierOutputRichness =
  refl

recordsAbelTriadicOutputMeasureSupportTarget :
  abelTriadicOutputMeasureSupportTargetRecorded ≡ true
recordsAbelTriadicOutputMeasureSupportTarget =
  refl

recordsWhitneyFrameLocalizationAssumption :
  whitneyFrameLocalizationAssumptionRecorded ≡ true
recordsWhitneyFrameLocalizationAssumption =
  refl

recordsNoAngularCollapseAssumption :
  noAngularCollapseAssumptionRecorded ≡ true
recordsNoAngularCollapseAssumption =
  refl

keepsPhysicalToFourierAngularCouplingFalse :
  physicalToFourierAngularCouplingProved ≡ false
keepsPhysicalToFourierAngularCouplingFalse =
  refl

keepsOutputDirectionSupportLiftFalse :
  outputDirectionSupportLiftProved ≡ false
keepsOutputDirectionSupportLiftFalse =
  refl

keepsPDEAbelMeasureSupportTheoremFalse :
  pdeAbelMeasureSupportTheoremProved ≡ false
keepsPDEAbelMeasureSupportTheoremFalse =
  refl

keepsLeiRenTianOutputSupportTransferFalse :
  leiRenTianOutputSupportTransferProved ≡ false
keepsLeiRenTianOutputSupportTransferFalse =
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

outputSupportTransferTheoremLadderSummary : String
outputSupportTransferTheoremLadderSummary =
  "The output-support ladder is: physical great-circle hitting enters A4, no-angular-collapse preserves directional richness, A4.1-A4.3 supply regularity/Jacobian/coarea, A4.4 yields Fourier strip-hitting richness, A4.5 asks for a uniform Type-I output-support constant, and promotion remains fail-closed until the full chain is proved."

organizationString : String
organizationString =
  "O: Own the self-contained A4 parent transfer lane only, packaging the LRT physical-to-Fourier route as an explicit in-repo theorem ladder with a named no-angular-collapse middle step."

requirementString : String
requirementString =
  "R: Record the exact A4 theorem ladder: physical great-circle richness enters the route, no-angular-collapse preserves direction richness, A4.1 direction-map regularity plus A4.2 Jacobian nondegeneracy and A4.3 coarea provide the middle transfer, A4.4 yields Fourier strip-hitting richness, and A4.5 requests a uniform output-support constant across the Type-I rescaling family, while every proof and promotion flag stays false."

codeArtifactString : String
codeArtifactString =
  "C: NSLeiRenTianOutputSupportTransferBoundary anchors LRT richness, Abel triadic stationarity A4, triadic output projection, an explicit six-clause transfer ladder, and the A4.1-A4.5 child sockets consumed by the fail-closed uniform-transfer lane."

stateString : String
stateString =
  "S: Boundary is recorded only; the physical-to-Fourier great-circle transfer theorem, the no-angular-collapse proof, the A4.1 regularity input, the A4.2/A4.3 Jacobian-coarea input, the A4.4 strip-hitting richness step, the A4.5 uniform Type-I-rescaling-family constant, the output-support lift, the PDE Abel support theorem, and Clay promotion are all still absent."

latticeString : String
latticeString =
  "L: LRT physical great-circle criterion -> no-angular-collapse physical/Fourier compatibility -> Abel triadic measure support -> A4.1 direction-map regularity -> A4.2 Jacobian lower-bound / nondegeneracy -> A4.3 coarea propagation -> A4.4 strip-hitting / pushforward richness -> A4.5 uniformity across the Type-I rescaling family -> future A4 stationarity consumer."

proposalString : String
proposalString =
  "P: Promote A4 only after proving the physical-to-Fourier great-circle transfer theorem together with no-angular-collapse and the A4.1-A4.5 child estimates that yield a uniform output-support constant across the Type-I rescaling family, then closing the support-lift and PDE Abel support consumers in the same analytic framework."

governanceString : String
governanceString =
  "G: This is a fail-closed theorem socket: recorded bookkeeping is true, while the transfer theorem, no-angular-collapse proof, quantitative constant, support lift, A4, Clay, and terminal promotions remain false."

gapString : String
gapString =
  "F: Blockers are the missing physical-to-Fourier great-circle transfer theorem, missing no-angular-collapse proof, missing A4.1 direction-map regularity input, missing A4.2/A4.3 quantitative Phi-Jacobian/coarea input, missing A4.4 strip-hitting / pushforward richness step, missing A4.5 uniformity-across-the-Type-I-rescaling-family constant, missing output-direction support lift, missing PDE Abel measure support theorem, and missing Clay promotion."

------------------------------------------------------------------------
-- Canonical receipt.

record NSLeiRenTianOutputSupportTransferBoundary : Set where
  constructor nsLeiRenTianOutputSupportTransferBoundary
  field
    physicalRichness :
      PhysicalVorticityDirectionRichness
    physicalRichnessIsCanonical :
      physicalRichness ≡ canonicalPhysicalVorticityDirectionRichness
    fourierOutputRichness :
      FourierTriadicOutputDirectionRichness
    fourierOutputRichnessIsCanonical :
      fourierOutputRichness ≡ canonicalFourierTriadicOutputDirectionRichness
    abelTriadicOutputSupport :
      AbelTriadicOutputMeasureSupport
    abelTriadicOutputSupportIsCanonical :
      abelTriadicOutputSupport ≡ canonicalAbelTriadicOutputMeasureSupport
    whitneyFrameLocalization :
      WhitneyFrameLocalizationAssumption
    whitneyFrameLocalizationIsCanonical :
      whitneyFrameLocalization ≡ canonicalWhitneyFrameLocalizationAssumption
    noAngularCollapse :
      NoAngularCollapseAssumption
    noAngularCollapseIsCanonical :
      noAngularCollapse ≡ canonicalNoAngularCollapseAssumption
    directionMapRegularitySocket :
      DirectionMapRegularitySocket
    directionMapRegularitySocketIsCanonical :
      directionMapRegularitySocket ≡ canonicalDirectionMapRegularitySocket
    coareaJacobianLowerBoundAttemptSocket :
      CoareaJacobianLowerBoundAttemptSocket
    coareaJacobianLowerBoundAttemptSocketIsCanonical :
      coareaJacobianLowerBoundAttemptSocket
        ≡ canonicalCoareaJacobianLowerBoundAttemptSocket
    pushforwardStripHittingConsequenceSocket :
      PushforwardStripHittingConsequenceSocket
    pushforwardStripHittingConsequenceSocketIsCanonical :
      pushforwardStripHittingConsequenceSocket
        ≡ canonicalPushforwardStripHittingConsequenceSocket
    uniformInRescalingConstantObligationSocket :
      UniformInRescalingConstantObligationSocket
    uniformInRescalingConstantObligationSocketIsCanonical :
      uniformInRescalingConstantObligationSocket
        ≡ canonicalUniformInRescalingConstantObligationSocket
    transferTarget :
      PhysicalToFourierAngularCouplingTarget
    transferTargetIsCanonical :
      transferTarget ≡ canonicalPhysicalToFourierAngularCouplingTarget
    dependencies :
      List OutputSupportTransferDependency
    dependenciesAreCanonical :
      dependencies ≡ canonicalOutputSupportTransferDependencies
    theoremClauses :
      List OutputSupportTransferClause
    theoremClausesAreCanonical :
      theoremClauses ≡ canonicalOutputSupportTransferClauses
    theoremClauseCount :
      Nat
    theoremClauseCountIsCanonical :
      theoremClauseCount ≡ outputSupportTransferClauseCount
    theoremClauseCountProof :
      theoremClauseCount ≡ 6
    theoremLadderSummary :
      String
    theoremLadderSummaryIsCanonical :
      theoremLadderSummary ≡ outputSupportTransferTheoremLadderSummary
    blockers :
      List OutputSupportTransferBlocker
    blockersAreCanonical :
      blockers ≡ canonicalOutputSupportTransferBlockers
    statuses :
      List OutputSupportTransferStatusRow
    statusesAreCanonical :
      statuses ≡ canonicalOutputSupportTransferStatusRows
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
      NSLeiRenTianOutputSupportTransferBoundaryRecorded ≡ true
    physicalRichnessRecorded :
      physicalVorticityGreatCircleRichnessRecorded ≡ true
    fourierRichnessRecorded :
      fourierTriadicOutputGreatCircleRichnessRecorded ≡ true
    abelSupportTargetRecorded :
      abelTriadicOutputMeasureSupportTargetRecorded ≡ true
    whitneyAssumptionRecorded :
      whitneyFrameLocalizationAssumptionRecorded ≡ true
    noCollapseAssumptionRecorded :
      noAngularCollapseAssumptionRecorded ≡ true
    angularCouplingProofFalse :
      physicalToFourierAngularCouplingProved ≡ false
    supportLiftProofFalse :
      outputDirectionSupportLiftProved ≡ false
    pdeAbelSupportProofFalse :
      pdeAbelMeasureSupportTheoremProved ≡ false
    outputSupportTransferProofFalse :
      leiRenTianOutputSupportTransferProved ≡ false
    claySolvedFalse :
      fullClayNSSolved ≡ false
    clayPromotionFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSLeiRenTianOutputSupportTransferBoundary public

canonicalNSLeiRenTianOutputSupportTransferBoundary :
  NSLeiRenTianOutputSupportTransferBoundary
canonicalNSLeiRenTianOutputSupportTransferBoundary =
  nsLeiRenTianOutputSupportTransferBoundary
    canonicalPhysicalVorticityDirectionRichness
    refl
    canonicalFourierTriadicOutputDirectionRichness
    refl
    canonicalAbelTriadicOutputMeasureSupport
    refl
    canonicalWhitneyFrameLocalizationAssumption
    refl
    canonicalNoAngularCollapseAssumption
    refl
    canonicalDirectionMapRegularitySocket
    refl
    canonicalCoareaJacobianLowerBoundAttemptSocket
    refl
    canonicalPushforwardStripHittingConsequenceSocket
    refl
    canonicalUniformInRescalingConstantObligationSocket
    refl
    canonicalPhysicalToFourierAngularCouplingTarget
    refl
    canonicalOutputSupportTransferDependencies
    refl
    canonicalOutputSupportTransferClauses
    refl
    outputSupportTransferClauseCount
    refl
    outputSupportTransferClauseCountIs6
    outputSupportTransferTheoremLadderSummary
    refl
    canonicalOutputSupportTransferBlockers
    refl
    canonicalOutputSupportTransferStatusRows
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
