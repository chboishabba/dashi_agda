module DASHI.Core.ClayCrossDomainLiteralFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact as NS
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as NSCritical
import DASHI.Physics.Closure.NSTriadKNCauchyFullVsSignedFluxBoundaryRound484Exact as NSCauchyBoundary
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as YM
import DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact as RH
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Zeta

------------------------------------------------------------------------
-- CROSS-DOMAIN TERMINAL FRONTIER MOTIFS
--
-- Reuse proof-search SHAPE only; never identify mathematical carriers across
-- programmes.
--
-- NS canonical correction (R486)
-- ------------------------------
-- R481-R485 were useful Cauchy proof-search archaeology, but a downstream
-- consumer audit shows that neither the full Cauchy form nor +F(T) is the
-- canonical Clay target.  R282/R423 already own the shortest exact consumer:
-- one cutoff-uniform INTEGRATED signed quadratic-companion heat-cross payment.
-- R423 sends that payment directly to the critical barrier.
--
-- R284/R434, Cauchy/Schur/operator bounds and endpoint decompositions remain
-- optional producer strategies.  Their unpaid children must not silently become
-- mandatory prerequisites of the direct R423 route.
------------------------------------------------------------------------

data TerminalProducerMotif : Set where
  sameObjectRepresentation : TerminalProducerMotif
  assignedAllowancePayment : TerminalProducerMotif
  signedIntegratedPayment : TerminalProducerMotif
  resolvedGramOperatorBound : TerminalProducerMotif
  sourceSemanticsRecovery : TerminalProducerMotif
  conjunctionOfIndependentChildren : TerminalProducerMotif
  downstreamCompilerReuse : TerminalProducerMotif


data Programme : Set where navierStokes yangMills riemannZeta : Programme

data TerminalCoordinate : Set where
  nsCutoffUniformIntegratedSignedCompanionBudget : TerminalCoordinate
  ymRound108Semantics : TerminalCoordinate
  ymRound108BC1SameObject : TerminalCoordinate
  rhOffAllowance : TerminalCoordinate
  rhGammaAllowance : TerminalCoordinate

coordinateProgramme : TerminalCoordinate → Programme
coordinateProgramme nsCutoffUniformIntegratedSignedCompanionBudget = navierStokes
coordinateProgramme ymRound108Semantics = yangMills
coordinateProgramme ymRound108BC1SameObject = yangMills
coordinateProgramme rhOffAllowance = riemannZeta
coordinateProgramme rhGammaAllowance = riemannZeta

primaryMotif : TerminalCoordinate → TerminalProducerMotif
primaryMotif nsCutoffUniformIntegratedSignedCompanionBudget = signedIntegratedPayment
primaryMotif ymRound108Semantics = sourceSemanticsRecovery
primaryMotif ymRound108BC1SameObject = sameObjectRepresentation
primaryMotif rhOffAllowance = assignedAllowancePayment
primaryMotif rhGammaAllowance = assignedAllowancePayment

coordinateReference : TerminalCoordinate → String
coordinateReference nsCutoffUniformIntegratedSignedCompanionBudget =
  "NS: R423 cutoff-uniform integrated signed quadratic-companion heat-cross budget"
coordinateReference ymRound108Semantics = "YM: source-fixed Round108 density semantics"
coordinateReference ymRound108BC1SameObject = "YM: selected potential = BC1 same-object representation weld"
coordinateReference rhOffAllowance = "RH/zeta: universal pole-quotient Off budget <= assigned A_off"
coordinateReference rhGammaAllowance = "RH/zeta: same-taper Gamma budget <= assigned A_Gamma"

------------------------------------------------------------------------
-- Exact NS pins.
------------------------------------------------------------------------

nsCanonicalShortestConsumerIsR423 :
  NS.round486R423IsCanonicalShortestConsumer ≡ true
nsCanonicalShortestConsumerIsR423 = NS.round486R423IsCanonicalShortestConsumerIsTrue

nsR423TargetIsCutoffUniformSignedCompanionBudget :
  NS.round486R423TargetIsCutoffUniformSignedCompanionBudget ≡ true
nsR423TargetIsCutoffUniformSignedCompanionBudget =
  NS.round486R423TargetIsCutoffUniformSignedCompanionBudgetIsTrue

nsCurrentFirstMissingIsDirectR423Budget :
  NS.firstCanonicalNSResidual NS.currentCanonicalNSStatus
  ≡ NS.missingCutoffUniformSignedCompanionBudget
nsCurrentFirstMissingIsDirectR423Budget = NS.currentFirstMissingIsR423Budget

nsCurrentMechanismIsThink :
  NS.mechanismFor (NS.firstCanonicalNSResidual NS.currentCanonicalNSStatus)
  ≡ NS.Think
nsCurrentMechanismIsThink = NS.currentMechanismIsThink

nsDirectR423BudgetStillOpen : NS.round486DirectR423BudgetClosed ≡ false
nsDirectR423BudgetStillOpen = NS.round486DirectR423BudgetClosedIsFalse

nsCrossOutputCoherenceNotRequired : NS.round486CrossOutputCoherenceRequired ≡ false
nsCrossOutputCoherenceNotRequired = NS.round486CrossOutputCoherenceRequiredIsFalse

nsR284DecompositionNotMandatory : NS.round486R284DecompositionMandatory ≡ false
nsR284DecompositionNotMandatory = NS.round486R284DecompositionMandatoryIsFalse

-- Optional R284/R434 producer route remains honestly open at three physical
-- region payments.  These are NOT direct R423 prerequisites.
nsOptionalR284DeepFarLowPhysicalWeldOpen :
  NSCritical.round434DeepFarLowPhysicalWeldClosed ≡ false
nsOptionalR284DeepFarLowPhysicalWeldOpen =
  NSCritical.round434DeepFarLowPhysicalWeldClosedIsFalse

nsOptionalR284DeepHighHighPhysicalWeldOpen :
  NSCritical.round434DeepHighHighPhysicalWeldClosed ≡ false
nsOptionalR284DeepHighHighPhysicalWeldOpen =
  NSCritical.round434DeepHighHighPhysicalWeldClosedIsFalse

nsOptionalR284CriticalConeCovarianceOpen :
  NSCritical.round434PhysicalCriticalConeCovarianceClosed ≡ false
nsOptionalR284CriticalConeCovarianceOpen =
  NSCritical.round434PhysicalCriticalConeCovarianceClosedIsFalse

nsFullCauchyFormNotSignedCrossIdentity :
  NSCauchyBoundary.round484FullFormSameObjectAsSignedFlux ≡ false
nsFullCauchyFormNotSignedCrossIdentity =
  NSCauchyBoundary.round484FullFormSameObjectAsSignedFluxIsFalse

nsPositiveTerminalFluxNotCanonicalClayLeaf :
  NS.round486PositiveTerminalFluxIsCanonicalClayLeaf ≡ false
nsPositiveTerminalFluxNotCanonicalClayLeaf =
  NS.round486PositiveTerminalFluxIsCanonicalClayLeafIsFalse

------------------------------------------------------------------------
-- Other programmes remain independent.
------------------------------------------------------------------------

ymDirectRouteRemainsAND :
  YM.routeTargets YM.directRound108ActionRoute
  ≡ YM.round108FixedDensitySemantics ∷ YM.round108SelectedPotentialMatchesBC1 ∷ []
ymDirectRouteRemainsAND = YM.directRound108RouteTargetsFixedSemanticsAndMatch

rhOffStillLive :
  Zeta.finalLeafState Zeta.universalPoleQuotientSignedOff ≡ Zeta.live
rhOffStillLive = Zeta.universalPoleQuotientOffIsLive

rhGammaStillLive :
  Zeta.finalLeafState Zeta.sameTaperGammaPrecision ≡ Zeta.live
rhGammaStillLive = Zeta.gammaPrecisionIsLive

rhDownstreamBudgetCompilerNotFreshLeaf :
  RH.FinalRHAllowanceSchedulerBoundary.strictCombinedBudgetIsFreshAnalyticLeaf
    RH.canonicalFinalRHAllowanceSchedulerBoundary ≡ false
rhDownstreamBudgetCompilerNotFreshLeaf = refl

------------------------------------------------------------------------
-- Highest-alpha shared search policy.
------------------------------------------------------------------------

record CrossDomainSearchPolicy : Set where
  constructor cross-domain-search-policy
  field
    attackTerminalLeavesOnly : Bool
    attackTerminalLeavesOnlyIsTrue : attackTerminalLeavesOnly ≡ true
    reopenOwnedCompilerInfrastructure : Bool
    reopenOwnedCompilerInfrastructureIsFalse : reopenOwnedCompilerInfrastructure ≡ false
    sameMotifImpliesSameTheorem : Bool
    sameMotifImpliesSameTheoremIsFalse : sameMotifImpliesSameTheorem ≡ false
    sameObjectReceiptsReusableAsArchitecture : Bool
    sameObjectReceiptsReusableAsArchitectureIsTrue : sameObjectReceiptsReusableAsArchitecture ≡ true
    allowancePaymentPatternReusableAsArchitecture : Bool
    allowancePaymentPatternReusableAsArchitectureIsTrue : allowancePaymentPatternReusableAsArchitecture ≡ true
    oneChildClosesYMParent : Bool
    oneChildClosesYMParentIsFalse : oneChildClosesYMParent ≡ false
    downstreamCompilerWorkAheadOfLiveAnalyticLeaves : Bool
    downstreamCompilerWorkAheadOfLiveAnalyticLeavesIsFalse : downstreamCompilerWorkAheadOfLiveAnalyticLeaves ≡ false

canonicalCrossDomainSearchPolicy : CrossDomainSearchPolicy
canonicalCrossDomainSearchPolicy =
  cross-domain-search-policy
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Current dependency order.
--
-- NS: Think directly on R423.  Optional producer decompositions may be explored
-- only when they improve the route; they do not enlarge the canonical cutset.
------------------------------------------------------------------------

data ClosurePhase : Set where
  representationOrSource : ClosurePhase
  terminalAnalyticPayment : ClosurePhase
  terminalOperatorBound : ClosurePhase
  downstreamCompiler : ClosurePhase

phase : TerminalCoordinate → ClosurePhase
phase nsCutoffUniformIntegratedSignedCompanionBudget = terminalAnalyticPayment
phase ymRound108Semantics = representationOrSource
phase ymRound108BC1SameObject = representationOrSource
phase rhOffAllowance = terminalAnalyticPayment
phase rhGammaAllowance = terminalAnalyticPayment

record CrossDomainBoundary : Set where
  constructor cross-domain-boundary
  field
    sharedSchedulerShapeProvesSharedMathematics : Bool
    sharedSchedulerShapeProvesSharedMathematicsIsFalse : sharedSchedulerShapeProvesSharedMathematics ≡ false
    representationPhaseAutomaticallyClosesAnalyticPayment : Bool
    representationPhaseAutomaticallyClosesAnalyticPaymentIsFalse : representationPhaseAutomaticallyClosesAnalyticPayment ≡ false
    rhOrNSPaymentAutomaticallyClosesYM : Bool
    rhOrNSPaymentAutomaticallyClosesYMIsFalse : rhOrNSPaymentAutomaticallyClosesYM ≡ false
    programmeClaimsClayCompletion : Bool
    programmeClaimsClayCompletionIsFalse : programmeClaimsClayCompletion ≡ false

canonicalCrossDomainBoundary : CrossDomainBoundary
canonicalCrossDomainBoundary =
  cross-domain-boundary false refl false refl false refl false refl
