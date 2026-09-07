module DASHI.Core.ClayCrossDomainLiteralFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact as NS
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as YM
import DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact as RH
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Zeta

------------------------------------------------------------------------
-- CROSS-DOMAIN TERMINAL FRONTIER MOTIFS
--
-- This is reuse of proof-search shape, not transfer of theorem content.
-- NS, YM and RH/zeta remain mathematically independent programmes.  The shared
-- value is that their current literal frontiers are now small enough to classify
-- by producer motif, which prevents wasting search on already-owned compiler
-- infrastructure.
--
-- NS UPDATE (R478)
-- ----------------
-- R477 installs the literal nonseparable Cauchy kernel and proves an exact
-- helical +/- split.  It also proves that two same-helicity scalar resolved
-- GramOperatorBounds are a sufficient producer for the total physical bound.
-- R471's least-privilege consumer contract, however, asks only for the TOTAL
-- resolved GramOperatorBound.  R478 therefore makes that one direct bound the
-- preferred terminal coordinate.  The +/- pair remains an optional stronger
-- producer route; the scheduler must not require it and thereby throw away
-- compensation that may be visible only in the summed signed quadratic form.
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
  nsDirectResolvedGram : TerminalCoordinate
  ymRound108Semantics : TerminalCoordinate
  ymRound108BC1SameObject : TerminalCoordinate
  rhOffAllowance : TerminalCoordinate
  rhGammaAllowance : TerminalCoordinate


coordinateProgramme : TerminalCoordinate → Programme
coordinateProgramme nsDirectResolvedGram = navierStokes
coordinateProgramme ymRound108Semantics = yangMills
coordinateProgramme ymRound108BC1SameObject = yangMills
coordinateProgramme rhOffAllowance = riemannZeta
coordinateProgramme rhGammaAllowance = riemannZeta

primaryMotif : TerminalCoordinate → TerminalProducerMotif
primaryMotif nsDirectResolvedGram = resolvedGramOperatorBound
primaryMotif ymRound108Semantics = sourceSemanticsRecovery
primaryMotif ymRound108BC1SameObject = sameObjectRepresentation
primaryMotif rhOffAllowance = assignedAllowancePayment
primaryMotif rhGammaAllowance = assignedAllowancePayment

coordinateReference : TerminalCoordinate → String
coordinateReference nsDirectResolvedGram =
  "NS: R478 direct total Cauchy-resolved fixed-output GramOperatorBound"
coordinateReference ymRound108Semantics = "YM: source-fixed Round108 density semantics"
coordinateReference ymRound108BC1SameObject = "YM: selected potential = BC1 same-object representation weld"
coordinateReference rhOffAllowance = "RH/zeta: universal pole-quotient Off budget <= assigned A_off"
coordinateReference rhGammaAllowance = "RH/zeta: same-taper Gamma budget <= assigned A_Gamma"

------------------------------------------------------------------------
-- Exact pins to current terminality / producer hierarchy.
------------------------------------------------------------------------

nsDirectResolvedGramStillOpen : NS.round478PhysicalDirectResolvedBoundClosed ≡ false
nsDirectResolvedGramStillOpen = NS.round478PhysicalDirectResolvedBoundClosedIsFalse

nsDirectResolvedConsumerPreferred : NS.round478DirectResolvedConsumerPreferred ≡ true
nsDirectResolvedConsumerPreferred = refl

nsSplitScalarPairSufficient : NS.round478SplitScalarPairIsSufficientProducer ≡ true
nsSplitScalarPairSufficient = refl

nsSplitScalarPairNotMandatory : NS.round478SplitScalarPairIsMandatory ≡ false
nsSplitScalarPairNotMandatory = NS.round478SplitScalarPairIsMandatoryIsFalse

nsResolvedHelicalCompilerAlreadyOwned : R477.round477TwoScalarResolvedBoundsCompile ≡ true
nsResolvedHelicalCompilerAlreadyOwned = refl

nsCauchyKernelAlreadyExplicit : R477.round477CauchyPairKernelExplicit ≡ true
nsCauchyKernelAlreadyExplicit = refl

nsResolventNormalizationAlreadyDivisionFree :
  R477.round477ResolventNormalizationDivisionFree ≡ true
nsResolventNormalizationAlreadyDivisionFree = refl

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
--
-- Search one literal coordinate at a time unless the exact consumer explicitly
-- permits a single producer theorem to pay more than one coordinate.  Reuse
-- infrastructure by MOTIF, never by silently identifying mathematical carriers.
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
-- Search order as a dependency statement, not a numerical ranking.
--
-- 1. Remove representation/source seams that block an already-built compiler.
-- 2. Attack terminal analytic/operator-bound leaves.
-- 3. Let existing downstream compilers fire; do not rebuild them.
--
-- YM's source/same-object children remain natural early representation targets.
-- NS has no preferred resolvent->heat seam and no mandatory +/- pair at the
-- terminal boundary: R478 leaves one direct total Cauchy-resolved Gram bound.
-- RH/zeta's two allowance payments remain irreducible analytic leaves.  This
-- does NOT assert that any of these theorems has been proved.
------------------------------------------------------------------------

data ClosurePhase : Set where
  representationOrSource : ClosurePhase
  terminalAnalyticPayment : ClosurePhase
  terminalOperatorBound : ClosurePhase
  downstreamCompiler : ClosurePhase


phase : TerminalCoordinate → ClosurePhase
phase nsDirectResolvedGram = terminalOperatorBound
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