module DASHI.Core.ClayCrossDomainLiteralFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as NS
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
-- NS UPDATE (R477)
-- ----------------
-- The older R442 direct signed-companion frontier exposed resolvent->heat and
-- signed-spacetime leaves.  R477 installs the nonseparable Cauchy kernel
-- directly on the fixed-output Gram quadratic form and proves the exact helical
-- +/- split.  On the currently preferred projected route the terminal NS leaves
-- are therefore the two scalar resolved GramOperatorBounds, not a separate
-- Laplace-realization seam.  The older direct signed route remains a fallback,
-- not the cross-domain scheduler's preferred NS frontier.
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
  nsPlusResolvedGram : TerminalCoordinate
  nsMinusResolvedGram : TerminalCoordinate
  ymRound108Semantics : TerminalCoordinate
  ymRound108BC1SameObject : TerminalCoordinate
  rhOffAllowance : TerminalCoordinate
  rhGammaAllowance : TerminalCoordinate


coordinateProgramme : TerminalCoordinate → Programme
coordinateProgramme nsPlusResolvedGram = navierStokes
coordinateProgramme nsMinusResolvedGram = navierStokes
coordinateProgramme ymRound108Semantics = yangMills
coordinateProgramme ymRound108BC1SameObject = yangMills
coordinateProgramme rhOffAllowance = riemannZeta
coordinateProgramme rhGammaAllowance = riemannZeta

primaryMotif : TerminalCoordinate → TerminalProducerMotif
primaryMotif nsPlusResolvedGram = resolvedGramOperatorBound
primaryMotif nsMinusResolvedGram = resolvedGramOperatorBound
primaryMotif ymRound108Semantics = sourceSemanticsRecovery
primaryMotif ymRound108BC1SameObject = sameObjectRepresentation
primaryMotif rhOffAllowance = assignedAllowancePayment
primaryMotif rhGammaAllowance = assignedAllowancePayment

coordinateReference : TerminalCoordinate → String
coordinateReference nsPlusResolvedGram =
  "NS: R477 physical plus-polarization Cauchy-resolved fixed-output GramOperatorBound"
coordinateReference nsMinusResolvedGram =
  "NS: R477 physical minus-polarization Cauchy-resolved fixed-output GramOperatorBound"
coordinateReference ymRound108Semantics = "YM: source-fixed Round108 density semantics"
coordinateReference ymRound108BC1SameObject = "YM: selected potential = BC1 same-object representation weld"
coordinateReference rhOffAllowance = "RH/zeta: universal pole-quotient Off budget <= assigned A_off"
coordinateReference rhGammaAllowance = "RH/zeta: same-taper Gamma budget <= assigned A_Gamma"

------------------------------------------------------------------------
-- Exact pins to current terminality.
------------------------------------------------------------------------

nsPlusResolvedGramStillOpen : NS.round477PhysicalPlusResolvedBoundClosed ≡ false
nsPlusResolvedGramStillOpen = NS.round477PhysicalPlusResolvedBoundClosedIsFalse

nsMinusResolvedGramStillOpen : NS.round477PhysicalMinusResolvedBoundClosed ≡ false
nsMinusResolvedGramStillOpen = NS.round477PhysicalMinusResolvedBoundClosedIsFalse

nsResolvedHelicalCompilerAlreadyOwned : NS.round477TwoScalarResolvedBoundsCompile ≡ true
nsResolvedHelicalCompilerAlreadyOwned = refl

nsCauchyKernelAlreadyExplicit : NS.round477CauchyPairKernelExplicit ≡ true
nsCauchyKernelAlreadyExplicit = refl

nsResolventNormalizationAlreadyDivisionFree :
  NS.round477ResolventNormalizationDivisionFree ≡ true
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
-- NS no longer schedules the old resolvent->heat representation seam on the
-- preferred projected route: R477 carries the Cauchy kernel directly and leaves
-- exactly two scalar resolved Gram bounds.  RH/zeta's two allowance payments
-- remain irreducible analytic leaves.  This does NOT assert that any of these
-- theorems has been proved.
------------------------------------------------------------------------

data ClosurePhase : Set where
  representationOrSource : ClosurePhase
  terminalAnalyticPayment : ClosurePhase
  terminalOperatorBound : ClosurePhase
  downstreamCompiler : ClosurePhase


phase : TerminalCoordinate → ClosurePhase
phase nsPlusResolvedGram = terminalOperatorBound
phase nsMinusResolvedGram = terminalOperatorBound
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
