module DASHI.Core.ClayCrossDomainLiteralFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNDirectSignedCompanionFrontierRound442Exact as NS
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
------------------------------------------------------------------------

data TerminalProducerMotif : Set where
  sameObjectRepresentation
  assignedAllowancePayment
  signedIntegratedPayment
  sourceSemanticsRecovery
  conjunctionOfIndependentChildren
  downstreamCompilerReuse
  : TerminalProducerMotif

data Programme : Set where navierStokes yangMills riemannZeta : Programme

data TerminalCoordinate : Set where
  nsResolventHeat
  nsSignedSpacetime
  ymRound108Semantics
  ymRound108BC1SameObject
  rhOffAllowance
  rhGammaAllowance
  : TerminalCoordinate

coordinateProgramme : TerminalCoordinate → Programme
coordinateProgramme nsResolventHeat = navierStokes
coordinateProgramme nsSignedSpacetime = navierStokes
coordinateProgramme ymRound108Semantics = yangMills
coordinateProgramme ymRound108BC1SameObject = yangMills
coordinateProgramme rhOffAllowance = riemannZeta
coordinateProgramme rhGammaAllowance = riemannZeta

primaryMotif : TerminalCoordinate → TerminalProducerMotif
primaryMotif nsResolventHeat = sameObjectRepresentation
primaryMotif nsSignedSpacetime = signedIntegratedPayment
primaryMotif ymRound108Semantics = sourceSemanticsRecovery
primaryMotif ymRound108BC1SameObject = sameObjectRepresentation
primaryMotif rhOffAllowance = assignedAllowancePayment
primaryMotif rhGammaAllowance = assignedAllowancePayment

coordinateReference : TerminalCoordinate → String
coordinateReference nsResolventHeat = "NS: exact R290 Cauchy-resolvent -> one-cell heat-factor realization"
coordinateReference nsSignedSpacetime = "NS: cutoff-uniform integrated payment of explicit R440/R441 common signed cross"
coordinateReference ymRound108Semantics = "YM: source-fixed Round108 density semantics"
coordinateReference ymRound108BC1SameObject = "YM: selected potential = BC1 same-object representation weld"
coordinateReference rhOffAllowance = "RH/zeta: universal pole-quotient Off budget <= assigned A_off"
coordinateReference rhGammaAllowance = "RH/zeta: same-taper Gamma budget <= assigned A_Gamma"

------------------------------------------------------------------------
-- Exact pins to current terminality.
------------------------------------------------------------------------

nsResolventStillOpen : NS.round442AnalyticResolventHeatRealizationClosed ≡ false
nsResolventStillOpen = NS.round442AnalyticResolventHeatRealizationClosedIsFalse

nsSignedSpacetimeStillOpen : NS.round442SignedCompanionSpacetimePaymentClosed ≡ false
nsSignedSpacetimeStillOpen = NS.round442SignedCompanionSpacetimePaymentClosedIsFalse

nsFiniteCompilerAlreadyOwned : NS.round442PhysicalR299RecordInhabited ≡ true
nsFiniteCompilerAlreadyOwned = NS.round442PhysicalR299RecordInhabitedIsTrue

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
-- 2. Attack terminal analytic allowance/signed-payment leaves.
-- 3. Let existing downstream compilers fire; do not rebuild them.
--
-- This makes YM's source/same-object children and NS's resolvent same-object
-- realization natural early targets, while RH/zeta's two allowance payments and
-- NS signed spacetime payment remain the irreducible analytic leaves.  It does
-- NOT assert that any of these theorems has been proved.
------------------------------------------------------------------------

data ClosurePhase : Set where
  representationOrSource
  terminalAnalyticPayment
  downstreamCompiler
  : ClosurePhase

phase : TerminalCoordinate → ClosurePhase
phase nsResolventHeat = representationOrSource
phase nsSignedSpacetime = terminalAnalyticPayment
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
