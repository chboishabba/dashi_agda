module DASHI.Core.ClayCrossDomainLiteralFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact as R478
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedSignedResidualRound479Exact as R479
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedPhysicalSnapshotRound480Exact as NS
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
-- NS UPDATE (R480)
-- ----------------
-- R477 installs the literal nonseparable Cauchy kernel and an exact helical
-- split.  R478 correctly notices that the TOTAL all-coefficient Gram bound is
-- weaker than demanding separate +/- bounds.  R479 adds a signed-residual
-- allowance producer so the paid diagonal can be separated from the genuinely
-- signed remainder without inserting absolute values.
--
-- R480 then follows the actual R472 downstream type one step further: R432 does
-- not consume a theorem for every hypothetical coefficient vector.  It consumes
-- the selected physical coefficient snapshot.  The least-privilege terminal
-- packet is therefore:
--
--   exact physical snapshot/same-object weld
--   + bound at that selected physical coefficient.
--
-- The uniform R478 theorem remains a sufficient producer, not a mandatory
-- terminal obligation.
------------------------------------------------------------------------

data TerminalProducerMotif : Set where
  sameObjectRepresentation : TerminalProducerMotif
  assignedAllowancePayment : TerminalProducerMotif
  signedIntegratedPayment : TerminalProducerMotif
  resolvedGramOperatorBound : TerminalProducerMotif
  selectedResolvedPayment : TerminalProducerMotif
  sourceSemanticsRecovery : TerminalProducerMotif
  conjunctionOfIndependentChildren : TerminalProducerMotif
  downstreamCompilerReuse : TerminalProducerMotif


data Programme : Set where navierStokes yangMills riemannZeta : Programme

data TerminalCoordinate : Set where
  nsResolvedSnapshotWeld : TerminalCoordinate
  nsSelectedResolvedPayment : TerminalCoordinate
  ymRound108Semantics : TerminalCoordinate
  ymRound108BC1SameObject : TerminalCoordinate
  rhOffAllowance : TerminalCoordinate
  rhGammaAllowance : TerminalCoordinate

coordinateProgramme : TerminalCoordinate → Programme
coordinateProgramme nsResolvedSnapshotWeld = navierStokes
coordinateProgramme nsSelectedResolvedPayment = navierStokes
coordinateProgramme ymRound108Semantics = yangMills
coordinateProgramme ymRound108BC1SameObject = yangMills
coordinateProgramme rhOffAllowance = riemannZeta
coordinateProgramme rhGammaAllowance = riemannZeta

primaryMotif : TerminalCoordinate → TerminalProducerMotif
primaryMotif nsResolvedSnapshotWeld = sameObjectRepresentation
primaryMotif nsSelectedResolvedPayment = selectedResolvedPayment
primaryMotif ymRound108Semantics = sourceSemanticsRecovery
primaryMotif ymRound108BC1SameObject = sameObjectRepresentation
primaryMotif rhOffAllowance = assignedAllowancePayment
primaryMotif rhGammaAllowance = assignedAllowancePayment

coordinateReference : TerminalCoordinate → String
coordinateReference nsResolvedSnapshotWeld =
  "NS: R480 actual physical Cauchy-resolved coefficient/signed-cross same-object snapshot"
coordinateReference nsSelectedResolvedPayment =
  "NS: R480 selected physical Cauchy-resolved quadratic <= selected fibre budget"
coordinateReference ymRound108Semantics = "YM: source-fixed Round108 density semantics"
coordinateReference ymRound108BC1SameObject = "YM: selected potential = BC1 same-object representation weld"
coordinateReference rhOffAllowance = "RH/zeta: universal pole-quotient Off budget <= assigned A_off"
coordinateReference rhGammaAllowance = "RH/zeta: same-taper Gamma budget <= assigned A_Gamma"

------------------------------------------------------------------------
-- Exact pins to current terminality / producer hierarchy.
------------------------------------------------------------------------

nsPhysicalSnapshotPreferred : NS.round480ActualPhysicalSnapshotIsPreferredConsumer ≡ true
nsPhysicalSnapshotPreferred = refl

nsPhysicalSnapshotWeldStillOpen : NS.round480PhysicalSnapshotSameObjectWeldClosed ≡ false
nsPhysicalSnapshotWeldStillOpen = NS.round480PhysicalSnapshotSameObjectWeldClosedIsFalse

nsSelectedResolvedPaymentStillOpen : NS.round480PhysicalSelectedResolvedBoundClosed ≡ false
nsSelectedResolvedPaymentStillOpen = NS.round480PhysicalSelectedResolvedBoundClosedIsFalse

nsUniformResolvedBoundSufficient : NS.round480UniformAllCoefficientBoundIsSufficient ≡ true
nsUniformResolvedBoundSufficient = refl

nsUniformResolvedBoundNotMandatory : NS.round480UniformAllCoefficientBoundIsMandatory ≡ false
nsUniformResolvedBoundNotMandatory = NS.round480UniformAllCoefficientBoundIsMandatoryIsFalse

nsR478DirectProducerPreferredWithinUniformLane : R478.round478DirectResolvedConsumerPreferred ≡ true
nsR478DirectProducerPreferredWithinUniformLane = refl

nsSplitScalarPairNotMandatory : R478.round478SplitScalarPairIsMandatory ≡ false
nsSplitScalarPairNotMandatory = R478.round478SplitScalarPairIsMandatoryIsFalse

nsSignedResidualProducerCompiles : R479.round479SignedResidualProducerCompilesToDirectConsumer ≡ true
nsSignedResidualProducerCompiles = refl

nsSignedResidualRemainsSigned : R479.round479ResidualRemainsSigned ≡ true
nsSignedResidualRemainsSigned = refl

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
-- 1. Close the R480 physical same-object snapshot weld from already-owned
--    R447/R448/R451/R456/R472 infrastructure if possible.
-- 2. Attack only the selected physical signed-resolved payment left in that
--    snapshot.  The uniform all-coefficient bound is optional.
-- 3. Let R432 and the existing downstream compilers fire.
--
-- YM and RH/zeta remain independent programmes with their own terminal leaves.
------------------------------------------------------------------------

data ClosurePhase : Set where
  representationOrSource : ClosurePhase
  terminalAnalyticPayment : ClosurePhase
  terminalOperatorBound : ClosurePhase
  downstreamCompiler : ClosurePhase

phase : TerminalCoordinate → ClosurePhase
phase nsResolvedSnapshotWeld = representationOrSource
phase nsSelectedResolvedPayment = terminalAnalyticPayment
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
