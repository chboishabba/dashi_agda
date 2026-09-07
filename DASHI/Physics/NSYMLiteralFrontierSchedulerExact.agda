module DASHI.Physics.NSYMLiteralFrontierSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.LiteralFrontierSchedulerExact as Literal
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Physics.Closure.NSTriadKNHighestAlphaFrontierRound285Exact as NS
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as YM146
import DASHI.Physics.YangMills.BalabanFrontierRouteAdmissionRound147Exact as YM147

------------------------------------------------------------------------
-- LITERAL NS/YM FRONTIER SCHEDULER
--
-- This owner does not create new NS or YM mathematics.  It applies the generic
-- close/redirect/reject scheduler to the exact repository frontier already
-- exposed by R285 and R146/R147.
------------------------------------------------------------------------

data NSMove : Set where
  boundedAlmostPeriodicRoute
  directCriticalConeRoute
  constantBandLocalizationRoute
  numericalCriticalConeDiagnostic
  : NSMove

nsLiteralMove : NSMove → Literal.LiteralFrontierMove
nsLiteralMove boundedAlmostPeriodicRoute = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "Package A / persistent-badness obstruction"
  "bounded almost-periodic persistent-bad route"
  "bounded critical-orbit route already contradicted by the existing payment"
  "Navier-Stokes Package A"
  "R281/R241 same-object obstruction"
  "repository theorem/no-go"
  "reject: known no-go"
nsLiteralMove directCriticalConeRoute = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "physical critical-cone signed covariance"
  "direct physical coherent-debt route"
  "signed convolution / phase / helicity structure on the parabolic critical cone"
  "Navier-Stokes Package A"
  "R217-R220/R234-R236/R285 physical critical-cone spine"
  "conditional formal theorem route"
  "redirect: highest-alpha live leaf"
nsLiteralMove constantBandLocalizationRoute = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "physical critical-cone signed covariance"
  "constant-band shell localization"
  "critical-cone theorem cannot be replaced by constant-band localization alone"
  "Navier-Stokes Package A"
  "R214 no-go carrier"
  "repository theorem/no-go"
  "reject: insufficient route"
nsLiteralMove numericalCriticalConeDiagnostic = Literal.literalFrontierMove
  Cross.numericalExperiment
  "physical critical-cone signed covariance"
  "numerical critical-cone diagnostic"
  "phase/helicity/covariance discriminator"
  "route selection only"
  "matched numerical carrier required"
  "diagnostic only; not theorem authority"
  "redirect only if discriminating"

nsOutcome : (move : NSMove) → Literal.LiteralMoveOutcome (nsLiteralMove move)
nsOutcome boundedAlmostPeriodicRoute = Literal.rejected
  (Literal.rejectedLiteralMove Literal.knownNoGo
    "R285 records the bounded almost-periodic persistent-bad route as rejected"
    true refl)
nsOutcome directCriticalConeRoute = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "physical critical-cone signed covariance remains the live leaf"
    "all earlier cell-mass and ED-payable-region receipts remain retained"
    "R285 direct physical coherent-debt route is the current highest-alpha redirect")
nsOutcome constantBandLocalizationRoute = Literal.rejected
  (Literal.rejectedLiteralMove Literal.knownNoGo
    "R214/R285: constant-band localization alone is insufficient for the critical cone"
    true refl)
nsOutcome numericalCriticalConeDiagnostic = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "use any discriminating numerical result only to reprioritize phase/helicity/covariance proof subroutes"
    "diagnostic observations remain evidence-only"
    "numerical evidence may redirect but cannot close Package A")

nsLiteralPortfolio : Literal.LiteralFrontierPortfolio
nsLiteralPortfolio = Literal.literalFrontierPortfolio
  NSMove nsLiteralMove nsOutcome
  "Navier-Stokes Package A"
  "R285 supplies the current explicit highest-alpha/no-go cut; this fixture enumerates only the live/rejected moves used here"
  true refl

nsBoundedRouteRejected :
  NS.round285BoundedAlmostPeriodicPersistentBadRouteRejected ≡ true
nsBoundedRouteRejected = NS.round285BoundedAlmostPeriodicPersistentBadRouteRejectedIsTrue

nsDirectRouteHighestAlpha :
  NS.round285DirectPhysicalCoherentDebtRouteHighestAlpha ≡ true
nsDirectRouteHighestAlpha = NS.round285DirectPhysicalCoherentDebtRouteHighestAlphaIsTrue

nsCriticalLeafOpen :
  NS.round285PhysicalCriticalConeSignedCovarianceClosed ≡ false
nsCriticalLeafOpen = NS.round285PhysicalCriticalConeSignedCovarianceClosedIsFalse

------------------------------------------------------------------------
-- Yang-Mills literal source frontier.
------------------------------------------------------------------------

data YMMove : Set where
  directRound108Route
  combinedRGFallbackRoute
  round108SemanticsChild
  round108BC1MatchChild
  numericalDensityDiagnostic
  : YMMove

ymLiteralMove : YMMove → Literal.LiteralFrontierMove
ymLiteralMove directRound108Route = Literal.literalFrontierMove
  Cross.sourceReconstruction
  "densityActionRealization"
  "direct Round108 action route"
  "both source-fixed density semantics and selected-potential BC1 match are required"
  "Balaban physical frontier"
  "R146 direct AND-route"
  "source theorem + same-object match required"
  "redirect until both children close"
ymLiteralMove combinedRGFallbackRoute = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "densityActionRealization"
  "CombinedRG fallback route"
  "density-to-state and state-to-BC1-potential children"
  "Balaban physical frontier"
  "R146 fallback AND-route"
  "conditional formal route"
  "redirect while either child remains open"
ymLiteralMove round108SemanticsChild = Literal.literalFrontierMove
  Cross.sourceReconstruction
  "round108FixedDensitySemantics"
  "recover source-fixed Round108 density semantics"
  "literal source semantics"
  "direct Round108 route"
  "same source object required"
  "source theorem matched only after exact reconstruction"
  "high-value source child"
ymLiteralMove round108BC1MatchChild = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "round108SelectedPotentialMatchesBC1"
  "prove selected-potential same-object match to BC1"
  "representation/same-object weld"
  "direct Round108 route"
  "selected potential and BC1 must be the same physical object"
  "formal equality/weld required"
  "high-value same-object child"
ymLiteralMove numericalDensityDiagnostic = Literal.literalFrontierMove
  Cross.numericalExperiment
  "densityActionRealization"
  "numerical density/potential diagnostic"
  "route discrimination only"
  "Balaban frontier route selection"
  "matched numerical carrier required"
  "analogyOnly theorem authority"
  "cannot close formal leaf"

ymOutcome : (move : YMMove) → Literal.LiteralMoveOutcome (ymLiteralMove move)
ymOutcome directRound108Route = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "close both Round108 semantics and BC1 same-object children"
    "R146 AND-structure retained"
    "direct route remains a parent route, not a free leaf")
ymOutcome combinedRGFallbackRoute = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "close both CombinedRG semantic children"
    "fallback route remains separately retained"
    "fallback remains admissible but does not inherit child authority")
ymOutcome round108SemanticsChild = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "source-exact Round108 semantics reconstruction"
    "source history retained"
    "source reconstruction is a live producer, not automatic closure")
ymOutcome round108BC1MatchChild = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "selected-potential = BC1 same-object weld"
    "representation provenance retained"
    "same-object equality is independently required")
ymOutcome numericalDensityDiagnostic = Literal.rejected
  (Literal.rejectedLiteralMove Literal.authorityInsufficient
    "R147 assigns numericalExperiment analogyOnly authority, which cannot directly close a theorem leaf"
    true refl)

ymLiteralPortfolio : Literal.LiteralFrontierPortfolio
ymLiteralPortfolio = Literal.literalFrontierPortfolio
  YMMove ymLiteralMove ymOutcome
  "Balaban physical frontier"
  "R146 exposes the explicit direct/fallback AND children; R147 supplies the authority boundary"
  true refl

ymDirectRouteHasTwoChildren :
  YM146.routeTargets YM146.directRound108ActionRoute
  ≡ YM146.round108FixedDensitySemantics ∷ YM146.round108SelectedPotentialMatchesBC1 ∷ []
ymDirectRouteHasTwoChildren = YM146.directRound108RouteTargetsFixedSemanticsAndMatch

ymNumericalCannotCloseLeaf :
  YM147.DirectLeafClosureCapability YM147.numericalExperiment → ⊥
ymNumericalCannotCloseLeaf = YM147.numericalExperimentCannotDirectlyCloseLeaf

record NSYMLiteralFrontierBoundary : Set where
  constructor nsymLiteralFrontierBoundary
  field
    rejectedNSRouteIsReopenedByGenericScheduler : Bool
    rejectedNSRouteIsReopenedByGenericSchedulerIsFalse :
      rejectedNSRouteIsReopenedByGenericScheduler ≡ false
    numericalNSDiagnosticEqualsPackageAClosure : Bool
    numericalNSDiagnosticEqualsPackageAClosureIsFalse :
      numericalNSDiagnosticEqualsPackageAClosure ≡ false
    ymParentRouteInheritsOneChildAuthority : Bool
    ymParentRouteInheritsOneChildAuthorityIsFalse :
      ymParentRouteInheritsOneChildAuthority ≡ false
    numericalYMExperimentClosesFormalLeaf : Bool
    numericalYMExperimentClosesFormalLeafIsFalse :
      numericalYMExperimentClosesFormalLeaf ≡ false

canonicalNSYMLiteralFrontierBoundary : NSYMLiteralFrontierBoundary
canonicalNSYMLiteralFrontierBoundary =
  nsymLiteralFrontierBoundary false refl false refl false refl false refl
