module DASHI.Physics.ProofSearchExperimentalParetoFrontierNSYMExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Core.SourceExactFrontierBidiCrossPollination2026 as Source
import DASHI.Physics.Closure.NSTriadKNHighestAlphaFrontierRound285Exact as NS
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as YM146
import DASHI.Physics.YangMills.BalabanFrontierRouteAdmissionRound147Exact as YM147

------------------------------------------------------------------------
-- NS / YM PROOF-SEARCH + EXPERIMENTAL PARETO FRONTIER CROSS-POLLINATION
--
-- Numerical and physical experiments can discriminate routes, calibrate
-- candidate models, or expose a missing coordinate.  They do not directly
-- discharge theorem leaves.  Formal route selection remains least-privilege
-- and consumer-relative.
------------------------------------------------------------------------

data PhysicsFrontierDomain : Set where navierStokes yangMills : PhysicsFrontierDomain

data PhysicsRefinementKind : Set where
  theoremReuse : PhysicsRefinementKind
  sourceReconstruction : PhysicsRefinementKind
  symbolicDerivation : PhysicsRefinementKind
  numericalDiagnostic : PhysicsRefinementKind
  physicalMeasurement : PhysicsRefinementKind


record PhysicsFrontierRefinement : Set where
  constructor physicsFrontierRefinement
  field
    domain : PhysicsFrontierDomain
    kind : PhysicsRefinementKind
    liveLeafReference : String
    candidateRouteReference : String
    residualCoordinateReference : String
    consumerReference : String
    experimentMayDiscriminate : Bool
    experimentDirectlyClosesFormalLeaf : Bool

open PhysicsFrontierRefinement public

nsCriticalConeRefinement : PhysicsFrontierRefinement
nsCriticalConeRefinement = physicsFrontierRefinement
  navierStokes
  symbolicDerivation
  "physical critical-cone signed covariance"
  "direct physical coherent-debt route"
  "signed convolution / phase / helicity covariance on the parabolic critical cone"
  "Package A closure"
  true false

ymDensityActionRefinement : PhysicsFrontierRefinement
ymDensityActionRefinement = physicsFrontierRefinement
  yangMills
  sourceReconstruction
  "densityActionRealization"
  "direct Round108 semantics+BC1 match or CombinedRG fallback"
  "source-fixed density semantics / selected potential same-object match"
  "Balaban physical frontier"
  true false

nsBoundedCriticalRouteRemainsRejected :
  NS.round285BoundedAlmostPeriodicPersistentBadRouteRejected ≡ true
nsBoundedCriticalRouteRemainsRejected =
  NS.round285BoundedAlmostPeriodicPersistentBadRouteRejectedIsTrue

nsDirectRouteRemainsHighestAlpha :
  NS.round285DirectPhysicalCoherentDebtRouteHighestAlpha ≡ true
nsDirectRouteRemainsHighestAlpha =
  NS.round285DirectPhysicalCoherentDebtRouteHighestAlphaIsTrue

nsCriticalConeLeafStillOpen :
  NS.round285PhysicalCriticalConeSignedCovarianceClosed ≡ false
nsCriticalConeLeafStillOpen =
  NS.round285PhysicalCriticalConeSignedCovarianceClosedIsFalse

nsNoClayPromotionFromDiagnostics : NS.round285ClayPromotion ≡ false
nsNoClayPromotionFromDiagnostics = refl

ymNumericalExperimentStillCannotDirectlyCloseLeaf :
  YM147.DirectLeafClosureCapability YM147.numericalExperiment → ⊥
ymNumericalExperimentStillCannotDirectlyCloseLeaf =
  YM147.numericalExperimentCannotDirectlyCloseLeaf

ymDirectRouteStillHasTwoRequiredChildren :
  YM146.routeTargets YM146.directRound108ActionRoute
  ≡ YM146.round108FixedDensitySemantics ∷ YM146.round108SelectedPotentialMatchesBC1 ∷ []
ymDirectRouteStillHasTwoRequiredChildren =
  YM146.directRound108RouteTargetsFixedSemanticsAndMatch

record PhysicsParetoFrontierBoundary : Set where
  constructor physicsParetoFrontierBoundary
  field
    numericalDiagnosticMaySelectBetweenLiveRoutes : Bool
    numericalDiagnosticMaySelectBetweenLiveRoutesIsTrue :
      numericalDiagnosticMaySelectBetweenLiveRoutes ≡ true
    numericalDiagnosticAutomaticallyClosesNSLeaf : Bool
    numericalDiagnosticAutomaticallyClosesNSLeafIsFalse :
      numericalDiagnosticAutomaticallyClosesNSLeaf ≡ false
    numericalExperimentAutomaticallyClosesYMLeaf : Bool
    numericalExperimentAutomaticallyClosesYMLeafIsFalse :
      numericalExperimentAutomaticallyClosesYMLeaf ≡ false
    paretoPreferredRouteMaySkipSameObjectAdmission : Bool
    paretoPreferredRouteMaySkipSameObjectAdmissionIsFalse :
      paretoPreferredRouteMaySkipSameObjectAdmission ≡ false
    rejectedRouteShouldRemainInEvidenceHistory : Bool
    rejectedRouteShouldRemainInEvidenceHistoryIsTrue :
      rejectedRouteShouldRemainInEvidenceHistory ≡ true

canonicalPhysicsParetoFrontierBoundary : PhysicsParetoFrontierBoundary
canonicalPhysicsParetoFrontierBoundary =
  physicsParetoFrontierBoundary true refl false refl false refl false refl true refl

existingCrossDomainBoundary : Cross.ProofSearchExperimentalParetoBoundary
existingCrossDomainBoundary = Cross.canonicalProofSearchExperimentalParetoBoundary

authoritativeSourceFrontierPattern : Set
authoritativeSourceFrontierPattern = Source.VerificationCarrier
