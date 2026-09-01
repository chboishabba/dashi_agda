module DASHI.Physics.Closure.NSTriadKNHighestAlphaProofSearchRound296Exact where

------------------------------------------------------------------------
-- ROUND296 / HIGHEST-ALPHA PROOF SEARCH AS AN ADMITTED AND/OR HYPERGRAPH
--
-- This module cross-pollinates the merged Aristotle MCGS search semantics and
-- the merged proof-search least-privilege admission gate into the literal NS
-- R285+ frontier.
--
-- Important search discipline:
--
--   * rejected routes remain first-class learned feedback;
--   * local lemma count is not programme progress;
--   * the R290 resolvent route is admitted only because it targets the same
--     R227/R220/R293 physical carrier and does not assume Package A;
--   * Package A is an AND-node below endpoint control AND weighted nonlinear
--     remainder control, not a Boolean that may be promoted by one local lemma.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNWaleffeSmallOrbitDecisionRound288Exact as R288
import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuarticFluxHomogeneityRound289Exact as R289
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295

------------------------------------------------------------------------
-- Literal search states.
------------------------------------------------------------------------

data NSProofState : Set where
  criticalConeGramUnpaid
  pointwiseAbsorptionUnpaid
  signedIntegratedGramUnpaid
  resolventEndpointUnpaid
  weightedCommutatorUnpaid
  literalRound240PackageA
  : NSProofState

data NSProofAction : Set where
  tryPointwiseSymmetry
  tryNaiveNonlinearFlux
  useResolventFlux
  closeSignedGramFromResolvent
  closePackageAFromSignedGram
  : NSProofAction

source : NSProofAction → NSProofState
source tryPointwiseSymmetry = criticalConeGramUnpaid
source tryNaiveNonlinearFlux = criticalConeGramUnpaid
source useResolventFlux = criticalConeGramUnpaid
source closeSignedGramFromResolvent = signedIntegratedGramUnpaid
source closePackageAFromSignedGram = literalRound240PackageA

targets : NSProofAction → List NSProofState
targets tryPointwiseSymmetry = pointwiseAbsorptionUnpaid ∷ []
targets tryNaiveNonlinearFlux = signedIntegratedGramUnpaid ∷ []
targets useResolventFlux = resolventEndpointUnpaid ∷ weightedCommutatorUnpaid ∷ []
targets closeSignedGramFromResolvent = resolventEndpointUnpaid ∷ weightedCommutatorUnpaid ∷ []
targets closePackageAFromSignedGram = signedIntegratedGramUnpaid ∷ []

nsHighestAlphaGraph : Aristotle.SearchHypergraph
nsHighestAlphaGraph = record
  { State = NSProofState
  ; Action = NSProofAction
  ; source = source
  ; targets = targets
  }

------------------------------------------------------------------------
-- Learned route dispositions.  These are search feedback, not theorem claims
-- stronger than the underlying R288/R289 no-promotion boundaries.
------------------------------------------------------------------------

pointwiseSymmetryDisposition : Least.RouteDisposition
pointwiseSymmetryDisposition = Least.rejected Least.noGoCollision

naiveNonlinearFluxDisposition : Least.RouteDisposition
naiveNonlinearFluxDisposition = Least.rejected Least.strengthMismatch

legacyR222MajorantDisposition : Least.RouteDisposition
legacyR222MajorantDisposition = Least.redirectedReuse

resolventRouteDisposition : Least.RouteDisposition
resolventRouteDisposition = Least.admitted

------------------------------------------------------------------------
-- Least-privilege admission for the surviving route.
--
-- The generic receipt constructors are intentionally used only to certify the
-- search route, not the mathematical leaves.  Endpoint positivity/control and
-- the weighted commutator spacetime estimate remain explicit frontier leaves.
------------------------------------------------------------------------

resolventRouteAdmission : Least.RouteAdmission
resolventRouteAdmission =
  Least.route-admission
    Least.exactTarget
    Least.sameObjectSpine
    Least.prerequisiteClosure
    Least.noKnownNoGo
    Least.noCircularDependency
    Least.noSilentStrengthening
    Least.authorityAdequacy
    Least.noveltyAgainstRepo
    Least.frontierImproves

resolventLiveSearch : Least.LiveProofSearch
resolventLiveSearch = Least.elaborateRoute resolventRouteAdmission

------------------------------------------------------------------------
-- AND-node package: both children are required before the signed integrated
-- Gram state may close.  No constructor is exposed from either child alone.
------------------------------------------------------------------------

data ResolventEndpointClosed : Set where
  endpointClosed : ResolventEndpointClosed

data WeightedCommutatorClosed : Set where
  weightedCommutatorClosed : WeightedCommutatorClosed

data SignedIntegratedGramClosed : Set where
  signedGramClosed : ResolventEndpointClosed → WeightedCommutatorClosed → SignedIntegratedGramClosed

data Round240PackageAClosed : Set where
  packageAClosed : SignedIntegratedGramClosed → Round240PackageAClosed

resolventChildrenCloseSignedGram :
  ResolventEndpointClosed → WeightedCommutatorClosed → SignedIntegratedGramClosed
resolventChildrenCloseSignedGram = signedGramClosed

signedGramClosesPackageA : SignedIntegratedGramClosed → Round240PackageAClosed
signedGramClosesPackageA = packageAClosed

------------------------------------------------------------------------
-- Search ledger.
------------------------------------------------------------------------

round296UsesAristotleAndOrSearch : Bool
round296UsesAristotleAndOrSearch = true

round296UsesLeastPrivilegeAdmission : Bool
round296UsesLeastPrivilegeAdmission = true

round296RejectedSymmetryRouteRetainedAsFeedback : Bool
round296RejectedSymmetryRouteRetainedAsFeedback = true

round296RejectedHomogeneityMismatchRetainedAsFeedback : Bool
round296RejectedHomogeneityMismatchRetainedAsFeedback = true

round296ResolventRouteAdmitted : Bool
round296ResolventRouteAdmitted = true

round296EndpointLeafClosed : Bool
round296EndpointLeafClosed = false

round296WeightedCommutatorLeafClosed : Bool
round296WeightedCommutatorLeafClosed = false

round296SignedIntegratedGramClosed : Bool
round296SignedIntegratedGramClosed = false

round296PackageAClosed : Bool
round296PackageAClosed = false

round296ClayPromotion : Bool
round296ClayPromotion = false

round296ResolventRouteAdmittedIsTrue : round296ResolventRouteAdmitted ≡ true
round296ResolventRouteAdmittedIsTrue = refl

round296PackageAClosedIsFalse : round296PackageAClosed ≡ false
round296PackageAClosedIsFalse = refl
