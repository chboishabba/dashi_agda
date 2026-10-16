module DASHI.Physics.Plasma.Phase243FreeBoundarySixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54

------------------------------------------------------------------------
-- FREE-BOUNDARY SIX: EXACT IDENTITY OF THE COIL-ROUTED SHORTLIST
--
-- These six rows are frozen from the deterministic executable receipt in
-- scripts/phase243_core54_pareto_coil.py.  They are search-artifact identities,
-- not experimental or literature authority.
--
-- Structurally the six rows are three geometry/phase representatives at two
-- ABC allocations:
--
--   Aoff : Core54 (0,0,1,offset)
--   Aali : Core54 (0,0,1,aligned)
--   Xoff : Core54 (2,0,0,offset)
--
-- each at either
--   route-C-only : deltaC=1, M=0, alpha=0
-- or
--   mixed        : deltaC=.75, M=.25, alpha=.1875.
--
-- Values below are integer-scaled script observations.  Their authority is
-- local executable/search evidence only.
------------------------------------------------------------------------

data Candidate6 : Set where
  AoffRouteC : Candidate6
  AaliRouteC : Candidate6
  AoffMixed : Candidate6
  AaliMixed : Candidate6
  XoffRouteC : Candidate6
  XoffMixed : Candidate6

candidateCount : Nat
candidateCount = 6

AoffTag AaliTag XoffTag : Q54.Core54
AoffTag = Q54.core54 C3.phase0 C3.phase0 C3.phase1 Q54.offsetPhase
AaliTag = Q54.core54 C3.phase0 C3.phase0 C3.phase1 Q54.alignedPhase
XoffTag = Q54.core54 C3.phase2 C3.phase0 C3.phase0 Q54.offsetPhase

candidateTag : Candidate6 → Q54.Core54
candidateTag AoffRouteC = AoffTag
candidateTag AaliRouteC = AaliTag
candidateTag AoffMixed = AoffTag
candidateTag AaliMixed = AaliTag
candidateTag XoffRouteC = XoffTag
candidateTag XoffMixed = XoffTag

record ABCScaled : Set where
  constructor abc-scaled
  field
    -- scale = 10^4
    deltaC10000 : Nat
    mach10000 : Nat
    alpha10000 : Nat

open ABCScaled public

routeCOnlyABC : ABCScaled
routeCOnlyABC = abc-scaled 10000 0 0

mixedABC : ABCScaled
mixedABC = abc-scaled 7500 2500 1875

candidateABC : Candidate6 → ABCScaled
candidateABC AoffRouteC = routeCOnlyABC
candidateABC AaliRouteC = routeCOnlyABC
candidateABC AoffMixed = mixedABC
candidateABC AaliMixed = mixedABC
candidateABC XoffRouteC = routeCOnlyABC
candidateABC XoffMixed = mixedABC

record ShortlistProxyObservation : Set where
  constructor shortlist-proxy-observation
  field
    -- scale = 10^8 unless stated otherwise.
    relativeBSpread1e8 : Nat
    geodesicCurvatureRMS1e8 : Nat
    normalFieldResidual1e8 : Nat
    coilCoefficientNorm1e8 : Nat
    -- min rho uses scale = 10^8.
    minimumRho1e8 : Nat

open ShortlistProxyObservation public

AoffProxy AaliProxy XoffProxy : ShortlistProxyObservation
AoffProxy = shortlist-proxy-observation 3364394 24477337 8501103 635987 92301999
AaliProxy = shortlist-proxy-observation 3364393 24477338 8501103 635987 92482459
XoffProxy = shortlist-proxy-observation 689984 24821284 52859370 1657864 100000000

candidateProxy : Candidate6 → ShortlistProxyObservation
candidateProxy AoffRouteC = AoffProxy
candidateProxy AaliRouteC = AaliProxy
candidateProxy AoffMixed = AoffProxy
candidateProxy AaliMixed = AaliProxy
candidateProxy XoffRouteC = XoffProxy
candidateProxy XoffMixed = XoffProxy

------------------------------------------------------------------------
-- P5 result ABI.
------------------------------------------------------------------------

data FreeBoundaryFailureReason : Set where
  solverNonConvergence : FreeBoundaryFailureReason
  coilGeometryInvalid : FreeBoundaryFailureReason
  noNestedFluxSurface : FreeBoundaryFailureReason
  divergenceFailure : FreeBoundaryFailureReason
  finiteBetaFailure : FreeBoundaryFailureReason
  abcMomentumBalanceFailure : FreeBoundaryFailureReason
  kineticOrFlowStabilityFailure : FreeBoundaryFailureReason
  sameObjectMismatch : FreeBoundaryFailureReason

record SolvedFreeBoundaryCase (candidate : Candidate6) : Set₁ where
  constructor solved-free-boundary-case
  field
    PhysicalState CoilField PlasmaField TotalField : Set
    state : PhysicalState
    coilField : CoilField
    plasmaField : PlasmaField
    totalField : TotalField

    selectedCandidateIdentityReceipt : Set
    selectedCoilCurrentsReceipt : Set
    totalFieldIsCoilPlusPlasmaReceipt : Set
    sameBoundaryGeometryReceipt : Set
    sameNormalizationReceipt : Set
    finiteBetaReceipt : Set
    nestedFluxSurfaceReceipt : Set
    divergenceFreeTotalFieldReceipt : Set
    freeBoundaryEquilibriumReceipt : Set
    declaredABCAllocationReceipt : Set
    abcMomentumBalanceReceipt : Set
    flowAnisotropyKineticClosureReceipt : Set
    solverResidualReceipt : Set
    solverProvenance : String

open SolvedFreeBoundaryCase public

record RejectedFreeBoundaryCase (candidate : Candidate6) : Set where
  constructor rejected-free-boundary-case
  field
    reason : FreeBoundaryFailureReason
    sameCandidateIdentityReceipt : Set
    failureObservableReceipt : Set
    failureProvenance : String

open RejectedFreeBoundaryCase public

data FreeBoundaryOutcome (candidate : Candidate6) : Set₁ where
  solved : SolvedFreeBoundaryCase candidate → FreeBoundaryOutcome candidate
  rejected : RejectedFreeBoundaryCase candidate → FreeBoundaryOutcome candidate

record FreeBoundarySixRun : Set₁ where
  constructor free-boundary-six-run
  field
    AoffRouteCOutcome : FreeBoundaryOutcome AoffRouteC
    AaliRouteCOutcome : FreeBoundaryOutcome AaliRouteC
    AoffMixedOutcome : FreeBoundaryOutcome AoffMixed
    AaliMixedOutcome : FreeBoundaryOutcome AaliMixed
    XoffRouteCOutcome : FreeBoundaryOutcome XoffRouteC
    XoffMixedOutcome : FreeBoundaryOutcome XoffMixed
    sameSolverFamilyReceipt : Set
    sameResolutionPolicyReceipt : Set
    sameConvergencePolicyReceipt : Set
    runProvenance : String

open FreeBoundarySixRun public

record FreeBoundarySixBoundary : Set where
  constructor free-boundary-six-boundary
  field
    sixCandidateIdentitiesFrozen : Bool
    sixCandidateIdentitiesFrozenIsTrue : sixCandidateIdentitiesFrozen ≡ true
    proxyMetricsAreFreeBoundarySolutions : Bool
    proxyMetricsAreFreeBoundarySolutionsIsFalse : proxyMetricsAreFreeBoundarySolutions ≡ false
    eachCandidateMustSolveOrReject : Bool
    eachCandidateMustSolveOrRejectIsTrue : eachCandidateMustSolveOrReject ≡ true
    rejectedCandidateMayBeRankedAsSolved : Bool
    rejectedCandidateMayBeRankedAsSolvedIsFalse : rejectedCandidateMayBeRankedAsSolved ≡ false
    acquiredSourceAuthorityTransfersIntoSolverReceipt : Bool
    acquiredSourceAuthorityTransfersIntoSolverReceiptIsFalse :
      acquiredSourceAuthorityTransfersIntoSolverReceipt ≡ false

canonicalFreeBoundarySixBoundary : FreeBoundarySixBoundary
canonicalFreeBoundarySixBoundary =
  free-boundary-six-boundary
    true refl
    false refl
    true refl
    false refl
    false refl

shortlistArtifactReference : String
shortlistArtifactReference =
  "scripts/phase243_core54_pareto_coil.py on PR #1096: 54 representatives -> 810 ABC-grid records -> 168 declared-axis Pareto records -> six coil-routed rows. These frozen rows retain numerical-artifact authority only."
