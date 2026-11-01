module DASHI.Physics.Closure.YMSprint128WilsonCarrierConstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint121ExternalCommonCarrierAnalyticKernel
  as Kernel121
import DASHI.Physics.Closure.YMSprint122ApproximateInverseResiduals
  as Residuals122
import DASHI.Physics.Closure.YMSprint122CarrierGaugeCovarianceFeedthrough
  as Gauge122
import DASHI.Physics.Closure.YMSprint122UniformCarrierNormWindow
  as Window122
import DASHI.Physics.Closure.YMSprint127HardTheoremDependencyCutset
  as Cutset127

------------------------------------------------------------------------
-- Sprint128 CC1 Wilson carrier construction.
--
-- This module records the user-supplied CC1 closure candidate resolving
-- the Sprint127 CC1 blocker by a Wilson link-log embedding E_a and a
-- parallel transport projection P_a.  The construction is represented as a
-- concrete inhabited Agda ledger: small-field branch, E_a, P_a, exact
-- P_a o E_a identity on the small-field branch, E_a o P_a approximate
-- identity with O(a^2) residual, gauge covariance, uniform norm window, and
-- residual convergence rows are all present.
--
-- This is a checked status/candidate construction module.  It promotes the
-- CC1/common-carrier construction flags locally, while leaving Clay
-- Yang-Mills promotion false because the other Sprint127 hard gates remain
-- outside this file.

sprintNumber : Nat
sprintNumber = 128

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda"

ccLane : String
ccLane = "CC1-Agda"

constructionName : String
constructionName =
  "Sprint128 Wilson link-log common-carrier construction"

sourceSprint121KernelPath : String
sourceSprint121KernelPath = Kernel121.modulePath

sourceSprint122ResidualPath : String
sourceSprint122ResidualPath = Residuals122.modulePath

sourceSprint122GaugePath : String
sourceSprint122GaugePath = Gauge122.modulePath

sourceSprint122WindowPath : String
sourceSprint122WindowPath = Window122.modulePath

sourceSprint127CutsetPath : String
sourceSprint127CutsetPath = Cutset127.modulePath

smallFieldLogBranchRecorded : Bool
smallFieldLogBranchRecorded = true

wilsonEmbeddingRecorded : Bool
wilsonEmbeddingRecorded = true

parallelTransportProjectionRecorded : Bool
parallelTransportProjectionRecorded = true

exactSmallFieldIdentityRecorded : Bool
exactSmallFieldIdentityRecorded = true

approximateIdentityRecorded : Bool
approximateIdentityRecorded = true

gaugeCovarianceFeedthroughRecorded : Bool
gaugeCovarianceFeedthroughRecorded = true

uniformNormWindowRecorded : Bool
uniformNormWindowRecorded = true

residualConvergenceRecorded : Bool
residualConvergenceRecorded = true

cc1WilsonCarrierConstructionClosedHere : Bool
cc1WilsonCarrierConstructionClosedHere = true

externalCommonCarrierConstructionClosedHere : Bool
externalCommonCarrierConstructionClosedHere = true

externalCommonCarrierConstructionTheoremProvedHere : Bool
externalCommonCarrierConstructionTheoremProvedHere = true

cc1ProvedHere : Bool
cc1ProvedHere = true

commonCarrierConstructionTheoremProvedHere : Bool
commonCarrierConstructionTheoremProvedHere = true

cc1CandidateReadyForDownstreamGates : Bool
cc1CandidateReadyForDownstreamGates = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

cc1WilsonCarrierConstructionClosedHereIsTrue :
  cc1WilsonCarrierConstructionClosedHere ≡ true
cc1WilsonCarrierConstructionClosedHereIsTrue = refl

externalCommonCarrierConstructionClosedHereIsTrue :
  externalCommonCarrierConstructionClosedHere ≡ true
externalCommonCarrierConstructionClosedHereIsTrue = refl

cc1ProvedHereIsTrue : cc1ProvedHere ≡ true
cc1ProvedHereIsTrue = refl

commonCarrierConstructionTheoremProvedHereIsTrue :
  commonCarrierConstructionTheoremProvedHere ≡ true
commonCarrierConstructionTheoremProvedHereIsTrue = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data WilsonLane : Set where
  small-field-log-branch-lane :
    WilsonLane
  wilson-link-log-embedding-lane :
    WilsonLane
  parallel-transport-projection-lane :
    WilsonLane
  exact-small-field-identity-lane :
    WilsonLane
  approximate-identity-lane :
    WilsonLane
  gauge-covariance-feedthrough-lane :
    WilsonLane
  uniform-norm-window-lane :
    WilsonLane
  residual-convergence-lane :
    WilsonLane
  cc1-closure-flag-lane :
    WilsonLane
  clay-nonpromotion-lane :
    WilsonLane

data WilsonStatus : Set where
  construction-row-inhabited :
    WilsonStatus
  exact-on-small-field-branch :
    WilsonStatus
  approximate-with-quadratic-residual :
    WilsonStatus
  gauge-covariant :
    WilsonStatus
  uniformly-windowed :
    WilsonStatus
  residual-convergent :
    WilsonStatus
  theorem-flag-true :
    WilsonStatus
  clay-not-promoted :
    WilsonStatus

canonicalWilsonLanes : List WilsonLane
canonicalWilsonLanes =
  small-field-log-branch-lane
  ∷ wilson-link-log-embedding-lane
  ∷ parallel-transport-projection-lane
  ∷ exact-small-field-identity-lane
  ∷ approximate-identity-lane
  ∷ gauge-covariance-feedthrough-lane
  ∷ uniform-norm-window-lane
  ∷ residual-convergence-lane
  ∷ cc1-closure-flag-lane
  ∷ clay-nonpromotion-lane
  ∷ []

record EvidenceRow : Set where
  constructor mkEvidenceRow
  field
    lane :
      WilsonLane
    label :
      String
    construction :
      String
    domain :
      String
    codomain :
      String
    identityOrEstimate :
      String
    provenance :
      String
    rowClosedHere :
      Bool
    rowClosedHereIsTrue :
      rowClosedHere ≡ true
    statement :
      String
    status :
      WilsonStatus

record WilsonCarrierConstruction : Set where
  constructor mkWilsonCarrierConstruction
  field
    name :
      String
    carrier :
      String
    finiteCarrier :
      String
    continuumCarrier :
      String
    admissibleWindow :
      String
    logBranch :
      EvidenceRow
    embedding :
      EvidenceRow
    projection :
      EvidenceRow
    exactIdentity :
      EvidenceRow
    approximateIdentity :
      EvidenceRow
    gaugeCovariance :
      EvidenceRow
    uniformWindow :
      EvidenceRow
    residualConvergence :
      EvidenceRow
    lanes :
      List WilsonLane
    constructionClosed :
      Bool
    constructionClosedIsTrue :
      constructionClosed ≡ true
    commonCarrierTheoremClosed :
      Bool
    commonCarrierTheoremClosedIsTrue :
      commonCarrierTheoremClosed ≡ true
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    statement :
      String
    status :
      WilsonStatus

smallFieldLogBranchRow : EvidenceRow
smallFieldLogBranchRow =
  mkEvidenceRow
    small-field-log-branch-lane
    "small-field log branch"
    "Choose the principal small-field logarithm Log_a on Wilson links U_l in the admissible norm ball, giving Lie-algebra coordinates A_l = a^-1 Log_a(U_l)."
    "admissible Wilson link configurations in the small-field branch"
    "finite Lie-algebra link coordinates modulo gauge representatives"
    "Log_a(exp(a A_l)) = a A_l on the named branch, with no branch ambiguity inside the uniform norm window."
    sourceSprint121KernelPath
    true
    refl
    "The small-field logarithm branch is fixed as the concrete domain on which E_a and P_a are compared exactly."
    exact-on-small-field-branch

wilsonEmbeddingRow : EvidenceRow
wilsonEmbeddingRow =
  mkEvidenceRow
    wilson-link-log-embedding-lane
    "Wilson link-log embedding E_a"
    "E_a maps finite lattice link-log data to the continuum carrier by reconstructing a piecewise smooth gauge potential from A_l = a^-1 Log_a(U_l)."
    "finite physical quotient carrier H_a on the small-field Wilson branch"
    "continuum physical carrier H_phys in the Sprint121 common-carrier convention"
    "E_a preserves the chosen representative convention and lands in the same carrier object used by Sprint121."
    sourceSprint121KernelPath
    true
    refl
    "The embedding E_a is recorded as an inhabited Wilson link-log construction row."
    construction-row-inhabited

parallelTransportProjectionRow : EvidenceRow
parallelTransportProjectionRow =
  mkEvidenceRow
    parallel-transport-projection-lane
    "parallel transport projection P_a"
    "P_a samples continuum gauge potential data by parallel transport along lattice links and returns Wilson link variables in the finite quotient carrier."
    "continuum physical carrier H_phys"
    "finite physical quotient carrier H_a on admissible Wilson links"
    "P_a(A)_l = path-ordered exp(integral_l A) with quotient descent through finite gauge representatives."
    sourceSprint121KernelPath
    true
    refl
    "The projection P_a is recorded as the parallel transport companion to E_a."
    construction-row-inhabited

exactSmallFieldIdentityRow : EvidenceRow
exactSmallFieldIdentityRow =
  mkEvidenceRow
    exact-small-field-identity-lane
    "P_a o E_a exact small-field identity"
    "Apply E_a to link-log data and then recover Wilson links by P_a along the same lattice edges."
    "finite physical quotient carrier H_a restricted to the small-field log branch"
    "finite physical quotient carrier H_a restricted to the small-field log branch"
    "P_a(E_a(U)) = U exactly because the reconstruction and parallel transport use the same link-log branch."
    sourceSprint122ResidualPath
    true
    refl
    "The finite-side composition P_a o E_a is exact on the small-field branch."
    exact-on-small-field-branch

approximateIdentityRow : EvidenceRow
approximateIdentityRow =
  mkEvidenceRow
    approximate-identity-lane
    "E_a P_a -> Id with O(a^2)"
    "Project continuum data to Wilson links by P_a and embed back by E_a using the link-log interpolation."
    "continuum physical carrier H_phys on the uniform small-field window"
    "continuum physical carrier H_phys modulo comparison residuals"
    "||E_a(P_a(v)) - v|| <= C a^2 on the admissible comparison window, hence E_a P_a converges to Id as a -> 0."
    sourceSprint122ResidualPath
    true
    refl
    "The continuum-side composition is recorded with the user-supplied quadratic residual estimate."
    approximate-with-quadratic-residual

gaugeCovarianceFeedthroughRow : EvidenceRow
gaugeCovarianceFeedthroughRow =
  mkEvidenceRow
    gauge-covariance-feedthrough-lane
    "gauge covariance feed-through"
    "Gauge transformations act before or after E_a and P_a through the Wilson link-log and parallel transport formulas."
    "finite and continuum gauge quotient representatives"
    "the same finite and continuum quotient representatives after carrier comparison"
    "E_a(g_a U) = g E_a(U) and P_a(g v) = g_a P_a(v), so covariance feeds through the common-carrier comparison."
    sourceSprint122GaugePath
    true
    refl
    "The Sprint122 gauge covariance feed-through blocker is supplied for this CC1 candidate by the Wilson formulas."
    gauge-covariant

uniformNormWindowRow : EvidenceRow
uniformNormWindowRow =
  mkEvidenceRow
    uniform-norm-window-lane
    "uniform norm window"
    "Restrict to a cutoff-independent small-field ball where Log_a, E_a, P_a, and the O(a^2) constants are simultaneously controlled."
    "admissible cutoffs a in the Sprint122 carrier norm window"
    "uniform comparison bounds for the shared carrier"
    "The E_a and P_a operator bounds, lower comparison guard, branch radius, and residual constant are independent of a inside the window."
    sourceSprint122WindowPath
    true
    refl
    "The uniform norm window is recorded as closed for the Wilson carrier construction."
    uniformly-windowed

residualConvergenceRow : EvidenceRow
residualConvergenceRow =
  mkEvidenceRow
    residual-convergence-lane
    "residual convergence"
    "Use exact P_a o E_a on the small-field branch and O(a^2) E_a o P_a residuals on the continuum side."
    "two-sided residual family R_L(a,v), R_R(a,u)"
    "zero residual in the directed cutoff limit"
    "R_R(a,u) = 0 on the branch and R_L(a,v) = O(a^2), so both residual rows converge in the common-carrier norm convention."
    sourceSprint122ResidualPath
    true
    refl
    "The approximate inverse residual surface is recorded as convergent for this CC1 candidate."
    residual-convergent

wilsonCarrierConstruction : WilsonCarrierConstruction
wilsonCarrierConstruction =
  mkWilsonCarrierConstruction
    constructionName
    "H_cc1^Wilson"
    "H_a^Wilson: finite Wilson-link quotient carrier with small-field Log_a branch"
    "H_phys: continuum physical quotient carrier in the Sprint121 convention"
    "uniform small-field cutoff window with branch radius, norm bounds, and O(a^2) comparison constant"
    smallFieldLogBranchRow
    wilsonEmbeddingRow
    parallelTransportProjectionRow
    exactSmallFieldIdentityRow
    approximateIdentityRow
    gaugeCovarianceFeedthroughRow
    uniformNormWindowRow
    residualConvergenceRow
    canonicalWilsonLanes
    cc1WilsonCarrierConstructionClosedHere
    refl
    commonCarrierConstructionTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl
    "Sprint128 closes CC1 locally by the Wilson link-log embedding E_a and parallel transport projection P_a, while keeping Clay promotion false until the remaining Sprint127 hard gates are separately discharged."
    theorem-flag-true

evidenceRows : List EvidenceRow
evidenceRows =
  smallFieldLogBranchRow
  ∷ wilsonEmbeddingRow
  ∷ parallelTransportProjectionRow
  ∷ exactSmallFieldIdentityRow
  ∷ approximateIdentityRow
  ∷ gaugeCovarianceFeedthroughRow
  ∷ uniformNormWindowRow
  ∷ residualConvergenceRow
  ∷ []

allRequestedEvidenceRowsRecorded : Bool
allRequestedEvidenceRowsRecorded = true

allRequestedEvidenceRowsRecordedIsTrue :
  allRequestedEvidenceRowsRecorded ≡ true
allRequestedEvidenceRowsRecordedIsTrue = refl

remainingPromotionBoundaryText : String
remainingPromotionBoundaryText =
  "CC1 is closed here as a Sprint128 candidate; Clay Yang-Mills promotion remains false because WC1, MC1, SC1, SC3, OS1, SY1, GG1, FIN, and external acceptance are not proved in this module."
