module DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact where

------------------------------------------------------------------------
-- RH H_off^pole: FINITE NEAR EVALUATION, NOT JUST MAJORIZATION
--
-- The checked 8889 budget-circularity return sharpens the analytic obligation:
-- a valid complement budget cannot be manufactured from the balance identity.
-- The off-ordinate channel must be independently evaluated closely enough for
-- the final window
--
--   B_off + B_Gamma < M_cluster.
--
-- After the generic cutoff theorem removes the infinite far shell and
-- reflection pairing removes sinh*sin, the unpaid zero-side object is finite:
--
--   sum_{sigma in nearOffFinset(t,J)}
--     m_sigma * integral 4 g_pole(u) cosh(a_sigma u)
--                         cos((b_sigma-t)u) du.
--
-- This file types the required signed evaluation receipt and fail-closes routes
-- that erase precisely the target-centred phase/sign information needed by the
-- consumer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as G2e
import DASHI.Analysis.RiemannHermitianSourceGapMapExact as Hermitian
import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact as Frobenius
import DASHI.Analysis.RiemannAristotlePoleQuotientLeanReturn8889Exact as Return

------------------------------------------------------------------------
-- Consumer-facing evaluation language.
--
-- `Within` is deliberately supplied by the real-analysis application.  This
-- owner does not fake an absolute-value metric in an unrelated scalar type.
------------------------------------------------------------------------

record SignedFiniteNearEvaluationSurface : Set₁ where
  constructor signed-finite-near-evaluation-surface
  field
    Scalar Error : Set
    signedNearValue : Scalar
    approximant : Scalar
    error : Error
    Within : Scalar → Scalar → Error → Set
    withinEvaluation : Within signedNearValue approximant error
    evaluationReference : String

open SignedFiniteNearEvaluationSurface public

------------------------------------------------------------------------
-- A downstream budget extraction is a separate receipt.  Knowing an
-- approximation is not by itself the inequality required by the RH consumer;
-- the application must prove how its approximant/error imply the chosen budget.
------------------------------------------------------------------------

record EvaluationProducesBudget
    (evaluation : SignedFiniteNearEvaluationSurface) : Set₁ where
  constructor evaluation-produces-budget
  field
    Budget : Set
    nearBudget : Budget
    ProducesRequiredUpper :
      SignedFiniteNearEvaluationSurface → Budget → Set
    producesRequiredUpper : ProducesRequiredUpper evaluation nearBudget
    budgetReference : String

open EvaluationProducesBudget public

------------------------------------------------------------------------
-- Candidate analytic route classes.
------------------------------------------------------------------------

data FiniteNearRoute : Set where
  directFiniteExponentialSum
  targetCenteredExplicitFormula
  localZeroCountOnly
  reflectionOnly
  absoluteEnvelopeMajorant
  montgomeryVaughanDirect
  unbridgedHermitianPoisson
  unbridgedPairKernelFrobenius
  namedHardyDonorOnly
  : FiniteNearRoute

------------------------------------------------------------------------
-- What an admitted route must preserve before it is allowed to claim it can
-- inhabit the finite-near producer socket.
------------------------------------------------------------------------

record PhasePreservingFiniteNearRoute (route : FiniteNearRoute) : Set₁ where
  constructor phase-preserving-finite-near-route
  field
    literalPoleTaperCarrierPreserved : Set
    targetCenteredGapPreserved : Set
    signedCosinePhasePreserved : Set
    multiplicityPreserved : Set
    finiteNearIndexSetPreserved : Set
    independentOfFinalBalanceIdentity : Set
    routeReference : String

open PhasePreservingFiniteNearRoute public

------------------------------------------------------------------------
-- Only route classes whose intended output language can preserve the literal
-- finite signed carrier receive constructors here.  Any other route can become
-- admissible later only through a new explicit carrier/interface bridge.
------------------------------------------------------------------------

data AdmissibleFiniteNearRoute : FiniteNearRoute → Set where
  directFiniteEstimateAdmissible :
    AdmissibleFiniteNearRoute directFiniteExponentialSum
  explicitFormulaAdmissible :
    AdmissibleFiniteNearRoute targetCenteredExplicitFormula

------------------------------------------------------------------------
-- Exact fail-closed route exclusions at the present frontier.
------------------------------------------------------------------------

localCountOnlyNotAdmissible :
  AdmissibleFiniteNearRoute localZeroCountOnly → ⊥
localCountOnlyNotAdmissible ()

reflectionOnlyNotAdmissible :
  AdmissibleFiniteNearRoute reflectionOnly → ⊥
reflectionOnlyNotAdmissible ()

absoluteEnvelopeNotAdmissible :
  AdmissibleFiniteNearRoute absoluteEnvelopeMajorant → ⊥
absoluteEnvelopeNotAdmissible ()

montgomeryVaughanDirectNotAdmissible :
  AdmissibleFiniteNearRoute montgomeryVaughanDirect → ⊥
montgomeryVaughanDirectNotAdmissible ()

unbridgedHermitianPoissonNotAdmissible :
  AdmissibleFiniteNearRoute unbridgedHermitianPoisson → ⊥
unbridgedHermitianPoissonNotAdmissible ()

unbridgedPairKernelNotAdmissible :
  AdmissibleFiniteNearRoute unbridgedPairKernelFrobenius → ⊥
unbridgedPairKernelNotAdmissible ()

namedHardyDonorOnlyNotAdmissible :
  AdmissibleFiniteNearRoute namedHardyDonorOnly → ⊥
namedHardyDonorOnlyNotAdmissible ()

------------------------------------------------------------------------
-- Producer package: admissible route + literal preservation + actual signed
-- evaluation + downstream budget extraction.
------------------------------------------------------------------------

record FiniteNearProducer : Set₁ where
  constructor finite-near-producer
  field
    route : FiniteNearRoute
    routeAdmissible : AdmissibleFiniteNearRoute route
    preservation : PhasePreservingFiniteNearRoute route
    evaluation : SignedFiniteNearEvaluationSurface
    budget : EvaluationProducesBudget evaluation

open FiniteNearProducer public

------------------------------------------------------------------------
-- Source-backed no-go receipts.
------------------------------------------------------------------------

localCountDoesNotControlTargetPhase :
  G2e.localZeroCountControlsCosinePhase G2e.canonicalG2eTargetCenteredSymmetryNoGo
  ≡ false
localCountDoesNotControlTargetPhase = refl

montgomeryVaughanDoesNotDirectlyCloseTargetSum :
  G2e.montgomeryVaughanOwnerDirectlyControlsThisLocalZeroCosineSum
    G2e.canonicalG2eTargetCenteredSymmetryNoGo ≡ false
montgomeryVaughanDoesNotDirectlyCloseTargetSum = refl

hermitianMixedKernelSummationStillOpen :
  Hermitian.mixedKernelSummationStillNew Hermitian.hermitianSourceGapBoundary
  ≡ true
hermitianMixedKernelSummationStillOpen = refl

pairKernelSummabilityStillOpen :
  Frobenius.offDiagonalPhiKernelSummabilityProvedHere
    Frobenius.pairKernelFrobeniusBoundary ≡ false
pairKernelSummabilityStillOpen = refl

budgetCircularityNoGoAlreadyOwned :
  Return.budgetCircularityNoGoOwned Return.canonicalPoleQuotientLeanReturn8889
  ≡ true
budgetCircularityNoGoAlreadyOwned = refl

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record FiniteNearEvaluationBoundary : Set where
  constructor finite-near-evaluation-boundary
  field
    finiteNearObjectAlreadyConstructed : Bool
    finiteNearObjectAlreadyConstructedIsTrue :
      finiteNearObjectAlreadyConstructed ≡ true

    targetCenteredSignedEvaluationRequired : Bool
    targetCenteredSignedEvaluationRequiredIsTrue :
      targetCenteredSignedEvaluationRequired ≡ true

    arbitraryUpperMajorantCountsAsEvaluation : Bool
    arbitraryUpperMajorantCountsAsEvaluationIsFalse :
      arbitraryUpperMajorantCountsAsEvaluation ≡ false

    directFiniteExponentialSumRouteAdmissible : Bool
    directFiniteExponentialSumRouteAdmissibleIsTrue :
      directFiniteExponentialSumRouteAdmissible ≡ true

    targetCenteredExplicitFormulaRouteAdmissible : Bool
    targetCenteredExplicitFormulaRouteAdmissibleIsTrue :
      targetCenteredExplicitFormulaRouteAdmissible ≡ true

    localCountRouteAdmissibleWithoutPhaseBridge : Bool
    localCountRouteAdmissibleWithoutPhaseBridgeIsFalse :
      localCountRouteAdmissibleWithoutPhaseBridge ≡ false

    montgomeryVaughanRouteAdmissibleWithoutCarrierBridge : Bool
    montgomeryVaughanRouteAdmissibleWithoutCarrierBridgeIsFalse :
      montgomeryVaughanRouteAdmissibleWithoutCarrierBridge ≡ false

    hermitianPoissonRouteAdmissibleWithoutLiteralCarrierBridge : Bool
    hermitianPoissonRouteAdmissibleWithoutLiteralCarrierBridgeIsFalse :
      hermitianPoissonRouteAdmissibleWithoutLiteralCarrierBridge ≡ false

    pairKernelRouteAdmissibleWithoutLiteralCarrierBridge : Bool
    pairKernelRouteAdmissibleWithoutLiteralCarrierBridgeIsFalse :
      pairKernelRouteAdmissibleWithoutLiteralCarrierBridge ≡ false

    namedHardyResultAdmissibleWithoutLiteralCarrierBridge : Bool
    namedHardyResultAdmissibleWithoutLiteralCarrierBridgeIsFalse :
      namedHardyResultAdmissibleWithoutLiteralCarrierBridge ≡ false

    finiteNearEvaluationClosed : Bool
    finiteNearEvaluationClosedIsFalse : finiteNearEvaluationClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    firstUnprovedTheorem : String

canonicalFiniteNearEvaluationBoundary : FiniteNearEvaluationBoundary
canonicalFiniteNearEvaluationBoundary =
  finite-near-evaluation-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "For the finite nearOffFinset attached to the high-ordinate exists_positive_taper_poleEven_zero taper, independently evaluate the signed reflection-paired sum 4*m_sigma*integral g_pole(u)*cosh(a_sigma*u)*cos((b_sigma-t)*u) du to an explicit approximant with error small enough that the induced near budget plus the already-owned far-shell budget and repaired Gamma budget lies below the quantitative cluster margin."
