module DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact where

------------------------------------------------------------------------
-- ROUND486 / RECONCILE CAUCHY ARCHAEOLOGY WITH THE CANONICAL CLAY CONSUMER
--
-- R481-R485 applied the repository proof-search discipline to the Cauchy route
-- and exposed a real same-object correction:
--
--   R447 full = diagonal + offDiagonal,
--   R448 offDiagonal = literal R397/R385 signed flux,
--
-- so the full R477 resolved form is not the R432 signed-cross object.
--
-- A downstream audit then matters even more: R393/R459 show +F(T) is not the
-- terminal orientation consumed by the temporal Package-A route, while the
-- authoritative R282/R423 highest-alpha route bypasses endpoint bookkeeping
-- entirely.  R423 consumes one cutoff-uniform INTEGRATED signed
-- quadratic-companion heat-cross payment and sends it directly to the critical
-- barrier.
--
-- Therefore the canonical live Clay search target is restored to exactly that
-- R423 payment.  Cauchy/full-form, temporal endpoint and R284 critical-cone
-- routes remain producer strategies or archaeology; none is silently promoted
-- to a mandatory prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Core.QueryPromotionResidualBidiExact as Residual
import DASHI.Physics.Closure.NSTriadKNPostCriticalElementNoGoHighestAlphaRound282Exact as R282
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNCauchyTerminalFluxEndpointRound458Exact as R458
import DASHI.Physics.Closure.NSTriadKNTerminalFluxPaidTemporalReductionRound459Exact as R459
import DASHI.Physics.Closure.NSTriadKNCauchyFullVsSignedFluxBoundaryRound484Exact as R484

------------------------------------------------------------------------
-- One canonical direct target.
------------------------------------------------------------------------

data CanonicalNSResidual : Set where
  missingCutoffUniformSignedCompanionBudget : CanonicalNSResidual
  canonicalNSConsumerClosed : CanonicalNSResidual

record CanonicalNSStatus : Set where
  constructor canonical-ns-status
  field
    cutoffUniformSignedCompanionBudgetPresent : Bool

open CanonicalNSStatus public

firstCanonicalNSResidual : CanonicalNSStatus → CanonicalNSResidual
firstCanonicalNSResidual (canonical-ns-status false) =
  missingCutoffUniformSignedCompanionBudget
firstCanonicalNSResidual (canonical-ns-status true) = canonicalNSConsumerClosed

data CanonicalNSProducer : Set where
  proveCutoffUniformIntegratedSignedCompanionBudget : CanonicalNSProducer
  noCanonicalNSProducerNeeded : CanonicalNSProducer

producerFor : CanonicalNSResidual → CanonicalNSProducer
producerFor missingCutoffUniformSignedCompanionBudget =
  proveCutoffUniformIntegratedSignedCompanionBudget
producerFor canonicalNSConsumerClosed = noCanonicalNSProducerNeeded

data SearchMechanism : Set where
  Think : SearchMechanism
  Done : SearchMechanism

mechanismFor : CanonicalNSResidual → SearchMechanism
mechanismFor missingCutoffUniformSignedCompanionBudget = Think
mechanismFor canonicalNSConsumerClosed = Done

currentCanonicalNSStatus : CanonicalNSStatus
currentCanonicalNSStatus = canonical-ns-status false

currentFirstMissingIsR423Budget :
  firstCanonicalNSResidual currentCanonicalNSStatus
  ≡ missingCutoffUniformSignedCompanionBudget
currentFirstMissingIsR423Budget = refl

currentProducerIsDirectSignedCompanionProof :
  producerFor (firstCanonicalNSResidual currentCanonicalNSStatus)
  ≡ proveCutoffUniformIntegratedSignedCompanionBudget
currentProducerIsDirectSignedCompanionProof = refl

currentMechanismIsThink :
  mechanismFor (firstCanonicalNSResidual currentCanonicalNSStatus) ≡ Think
currentMechanismIsThink = refl

------------------------------------------------------------------------
-- Route dispositions / learned pruning.
------------------------------------------------------------------------

-- Canonical direct R423 search is admitted.
directR423Disposition : Least.RouteDisposition
directR423Disposition = Least.admitted

-- Treating the FULL Cauchy form as the signed-cross identity is a carrier error.
fullCauchyAsSignedCrossDisposition : Least.RouteDisposition
fullCauchyAsSignedCrossDisposition = Least.rejected Least.carrierMismatch

-- R448's off-diagonal representation is already owned; do not re-prove it.
r448OffDiagonalRepresentationDisposition : Least.RouteDisposition
r448OffDiagonalRepresentationDisposition = Least.redirectedReuse

-- The R284/R434 critical-cone decomposition is a valid optional producer route,
-- but its three physical region payments remain open; it is not a prerequisite
-- of the direct R423 target.
criticalConeDecompositionDisposition : Least.RouteDisposition
criticalConeDecompositionDisposition = Least.admitted

-- +F(T) is not a prerequisite of the R393/R459 temporal consumer: that route
-- uses -F(T), which is already paid by R458.
positiveTerminalFluxAsClayPrerequisiteDisposition : Least.RouteDisposition
positiveTerminalFluxAsClayPrerequisiteDisposition =
  Least.rejected Least.strengthMismatch

------------------------------------------------------------------------
-- Exact pins to repository-owned routing facts.
------------------------------------------------------------------------

round486R423IsCanonicalShortestConsumer : Bool
round486R423IsCanonicalShortestConsumer =
  R282.round282DirectRound423SignedCompanionHighestAlpha

round486R423TargetIsCutoffUniformSignedCompanionBudget : Bool
round486R423TargetIsCutoffUniformSignedCompanionBudget =
  R282.round282R423TargetIsCutoffUniformSignedCompanionBudget

round486CrossOutputCoherenceRequired : Bool
round486CrossOutputCoherenceRequired =
  R282.round282CrossOutputCoherenceStillRequired

round486R284DecompositionMandatory : Bool
round486R284DecompositionMandatory =
  R282.round282R284DecompositionMandatoryForR423

round486R284DeepFarLowPhysicalWeldClosed : Bool
round486R284DeepFarLowPhysicalWeldClosed =
  R434.round434DeepFarLowPhysicalWeldClosed

round486R284DeepHighHighPhysicalWeldClosed : Bool
round486R284DeepHighHighPhysicalWeldClosed =
  R434.round434DeepHighHighPhysicalWeldClosed

round486R284CriticalConeCovarianceClosed : Bool
round486R284CriticalConeCovarianceClosed =
  R434.round434PhysicalCriticalConeCovarianceClosed

round486FullCauchySameObjectAsSignedFlux : Bool
round486FullCauchySameObjectAsSignedFlux =
  R484.round484FullFormSameObjectAsSignedFlux

round486NegativeTerminalFluxPaid : Bool
round486NegativeTerminalFluxPaid = R458.round458NegativeTerminalR397FluxPaid

round486TerminalEndpointRemovedFromTemporalFrontier : Bool
round486TerminalEndpointRemovedFromTemporalFrontier =
  R459.round459TerminalEndpointRemovedFromTemporalFrontier

round486PositiveTerminalFluxIsCanonicalClayLeaf : Bool
round486PositiveTerminalFluxIsCanonicalClayLeaf = false

round486DirectR423BudgetClosed : Bool
round486DirectR423BudgetClosed =
  R282.round282PhysicalIntegratedCoherentBudgetClosed

round486PackageAClosed : Bool
round486PackageAClosed = false

round486ClayPromotion : Bool
round486ClayPromotion = false

------------------------------------------------------------------------
-- Least-privilege admission certifies the SEARCH route, not the theorem.
------------------------------------------------------------------------

directR423RouteAdmission : Least.RouteAdmission
directR423RouteAdmission =
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

directR423LiveSearch : Least.LiveProofSearch
directR423LiveSearch = Least.elaborateRoute directR423RouteAdmission

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

genericProducerNameDoesNotCreateReceipt : Residual.ProducerNameCreatesReceipt → ⊥
genericProducerNameDoesNotCreateReceipt = Residual.producerNameDoesNotCreateReceipt

genericLaterStageDoesNotRepairEarlierGap :
  Residual.LaterStageRepairsEarlierGap → ⊥
genericLaterStageDoesNotRepairEarlierGap = Residual.laterStageDoesNotRepairEarlierGap

round486R423IsCanonicalShortestConsumerIsTrue :
  round486R423IsCanonicalShortestConsumer ≡ true
round486R423IsCanonicalShortestConsumerIsTrue =
  R282.round282DirectRound423SignedCompanionHighestAlphaIsTrue

round486R423TargetIsCutoffUniformSignedCompanionBudgetIsTrue :
  round486R423TargetIsCutoffUniformSignedCompanionBudget ≡ true
round486R423TargetIsCutoffUniformSignedCompanionBudgetIsTrue =
  R282.round282R423TargetIsCutoffUniformSignedCompanionBudgetIsTrue

round486CrossOutputCoherenceRequiredIsFalse :
  round486CrossOutputCoherenceRequired ≡ false
round486CrossOutputCoherenceRequiredIsFalse =
  R282.round282CrossOutputCoherenceStillRequiredIsFalse

round486R284DecompositionMandatoryIsFalse :
  round486R284DecompositionMandatory ≡ false
round486R284DecompositionMandatoryIsFalse =
  R282.round282R284DecompositionMandatoryForR423IsFalse

round486FullCauchySameObjectAsSignedFluxIsFalse :
  round486FullCauchySameObjectAsSignedFlux ≡ false
round486FullCauchySameObjectAsSignedFluxIsFalse =
  R484.round484FullFormSameObjectAsSignedFluxIsFalse

round486PositiveTerminalFluxIsCanonicalClayLeafIsFalse :
  round486PositiveTerminalFluxIsCanonicalClayLeaf ≡ false
round486PositiveTerminalFluxIsCanonicalClayLeafIsFalse = refl

round486DirectR423BudgetClosedIsFalse :
  round486DirectR423BudgetClosed ≡ false
round486DirectR423BudgetClosedIsFalse = refl

round486ClayPromotionIsFalse : round486ClayPromotion ≡ false
round486ClayPromotionIsFalse = refl
