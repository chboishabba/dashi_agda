module DASHI.Analysis.RiemannZetaLiteralFrontierSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.LiteralFrontierSchedulerExact as Literal
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact as RH
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as FinalCut

------------------------------------------------------------------------
-- LITERAL RH / ZETA FINAL-CARRIER SCHEDULER
--
-- The final consumer is already narrowed to exactly two analytic payments on
-- the universal pole-quotient carrier.  This owner applies close/redirect/reject
-- directly to those leaves and prunes historical diagnostics/downstream compiler
-- work from the forward research frontier.
------------------------------------------------------------------------

data RHZetaMove : Set where
  payUniversalOffAllowance
  paySameTaperGammaAllowance
  reopenDeterminantDiagnostic
  redoClusterMarginAnalysis
  rebuildFinalContradictionCompiler
  chooseFarTailCutoffAlone
  : RHZetaMove

move : RHZetaMove → Literal.LiteralFrontierMove
move payUniversalOffAllowance = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "universal pole-quotient Off assigned-allowance payment"
  ; Literal.moveReference = "prove B_off <= A_off at one common quarter-period crossing cutoff"
  ; Literal.residualReference = "literal final Off allowance payment remains open"
  ; Literal.consumerReference = "final pole-quotient RH contradiction consumer"
  ; Literal.sameObjectReference = "same literal universal pole-quotient taper and exact producer cutoff required"
  ; Literal.authorityReference = "analytic theorem payment required"
  ; Literal.paretoReference = "terminal live analytic leaf"
  }
move paySameTaperGammaAllowance = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "same-taper Gamma assigned-allowance payment"
  ; Literal.moveReference = "prove B_Gamma <= A_Gamma on the exact universal pole-quotient taper"
  ; Literal.residualReference = "literal final Gamma allowance payment remains open"
  ; Literal.consumerReference = "final pole-quotient RH contradiction consumer"
  ; Literal.sameObjectReference = "same literal universal pole-quotient taper as final consumer required"
  ; Literal.authorityReference = "analytic theorem payment required"
  ; Literal.paretoReference = "terminal live analytic leaf"
  }
move reopenDeterminantDiagnostic = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "historical determinant signed diagnostic"
  ; Literal.moveReference = "promote determinant taper scalarization to final pole-quotient leaf"
  ; Literal.residualReference = "carrier/taper mismatch to final consumer"
  ; Literal.consumerReference = "final pole-quotient RH contradiction consumer"
  ; Literal.sameObjectReference = "determinant taper is not definitionally the final pole-quotient taper"
  ; Literal.authorityReference = "diagnostic theorem does not pay final leaf"
  ; Literal.paretoReference = "pruned from terminal scheduler"
  }
move redoClusterMarginAnalysis = record
  { Literal.producer = Cross.repositoryReuse
  ; Literal.liveLeafReference = "owned cluster margin"
  ; Literal.moveReference = "re-derive cluster margin mathematics"
  ; Literal.residualReference = "none: cluster margin mathematics already owned"
  ; Literal.consumerReference = "downstream same-object attachment"
  ; Literal.sameObjectReference = "attachment remains downstream; derivation is already repository-owned"
  ; Literal.authorityReference = "repository theorem already present"
  ; Literal.paretoReference = "stale/already owned"
  }
move rebuildFinalContradictionCompiler = record
  { Literal.producer = Cross.repositoryReuse
  ; Literal.liveLeafReference = "final contradiction compiler"
  ; Literal.moveReference = "rebuild final allowance/order contradiction compiler"
  ; Literal.residualReference = "none: compiler is already reusable once literal payments exist"
  ; Literal.consumerReference = "final pole-quotient RH contradiction"
  ; Literal.sameObjectReference = "existing order transport and allowance assembly own this compiler path"
  ; Literal.authorityReference = "repository theorem already present"
  ; Literal.paretoReference = "stale/already owned"
  }
move chooseFarTailCutoffAlone = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "Off assigned-allowance payment"
  ; Literal.moveReference = "choose final Off cutoff from far-tail decay alone"
  ; Literal.residualReference = "final Off leaf requires one common cutoff fitting near+far budget into A_off"
  ; Literal.consumerReference = "Off allowance payment"
  ; Literal.sameObjectReference = "same cutoff must feed the exact Off producer"
  ; Literal.authorityReference = "consumer-strength mismatch"
  ; Literal.paretoReference = "known pruned subroute"
  }

outcome : (m : RHZetaMove) → Literal.LiteralMoveOutcome (move m)
outcome payUniversalOffAllowance = Literal.redirected record
  { Literal.frontierReducedOrRecharted = true
  ; Literal.frontierReducedOrRechartedIsTrue = refl
  ; Literal.nextResidualReference = "construct exact PoleQuotientOffAllowancePayment"
  ; Literal.retainedEvidenceReference = "retain owned cluster margin and downstream allowance/order compilers"
  ; Literal.redirectReference = "terminal Off payment"
  }
outcome paySameTaperGammaAllowance = Literal.redirected record
  { Literal.frontierReducedOrRecharted = true
  ; Literal.frontierReducedOrRechartedIsTrue = refl
  ; Literal.nextResidualReference = "construct exact PoleQuotientGammaAllowancePayment"
  ; Literal.retainedEvidenceReference = "retain owned cluster margin and downstream allowance/order compilers"
  ; Literal.redirectReference = "terminal Gamma payment"
  }
outcome reopenDeterminantDiagnostic = Literal.rejected record
  { Literal.reason = Literal.carrierMismatch
  ; Literal.rejectionReference = "final pole-quotient cut does not identify determinant taper with final taper"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }
outcome redoClusterMarginAnalysis = Literal.rejected record
  { Literal.reason = Literal.staleOrAlreadyOwned
  ; Literal.rejectionReference = "cluster margin mathematics is already owned and only downstream attachment remains"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }
outcome rebuildFinalContradictionCompiler = Literal.rejected record
  { Literal.reason = Literal.staleOrAlreadyOwned
  ; Literal.rejectionReference = "allowance/order transport compiler already produces final contradiction once payments are present"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }
outcome chooseFarTailCutoffAlone = Literal.rejected record
  { Literal.reason = Literal.consumerMismatch
  ; Literal.rejectionReference = "Off compiler requires one common crossing cutoff; far-tail decay alone is insufficient"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }

rhZetaLiteralPortfolio : Literal.LiteralFrontierPortfolio
rhZetaLiteralPortfolio = record
  { Literal.Move = RHZetaMove
  ; Literal.literalMove = move
  ; Literal.outcome = outcome
  ; Literal.liveConsumerReference = "universal pole-quotient final RH/zeta contradiction consumer"
  ; Literal.portfolioCompletenessReference = "authoritative final scheduler admits exactly Off and Gamma analytic payments; other entries are regression controls"
  ; Literal.residualRelevantOnly = true
  ; Literal.residualRelevantOnlyIsTrue = refl
  }

offLeafStillLive :
  FinalCut.finalLeafState FinalCut.universalPoleQuotientSignedOff ≡ FinalCut.live
offLeafStillLive = FinalCut.universalPoleQuotientOffIsLive

gammaLeafStillLive :
  FinalCut.finalLeafState FinalCut.sameTaperGammaPrecision ≡ FinalCut.live
gammaLeafStillLive = FinalCut.gammaPrecisionIsLive

finalCompilerAlreadyDownstream :
  RH.FinalRHAllowanceSchedulerBoundary.strictCombinedBudgetIsFreshAnalyticLeaf
    RH.canonicalFinalRHAllowanceSchedulerBoundary ≡ false
finalCompilerAlreadyDownstream = refl

rhStillOpen :
  RH.FinalRHAllowanceSchedulerBoundary.rhDerived
    RH.canonicalFinalRHAllowanceSchedulerBoundary ≡ false
rhStillOpen = refl

record RHZetaLiteralBoundary : Set where
  constructor rh-zeta-literal-boundary
  field
    exactlyTwoTerminalAnalyticPayments : Bool
    exactlyTwoTerminalAnalyticPaymentsIsTrue : exactlyTwoTerminalAnalyticPayments ≡ true
    determinantDiagnosticMayReplaceFinalCarrier : Bool
    determinantDiagnosticMayReplaceFinalCarrierIsFalse : determinantDiagnosticMayReplaceFinalCarrier ≡ false
    downstreamCompilerShouldBeRebuilt : Bool
    downstreamCompilerShouldBeRebuiltIsFalse : downstreamCompilerShouldBeRebuilt ≡ false

canonicalRHZetaLiteralBoundary : RHZetaLiteralBoundary
canonicalRHZetaLiteralBoundary =
  rh-zeta-literal-boundary true refl false refl false refl
