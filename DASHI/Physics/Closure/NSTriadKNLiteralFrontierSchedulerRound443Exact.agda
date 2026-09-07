module DASHI.Physics.Closure.NSTriadKNLiteralFrontierSchedulerRound443Exact where

------------------------------------------------------------------------
-- ROUND443 / USE THE LITERAL FRONTIER SCHEDULER ON THE CURRENT NS CUT
--
-- R442 has already compiled away the finite orientation/folding/amplitude/
-- R299-record seams.  Its authoritative residual consists of exactly two
-- analytic coordinates:
--
--   A. resolvent/heat realization of the literal R290 Cauchy weight;
--   B. cutoff-uniform signed spacetime payment for the explicit common cross.
--
-- This owner does not invent a third theorem.  It runs the generic literal
-- scheduler over that actual cut.  Both analytic coordinates are live redirects;
-- already-compiled finite routes are rejected as stale, the optional Schur
-- strategy is rejected as a mandatory intermediate, and a numerical diagnostic
-- is rejected as a theorem-closing move while remaining admissible as evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.LiteralFrontierSchedulerExact as Literal
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Physics.Closure.NSTriadKNDirectSignedCompanionFrontierRound442Exact as R442

data Round443Move : Set where
  realizeResolventHeat
  paySignedSpacetimeCross
  reopenFiniteFold
  requireSchurIntermediate
  numericalCrossDiagnosticAsClosure
  : Round443Move

move : Round443Move → Literal.LiteralFrontierMove
move realizeResolventHeat = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "R442 analytic coordinate A: resolvent/heat realization"
  ; Literal.moveReference = "install exact analytic representation of the literal R290 Cauchy resolvent weight by the one-cell heat factors consumed by R299/R440/R441"
  ; Literal.residualReference = "resolvent/heat same-object analytic realization remains open"
  ; Literal.consumerReference = "R423-ready direct signed-companion route / Package A"
  ; Literal.sameObjectReference = "same literal R290 weight and same R299/R440/R441 heat-factor carrier required"
  ; Literal.authorityReference = "symbolic theorem route; no numerical substitution"
  ; Literal.paretoReference = "live analytic coordinate; not dominated by already-closed finite algebra"
  }
move paySignedSpacetimeCross = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "R442 analytic coordinate B: signed spacetime payment"
  ; Literal.moveReference = "prove cutoff-uniform integrated upper bound for the explicit quadratic-companion common cross of exact R423 type"
  ; Literal.residualReference = "signed common-cross spacetime estimate remains open"
  ; Literal.consumerReference = "R423 direct signed acceptance / Package A"
  ; Literal.sameObjectReference = "must pay the exact common cross identified by R440/R441"
  ; Literal.authorityReference = "analytic theorem required"
  ; Literal.paretoReference = "co-live analytic coordinate; no total ordering with resolvent/heat realization is claimed"
  }
move reopenFiniteFold = record
  { Literal.producer = Cross.repositoryReuse
  ; Literal.liveLeafReference = "historical finite orientation/fold/amplitude/R299 seams"
  ; Literal.moveReference = "redo finite same-object fold machinery"
  ; Literal.residualReference = "none: R436--R441 already close this finite carrier stack"
  ; Literal.consumerReference = "R442 current frontier"
  ; Literal.sameObjectReference = "already compiler-owned"
  ; Literal.authorityReference = "repository theorem reuse already present"
  ; Literal.paretoReference = "strictly stale relative to current two-coordinate analytic cut"
  }
move requireSchurIntermediate = record
  { Literal.producer = Cross.symbolicProofRoute
  ; Literal.liveLeafReference = "optional R301 Schur sufficient-producer strategy"
  ; Literal.moveReference = "make Schur route mandatory before attacking R442"
  ; Literal.residualReference = "R442 explicitly says Schur is optional, not a required leaf"
  ; Literal.consumerReference = "direct signed-companion consumer"
  ; Literal.sameObjectReference = "different sufficient producer route"
  ; Literal.authorityReference = "cannot strengthen consumer prerequisites silently"
  ; Literal.paretoReference = "consumer mismatch: optional strategy cannot be promoted to mandatory coordinate"
  }
move numericalCrossDiagnosticAsClosure = record
  { Literal.producer = Cross.numericalExperiment
  ; Literal.liveLeafReference = "R442 signed spacetime payment"
  ; Literal.moveReference = "use numerical common-cross diagnostic as direct formal closure"
  ; Literal.residualReference = "may inform route choice but does not inhabit the analytic inequality"
  ; Literal.consumerReference = "Package A / Clay theorem route"
  ; Literal.sameObjectReference = "diagnostic must not be confused with proof term"
  ; Literal.authorityReference = "numericalExperiment maps to analogyOnly theorem authority"
  ; Literal.paretoReference = "informational value does not create theorem-closing authority"
  }

resolventRedirect : Literal.RedirectedLiteralMove (move realizeResolventHeat)
resolventRedirect = record
  { Literal.frontierReducedOrRecharted = true
  ; Literal.frontierReducedOrRechartedIsTrue = refl
  ; Literal.nextResidualReference = "exact R290 resolvent weight -> analytic one-cell heat-factor representation"
  ; Literal.retainedEvidenceReference = "retain R436--R441 finite same-object closure stack"
  ; Literal.redirectReference = "R442 analytic coordinate A"
  }

spacetimeRedirect : Literal.RedirectedLiteralMove (move paySignedSpacetimeCross)
spacetimeRedirect = record
  { Literal.frontierReducedOrRecharted = true
  ; Literal.frontierReducedOrRechartedIsTrue = refl
  ; Literal.nextResidualReference = "cutoff-uniform integrated payment of the explicit R440/R441 common cross"
  ; Literal.retainedEvidenceReference = "retain exact finite factorization and R299 normalization"
  ; Literal.redirectReference = "R442 analytic coordinate B"
  }

finiteFoldRejected : Literal.RejectedLiteralMove (move reopenFiniteFold)
finiteFoldRejected = record
  { Literal.reason = Literal.staleOrAlreadyOwned
  ; Literal.rejectionReference = "R442 records every finite fold/amplitude/R299 seam as closed"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }

mandatorySchurRejected : Literal.RejectedLiteralMove (move requireSchurIntermediate)
mandatorySchurRejected = record
  { Literal.reason = Literal.consumerMismatch
  ; Literal.rejectionReference = "R442: Schur route is sufficient/optional, not mandatory"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }

numericalClosureRejected : Literal.RejectedLiteralMove (move numericalCrossDiagnosticAsClosure)
numericalClosureRejected = record
  { Literal.reason = Literal.authorityInsufficient
  ; Literal.rejectionReference = "numerical diagnostic may reprioritise analytic search but cannot close R423/Package A"
  ; Literal.retainedForAudit = true
  ; Literal.retainedForAuditIsTrue = refl
  }

outcome : (m : Round443Move) → Literal.LiteralMoveOutcome (move m)
outcome realizeResolventHeat = Literal.redirected resolventRedirect
outcome paySignedSpacetimeCross = Literal.redirected spacetimeRedirect
outcome reopenFiniteFold = Literal.rejected finiteFoldRejected
outcome requireSchurIntermediate = Literal.rejected mandatorySchurRejected
outcome numericalCrossDiagnosticAsClosure = Literal.rejected numericalClosureRejected

round443CurrentPortfolio : Literal.LiteralFrontierPortfolio
round443CurrentPortfolio = record
  { Literal.Move = Round443Move
  ; Literal.literalMove = move
  ; Literal.outcome = outcome
  ; Literal.liveConsumerReference = "R442 direct signed-companion route -> R423 -> Package A"
  ; Literal.portfolioCompletenessReference = "R442 states exactly two analytic coordinates remain; the other entries here are explicit stale/authority regression controls"
  ; Literal.residualRelevantOnly = true
  ; Literal.residualRelevantOnlyIsTrue = refl
  }

------------------------------------------------------------------------
-- Exact receipts imported from the current frontier.
------------------------------------------------------------------------

round443FiniteSameObjectStackAlreadyClosed :
  R442.round442PhysicalR299RecordInhabited ≡ true
round443FiniteSameObjectStackAlreadyClosed =
  R442.round442PhysicalR299RecordInhabitedIsTrue

round443ResolventHeatStillOpen :
  R442.round442AnalyticResolventHeatRealizationClosed ≡ false
round443ResolventHeatStillOpen =
  R442.round442AnalyticResolventHeatRealizationClosedIsFalse

round443SignedSpacetimeStillOpen :
  R442.round442SignedCompanionSpacetimePaymentClosed ≡ false
round443SignedSpacetimeStillOpen =
  R442.round442SignedCompanionSpacetimePaymentClosedIsFalse

round443SchurNotMandatory : R442.round442SchurRouteMandatory ≡ false
round443SchurNotMandatory = R442.round442SchurRouteMandatoryIsFalse

round443PackageAStillOpen : R442.round442PackageAClosed ≡ false
round443PackageAStillOpen = R442.round442PackageAClosedIsFalse

round443ClayStillOpen : R442.round442ClayPromotion ≡ false
round443ClayStillOpen = R442.round442ClayPromotionIsFalse

record Round443Boundary : Set where
  constructor round443Boundary
  field
    finiteAlgebraShouldBeReopened : Bool
    finiteAlgebraShouldBeReopenedIsFalse : finiteAlgebraShouldBeReopened ≡ false
    exactlyTwoAnalyticCoordinatesRemain : Bool
    exactlyTwoAnalyticCoordinatesRemainIsTrue : exactlyTwoAnalyticCoordinatesRemain ≡ true
    schedulerClaimsUniqueOrderingBetweenTheTwo : Bool
    schedulerClaimsUniqueOrderingBetweenTheTwoIsFalse : schedulerClaimsUniqueOrderingBetweenTheTwo ≡ false
    numericalDiagnosticMayClosePackageA : Bool
    numericalDiagnosticMayClosePackageAIsFalse : numericalDiagnosticMayClosePackageA ≡ false

canonicalRound443Boundary : Round443Boundary
canonicalRound443Boundary =
  round443Boundary false refl true refl false refl false refl
