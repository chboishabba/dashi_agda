module DASHI.Physics.Closure.NSTriadKNThreeWeightAffineCertificateProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
-- Uses: Theorem 1(c), equations (42)--(43), the strict epsilon parameter,
-- and the three independent output/partial-adjoint weighted inequalities.
-- Relationship: supplies the affine weight method and the target certificate
-- shape, not the Navier--Stokes orbit-shell coefficients.
--
-- Author: Pierre Germain.
-- Title: "Multipliers, paramultipliers, and weak-strong uniqueness for the
-- Navier-Stokes equations".
-- Venue/year: Journal of Differential Equations 226 (2006), 373--428.
-- DOI: 10.1016/j.jde.2005.10.007.
-- Uses: Theorem 3.9 only as a model for a complete Sobolev-indexed ledger
-- with explicit boundary cases.
-- Relationship: no Germain theorem is consumed as an orbit-shell Schur bound.
--
-- Authors: DASHI repository contributors.
-- Title: "Strict three-weight affine feasibility certificate".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; the Navier--Stokes constraints are repository-original.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem as Source

data ConstraintOwner : Set where
  outputConstraint firstAdjointConstraint secondAdjointConstraint : ConstraintOwner

data OrderingClass : Set where
  outputLow leftLow rightLow comparable transition residual : OrderingClass

record AffineConstraint {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    owner : ConstraintOwner
    ordering : OrderingClass

    leftCoefficient rightCoefficient outputCoefficient : Scalar
    target epsilonMargin : Scalar

    evaluatedLeft evaluatedRight evaluatedOutput evaluatedTotal : Scalar
    affineIdentity : Set s
    strictBelowTarget : Set s

open AffineConstraint public

record ThreeWeightCandidate {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    leftExponent rightExponent outputExponent epsilon : Scalar

    leftWeightPositive : Set s
    rightWeightPositive : Set s
    outputWeightPositive : Set s
    epsilonStrictlyPositive : Set s

open ThreeWeightCandidate public

record StrictThreeWeightCertificate {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    candidate : ThreeWeightCandidate {s}

    outputCondition : OrderingClass → AffineConstraint {s}
    firstAdjointCondition : OrderingClass → AffineConstraint {s}
    secondAdjointCondition : OrderingClass → AffineConstraint {s}

    allOutputOrderingsStrict : Set s
    allFirstAdjointOrderingsStrict : Set s
    allSecondAdjointOrderingsStrict : Set s

    allGeometricSeriesConverge : Set s
    cancellationOrderSufficient : Set s
    repositorySeparationThresholdConsumed : Set s
    orbitConstantsIndependentOfCutoff : Set s
    helicityConstantsIndependentOfCutoff : Set s
    directionWeightPreservesConstraints : Set s

    grafakosTorresOutputCondition : Set s
    grafakosTorresFirstAdjointCondition : Set s
    grafakosTorresSecondAdjointCondition : Set s
    cutoffUniformThreeFunctionBound : Set s

open StrictThreeWeightCertificate public

record ExactAffineSolver {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    Constraint : Set s
    Candidate : Set s
    Certificate : Set s

    collectOutputLedger : Set s
    collectFirstAdjointLedger : Set s
    collectSecondAdjointLedger : Set s

    normalizeRationalConstraints : Set s
    solveAffineEqualities : Set s
    checkStrictInequalities : Set s
    checkEndpointAndBoundaryCases : Set s
    emitExactCertificate : Set s

    soundness : Set s

open ExactAffineSolver public

record AnalyticReadinessAudit : Set where
  constructor audit
  field
    outputLedgerRequired : Bool
    firstAdjointLedgerRequired : Bool
    secondAdjointLedgerRequired : Bool
    highHighToLowGainRequired : Bool
    repositoryThresholdRequired : Bool
    prematureCertificateForbidden : Bool
    unknownWeightCount : Nat
    requiredIndependentEquationCount : Nat

open AnalyticReadinessAudit public

analyticReadinessAudit : AnalyticReadinessAudit
analyticReadinessAudit = audit true true true true true true 3 3

record AnalyticReadinessReceipt : Set where
  constructor receipt
  field
    threeUnknownWeights : unknownWeightCount analyticReadinessAudit ≡ 3
    threeIndependentLedgersNeeded :
      requiredIndependentEquationCount analyticReadinessAudit ≡ 3
    noPrematureCertificate :
      prematureCertificateForbidden analyticReadinessAudit ≡ true

open AnalyticReadinessReceipt public

analyticReadinessReceipt : AnalyticReadinessReceipt
analyticReadinessReceipt = receipt refl refl refl

sourceAffineMethodRepresented : Bool
sourceAffineMethodRepresented = Source.grafakosTorresExponentSystemRepresented

sourceAffineMethodRepresentedIsTrue : sourceAffineMethodRepresented ≡ true
sourceAffineMethodRepresentedIsTrue =
  Source.grafakosTorresExponentSystemRepresentedIsTrue

exactAffineSolverSurfaceRepresented : Bool
exactAffineSolverSurfaceRepresented = true

exactAffineSolverSurfaceRepresentedIsTrue :
  exactAffineSolverSurfaceRepresented ≡ true
exactAffineSolverSurfaceRepresentedIsTrue = refl

strictNavierStokesThreeWeightCertificateClosed : Bool
strictNavierStokesThreeWeightCertificateClosed = false

strictNavierStokesThreeWeightCertificateClosedIsFalse :
  strictNavierStokesThreeWeightCertificateClosed ≡ false
strictNavierStokesThreeWeightCertificateClosedIsFalse = refl
