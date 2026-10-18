module DASHI.Physics.Closure.NSTriadKNCanonicalBAnalyticCutsetASTExact where

------------------------------------------------------------------------
-- CANONICAL PERIODIC-B ANALYTIC CUTSET AST
--
-- Purpose
-- -------
-- Record the least-privilege theorem boundary after the modern direct R503 /
-- R568 archaeology.  This file does NOT prove either remaining Navier--Stokes
-- estimate.  It gives them exact types and pins every surrounding invariant to
-- the strongest theorem-bearing owner currently in the corpus.
--
-- Canonical new PDE leaf on the direct R423/R503 route:
--
--   forall cutoff terminal,
--     4 * integral(globalForcingFull cutoff) <= B(terminal),
--
-- with B independent of the Galerkin cutoff.
--
-- The literal critical-production absorption used by R414 is retained as a
-- separate analytic residual.  In particular this module does not infer that
-- an R568 inhabitant supplies the R414 production inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedOverlapFrontierRound586Exact as R586
import DASHI.Physics.Closure.NSTriadKNLiteralSpectatorResolventOverlapRound587Exact as R587
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventPhysicalShellFloorRound589Exact as R589
import DASHI.Physics.Closure.NSTriadKNDirectLeafALeastPrivilegeRound591Exact as R591
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Typed analytic atoms.
------------------------------------------------------------------------

data PeriodicBAnalyticAtom : Set where
  cutoffUniformLiveCommutatorBudget : PeriodicBAnalyticAtom
  cutoffUniformSameOutputEnvelopeMass : PeriodicBAnalyticAtom
  signedNestedSpacetimeTransport : PeriodicBAnalyticAtom
  literalCriticalProductionAbsorption : PeriodicBAnalyticAtom
  scalarFTCInstallation : PeriodicBAnalyticAtom
  nonnegativeIntegrationInstallation : PeriodicBAnalyticAtom

data ProofState : Set where
  theoremBearing : ProofState
  compilerOnly : ProofState
  openAnalytic : ProofState
  openStandardAnalysis : ProofState
  optionalProducer : ProofState

stateOf : PeriodicBAnalyticAtom → ProofState
stateOf cutoffUniformLiveCommutatorBudget = openAnalytic
stateOf cutoffUniformSameOutputEnvelopeMass = openAnalytic
stateOf signedNestedSpacetimeTransport = openAnalytic
stateOf literalCriticalProductionAbsorption = openAnalytic
stateOf scalarFTCInstallation = openStandardAnalysis
stateOf nonnegativeIntegrationInstallation = openStandardAnalysis

------------------------------------------------------------------------
-- 2. Exact canonical direct-leaf AST.
------------------------------------------------------------------------

module DirectLeafAST
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn =
    R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  module Support =
    R405.LiteralCutoffSupport
      Time initialTime integrateTo DerivativeOf

  module Comm =
    R568.LiveCommutatorOnly
      Time initialTime integrateTo DerivativeOf integration

  -- This is the canonical theorem statement, not a proxy.
  --
  -- The bound may depend on terminal time and fixed physical/background data,
  -- but its TYPE contains no cutoff argument.  Thus any inhabitant is
  -- definitionally cutoff-uniform at this interface.
  record CutoffUniformLiveCommutatorBudgetAST
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      bound : Time → ℚ

      paysLiteralR568 :
        (cutoff : Nat) (terminal : Time) →
        R567.four567
          * Comm.integratedGlobalForcingFull T R cutoff terminal
        ≤ bound terminal

  open CutoffUniformLiveCommutatorBudgetAST public

  -- Exact adapter into the pre-existing R568 consumer.  It introduces no
  -- additional estimate.
  toR568 :
    ∀ {T R} →
    CutoffUniformLiveCommutatorBudgetAST T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  toR568 P = record
    { Comm.cutoffIndependentCommutatorBound568 = bound P
    ; Comm.liveCommutatorOnlyBudget568 = paysLiteralR568 P
    }

------------------------------------------------------------------------
-- 3. Producer-side AST boundary.
--
-- R586 deliberately makes same-output envelope mass canonical while leaving
-- the producer route open.  R589's shell/resolvent ceiling is therefore only
-- an optional producer ingredient, not part of the direct-leaf theorem type.
------------------------------------------------------------------------

data SameOutputEnvelopeProducerAST : Set where
  directPhysicalSameOutputGram : SameOutputEnvelopeProducerAST
  pShellResolventDecay : SameOutputEnvelopeProducerAST
  absoluteRowColumnSchurFallback : SameOutputEnvelopeProducerAST

producerState :
  SameOutputEnvelopeProducerAST → ProofState
producerState directPhysicalSameOutputGram = optionalProducer
producerState pShellResolventDecay = optionalProducer
producerState absoluteRowColumnSchurFallback = optionalProducer

------------------------------------------------------------------------
-- 4. Bounded invariant ledger.
--
-- TRUE/FALSE values here are imported theorem-status receipts only.  They are
-- intentionally not used as proofs of the analytic leaf.
------------------------------------------------------------------------

record CanonicalBInvariantBounds : Set where
  field
    literalUnrestrictedNestedSameObject :
      R586.round586LiteralUnrestrictedNestedSameObjectClosed ≡ true

    operatorShellIsOuterForcing :
      R586.round586OperatorShellNormalizedToOuterForcing ≡ true

    localSignedOverlapEnvelope :
      R586.round586LocalSignedOverlapEnvelopeClosed ≡ true

    pointwiseMassDoesNotCloseFibre :
      R586.round586PointwiseMassAloneClosesSameOutputFibre ≡ false

    explicitSeparationDecayNotMandatory :
      R586.round586ExplicitSeparationDecayMandatory ≡ false

    cutoffUniformEnvelopeMassStillOpen :
      R586.round586CutoffUniformSameOutputEnvelopeMassClosed ≡ false

    signedSpacetimePaymentStillOpen :
      R586.round586SpacetimeSignedNestedPaymentClosed ≡ false

    localHermitianYoungClosed :
      R579.round579LocalHermitianEnvelopeClosed ≡ true

    shellResolventCeilingCompilerClosed :
      R589.round589LiteralSpectatorResolventShellCeilingCompilerClosed ≡ true

    shellResolventCeilingDoesNotCloseEnvelopeMass :
      R589.round589CutoffUniformSameOutputEnvelopeMassClosed ≡ false

    amplitudeHalfEliminated :
      R568.round568AmplitudeSpacetimeLeafEliminated ≡ true

    diagonalEstimateNotIndependent :
      R568.round568DiagonalNonlinearEstimateStillIndependent ≡ false

    liveCommutatorBudgetStillOpen :
      R568.round568LiveCommutatorSpacetimeBudgetClosed ≡ false

    temporalRouteNotCanonicalPrerequisite :
      R591.round591TemporalRouteCanonicalPrerequisite ≡ false

canonicalBInvariantBounds : CanonicalBInvariantBounds
canonicalBInvariantBounds = record
  { literalUnrestrictedNestedSameObject =
      R586.round586LiteralUnrestrictedNestedSameObjectClosedIsTrue
  ; operatorShellIsOuterForcing =
      R586.round586OperatorShellNormalizedToOuterForcingIsTrue
  ; localSignedOverlapEnvelope =
      R586.round586LocalSignedOverlapEnvelopeClosedIsTrue
  ; pointwiseMassDoesNotCloseFibre =
      R586.round586PointwiseMassAloneClosesSameOutputFibreIsFalse
  ; explicitSeparationDecayNotMandatory =
      R586.round586ExplicitSeparationDecayMandatoryIsFalse
  ; cutoffUniformEnvelopeMassStillOpen =
      R586.round586CutoffUniformSameOutputEnvelopeMassClosedIsFalse
  ; signedSpacetimePaymentStillOpen = refl
  ; localHermitianYoungClosed =
      R579.round579LocalHermitianEnvelopeClosedIsTrue
  ; shellResolventCeilingCompilerClosed =
      R589.round589LiteralSpectatorResolventShellCeilingCompilerClosedIsTrue
  ; shellResolventCeilingDoesNotCloseEnvelopeMass = refl
  ; amplitudeHalfEliminated =
      R568.round568AmplitudeSpacetimeLeafEliminatedIsTrue
  ; diagonalEstimateNotIndependent = refl
  ; liveCommutatorBudgetStillOpen =
      R568.round568LiveCommutatorSpacetimeBudgetClosedIsFalse
  ; temporalRouteNotCanonicalPrerequisite =
      R591.round591TemporalRouteCanonicalPrerequisiteIsFalse
  }

------------------------------------------------------------------------
-- 5. Residual cutset.
------------------------------------------------------------------------

data CanonicalBResidual : Set where
  missingR568CutoffUniformLiveCommutatorBudget : CanonicalBResidual
  missingR414LiteralCriticalProductionAbsorption : CanonicalBResidual
  missingConcreteScalarFTC : CanonicalBResidual
  missingConcreteNonnegativeIntegration : CanonicalBResidual
  periodicBAnalyticCutsetPaid : CanonicalBResidual

currentCanonicalBResidual : CanonicalBResidual
currentCanonicalBResidual =
  missingR568CutoffUniformLiveCommutatorBudget

-- The direct R568 theorem is the first current analytic leaf.
-- The R414 production inequality remains separately open and is not discharged
-- by an inhabitant of the direct-leaf AST.

canonicalDirectR568LeafClosed : Bool
canonicalDirectR568LeafClosed = false

canonicalR414ProductionAbsorptionClosed : Bool
canonicalR414ProductionAbsorptionClosed = false

canonicalPeriodicBAnalyticCutsetPaid : Bool
canonicalPeriodicBAnalyticCutsetPaid = false

canonicalDirectR568LeafClosedIsFalse :
  canonicalDirectR568LeafClosed ≡ false
canonicalDirectR568LeafClosedIsFalse = refl

canonicalR414ProductionAbsorptionClosedIsFalse :
  canonicalR414ProductionAbsorptionClosed ≡ false
canonicalR414ProductionAbsorptionClosedIsFalse = refl

canonicalPeriodicBAnalyticCutsetPaidIsFalse :
  canonicalPeriodicBAnalyticCutsetPaid ≡ false
canonicalPeriodicBAnalyticCutsetPaidIsFalse = refl
