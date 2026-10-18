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
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
import DASHI.Physics.Closure.NSTriadKNLiveSpectatorResolventNestedLeafABidiExact as LiveNested
import DASHI.Physics.Closure.NSTriadKNWeightedNestedSignedCrossThreeOrbitBidiExact as SignedThreeOrbit
import DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact as Signed29
import DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedSignedOverlapRound584Exact as R584

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Typed analytic atoms.
------------------------------------------------------------------------

data PeriodicBAnalyticAtom : Set where
  cutoffUniformLiveCommutatorBudget : PeriodicBAnalyticAtom
  cutoffUniformSameOutputEnvelopeMass : PeriodicBAnalyticAtom
  signedBilinearTransportDecomposition : PeriodicBAnalyticAtom
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
stateOf signedBilinearTransportDecomposition = theoremBearing
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
  -- 2a. Exact producer-side live nested transport.
  --
  -- This is not a second analytic leaf.  LiveNested proves that the literal
  -- R568 forcing scalar is the same live spectator-resolvent / R573 nested
  -- signed object, including canonical output summation and integration.
  -- An inhabitant of its spacetime budget therefore compiles directly to the
  -- SAME R568 consumer above.
  ------------------------------------------------------------------------

  record SignedNestedTransportProducerAST
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      nestedBudget :
        LiveNested.LiveNested.NestedSpectatorSpacetimeBudget
          Time initialTime integrateTo DerivativeOf integration T R

  open SignedNestedTransportProducerAST public

  signedNestedTransportToR568 :
    ∀ {T R} →
    SignedNestedTransportProducerAST T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  signedNestedTransportToR568 {T} {R} P =
    LiveNested.LiveNested.nestedBudgetBuildsR568
      Time initialTime integrateTo DerivativeOf integration
      (nestedBudget P)

  signedNestedTransportToDirectAST :
    ∀ {T R} →
    SignedNestedTransportProducerAST T R →
    CutoffUniformLiveCommutatorBudgetAST T R
  signedNestedTransportToDirectAST {T} {R} P =
    let
      B = signedNestedTransportToR568 P
    in
    record
      { bound = Comm.cutoffIndependentCommutatorBound568 B
      ; paysLiteralR568 = Comm.liveCommutatorOnlyBudget568 B
      }

  ----------------------------------------------------------------------
  -- Signed bilinear transport producer for the R568 leaf.
  --
  -- R584 supplies the literal unrestricted nested same-output pair carrier
  -- and maps each pair into R29.SignedCrossShellCell.  R29 supplies the
  -- finite signed aggregation theorem.  What is NOT already proved is the
  -- same-object weld from the live R568 global forcing observable to a
  -- concrete family of those cells, nor the cutoff-uniform spacetime payment.
  --
  -- The two records below expose exactly those two remaining jobs.  The
  -- compiler into R568 uses only integration congruence; it introduces no
  -- inequality beyond the supplied signed spacetime payment.
  ----------------------------------------------------------------------

  record SignedBilinearTransportDecompositionAST
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      signedCells :
        Nat → Time → List Signed29.SignedCrossShellCell

      liveForcingIsSignedBilinearAggregate :
        (cutoff : Nat) (time : Time) →
        Comm.globalForcingFull T R cutoff time
        ≡ Signed29.sumSignedPairings (signedCells cutoff time)

  open SignedBilinearTransportDecompositionAST public

  record CutoffUniformSignedBilinearTransportBudgetAST
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (D : SignedBilinearTransportDecompositionAST T R) : Set₁ where
    field
      signedTransportBound : Time → ℚ

      paysSignedBilinearTransport :
        (cutoff : Nat) (terminal : Time) →
        R567.four567
          * integrateTo
              (λ time →
                Signed29.sumSignedPairings
                  (signedCells D cutoff time))
              terminal
        ≤ signedTransportBound terminal

  open CutoffUniformSignedBilinearTransportBudgetAST public

  signedBilinearTransportBuildsR568 :
    ∀ {T R}
      {D : SignedBilinearTransportDecompositionAST T R} →
    CutoffUniformSignedBilinearTransportBudgetAST T R D →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  signedBilinearTransportBuildsR568 {T} {R} {D} P =
    record
      { Comm.cutoffIndependentCommutatorBound568 =
          signedTransportBound P
      ; Comm.liveCommutatorOnlyBudget568 = λ cutoff terminal →
          let
            live =
              Comm.integratedGlobalForcingFull T R cutoff terminal

            signed =
              integrateTo
                (λ time →
                  Signed29.sumSignedPairings
                    (signedCells D cutoff time))
                terminal

            sameObject :
              live ≡ signed
            sameObject =
              R495.integrateCongruent integration
                (Comm.globalForcingFull T R cutoff)
                (λ time →
                  Signed29.sumSignedPairings
                    (signedCells D cutoff time))
                (liveForcingIsSignedBilinearAggregate D cutoff)
                terminal

            paid :
              R567.four567 * signed
              ≤ signedTransportBound P terminal
            paid = paysSignedBilinearTransport P cutoff terminal
          in
          subst
            (λ selected →
              R567.four567 * selected
              ≤ signedTransportBound P terminal)
            (sym sameObject)
            paid
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

    literalNestedPairMapsToSignedBilinearCell :
      R584.round584LocalSignedOverlapEnvelopeClosed ≡ true

    finiteSignedBilinearAggregationClosed :
      Signed29.crossShellAlmostOrthogonalityScalarCoreClosed ≡ true

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


    liveNestedOutputSameObjectWeld :
      LiveNested.liveNestedR568OutputSameObjectWeldClosed ≡ true

    liveNestedIntegrationTransport :
      LiveNested.liveNestedIntegrationTransportClosed ≡ true

    liveNestedBudgetCompilerToR568 :
      LiveNested.liveNestedBudgetCompilesToR568 ≡ true

    liveNestedSpacetimeEstimateStillOpen :
      LiveNested.liveNestedCutoffUniformSpacetimeEstimateClosed ≡ false

    bilinearSignedThreeOrbitDecomposition :
      SignedThreeOrbit.signedHermitianConsumerDescendsToThreeBonyOrbits ≡ true

    bilinearSignedTransportKeepsNormDelayed :
      SignedThreeOrbit.normIntroducedBeforeSignedCross ≡ false

    bilinearSignedThreeOrbitBudgetStillOpen :
      SignedThreeOrbit.cutoffUniformSignedThreeOrbitBudgetClosed ≡ false

canonicalBInvariantBounds : CanonicalBInvariantBounds
canonicalBInvariantBounds = record
  { literalUnrestrictedNestedSameObject =
      R586.round586LiteralUnrestrictedNestedSameObjectClosedIsTrue
  ; operatorShellIsOuterForcing =
      R586.round586OperatorShellNormalizedToOuterForcingIsTrue
  ; localSignedOverlapEnvelope =
      R586.round586LocalSignedOverlapEnvelopeClosedIsTrue
  ; literalNestedPairMapsToSignedBilinearCell =
      R584.round584LocalSignedOverlapEnvelopeClosedIsTrue
  ; finiteSignedBilinearAggregationClosed =
      Signed29.crossShellAlmostOrthogonalityScalarCoreClosedIsTrue
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
  ; liveNestedOutputSameObjectWeld =
      LiveNested.liveNestedR568OutputSameObjectWeldClosedIsTrue
  ; liveNestedIntegrationTransport = refl
  ; liveNestedBudgetCompilerToR568 =
      LiveNested.liveNestedBudgetCompilesToR568IsTrue
  ; liveNestedSpacetimeEstimateStillOpen = refl
  ; bilinearSignedThreeOrbitDecomposition =
      SignedThreeOrbit.signedHermitianConsumerDescendsToThreeBonyOrbitsIsTrue
  ; bilinearSignedTransportKeepsNormDelayed =
      SignedThreeOrbit.normIntroducedBeforeSignedCrossIsFalse
  ; bilinearSignedThreeOrbitBudgetStillOpen = refl
  }

------------------------------------------------------------------------
-- 5. R568 producer frontier.
--
-- The canonical global residual remains the R568 budget itself.  Internally,
-- the preferred signed producer is now typed as two exact sub-obligations:
--
--   (i) live global forcing = finite R29 signed bilinear aggregate;
--  (ii) cutoff-uniform spacetime payment of that same signed aggregate.
--
-- R29/R584 already own the finite carrier and local signed envelope; neither
-- theorem is misreported as the missing global/time estimate.
------------------------------------------------------------------------

data CanonicalR568SignedProducerResidual : Set where
  missingLiveForcingSignedBilinearSameObjectWeld :
    CanonicalR568SignedProducerResidual
  missingCutoffUniformSignedBilinearSpacetimePayment :
    CanonicalR568SignedProducerResidual
  canonicalR568SignedProducerPaid :
    CanonicalR568SignedProducerResidual

currentCanonicalR568SignedProducerResidual :
  CanonicalR568SignedProducerResidual
currentCanonicalR568SignedProducerResidual =
  missingLiveForcingSignedBilinearSameObjectWeld

canonicalR568SignedFiniteAggregationClosed : Bool
canonicalR568SignedFiniteAggregationClosed =
  Signed29.crossShellAlmostOrthogonalityScalarCoreClosed

canonicalR568LiteralNestedToSignedCellClosed : Bool
canonicalR568LiteralNestedToSignedCellClosed =
  R584.round584LocalSignedOverlapEnvelopeClosed

canonicalR568LiveForcingSignedBilinearSameObjectWeldClosed : Bool
canonicalR568LiveForcingSignedBilinearSameObjectWeldClosed = false

canonicalR568SignedBilinearSpacetimePaymentClosed : Bool
canonicalR568SignedBilinearSpacetimePaymentClosed = false

canonicalR568SignedFiniteAggregationClosedIsTrue :
  canonicalR568SignedFiniteAggregationClosed ≡ true
canonicalR568SignedFiniteAggregationClosedIsTrue =
  Signed29.crossShellAlmostOrthogonalityScalarCoreClosedIsTrue

canonicalR568LiteralNestedToSignedCellClosedIsTrue :
  canonicalR568LiteralNestedToSignedCellClosed ≡ true
canonicalR568LiteralNestedToSignedCellClosedIsTrue =
  R584.round584LocalSignedOverlapEnvelopeClosedIsTrue

canonicalR568LiveForcingSignedBilinearSameObjectWeldClosedIsFalse :
  canonicalR568LiveForcingSignedBilinearSameObjectWeldClosed ≡ false
canonicalR568LiveForcingSignedBilinearSameObjectWeldClosedIsFalse = refl

canonicalR568SignedBilinearSpacetimePaymentClosedIsFalse :
  canonicalR568SignedBilinearSpacetimePaymentClosed ≡ false
canonicalR568SignedBilinearSpacetimePaymentClosedIsFalse = refl

------------------------------------------------------------------------
-- 6. Residual cutset.
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

canonicalR568BoundaryBoundIntoAST : Bool
canonicalR568BoundaryBoundIntoAST = true

canonicalSignedNestedTransportCompilerBoundIntoAST : Bool
canonicalSignedNestedTransportCompilerBoundIntoAST = true

canonicalBilinearSignedThreeOrbitDecompositionBoundIntoAST : Bool
canonicalBilinearSignedThreeOrbitDecompositionBoundIntoAST = true

canonicalDirectR568LeafClosed : Bool
canonicalDirectR568LeafClosed = false

canonicalR414ProductionAbsorptionClosed : Bool
canonicalR414ProductionAbsorptionClosed = false

canonicalPeriodicBAnalyticCutsetPaid : Bool
canonicalPeriodicBAnalyticCutsetPaid = false

canonicalR568BoundaryBoundIntoASTIsTrue :
  canonicalR568BoundaryBoundIntoAST ≡ true
canonicalR568BoundaryBoundIntoASTIsTrue = refl

canonicalSignedNestedTransportCompilerBoundIntoASTIsTrue :
  canonicalSignedNestedTransportCompilerBoundIntoAST ≡ true
canonicalSignedNestedTransportCompilerBoundIntoASTIsTrue = refl

canonicalBilinearSignedThreeOrbitDecompositionBoundIntoASTIsTrue :
  canonicalBilinearSignedThreeOrbitDecompositionBoundIntoAST ≡ true
canonicalBilinearSignedThreeOrbitDecompositionBoundIntoASTIsTrue = refl

canonicalDirectR568LeafClosedIsFalse :
  canonicalDirectR568LeafClosed ≡ false
canonicalDirectR568LeafClosedIsFalse = refl

canonicalR414ProductionAbsorptionClosedIsFalse :
  canonicalR414ProductionAbsorptionClosed ≡ false
canonicalR414ProductionAbsorptionClosedIsFalse = refl

canonicalPeriodicBAnalyticCutsetPaidIsFalse :
  canonicalPeriodicBAnalyticCutsetPaid ≡ false
canonicalPeriodicBAnalyticCutsetPaidIsFalse = refl
