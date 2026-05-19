module DASHI.Physics.Closure.ContinuumLimitTheorem where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.G3P2LimitConvergenceSurface as G3P2
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2CanonicalPressureMetricP2BridgeOrObstruction as W2PM

------------------------------------------------------------------------
-- Continuum-limit theorem candidate.
--
-- This module is deliberately non-promoting.  It records the exact typed
-- surface needed before a lattice/discrete DASHI candidate can be upgraded to
-- a continuum metric/connection/Einstein convergence theorem.  The existing
-- W2 state is consumed as a bridge-or-obstruction/rate boundary: W2 affects
-- the available rate surface, not the existence shape of a future continuum
-- theorem.  No W2 authority token, W2 closure, unification promotion, curved
-- GR recovery, or Einstein-equation receipt is constructed here.

data ContinuumLimitCandidateStatus : Set where
  theoremRequestOnlyW2RateBlockedNoPromotion :
    ContinuumLimitCandidateStatus

data W2ContinuumResolutionRole : Set where
  w2ResolutionAffectsRateNotExistence :
    W2ContinuumResolutionRole

data ContinuumLimitMissingPrimitive : Set where
  missingLatticeEmbedding :
    ContinuumLimitMissingPrimitive

  missingContinuumFieldConvergence :
    ContinuumLimitMissingPrimitive

  missingMetricErrorBound :
    ContinuumLimitMissingPrimitive

  missingConnectionErrorBound :
    ContinuumLimitMissingPrimitive

  missingEinsteinTensorContinuity :
    ContinuumLimitMissingPrimitive

  missingW2BridgeOrObstructionResolution :
    ContinuumLimitMissingPrimitive

record ContinuumLimitEpsilonRateSurface : Setω where
  field
    DiscreteScale :
      Set

    Epsilon :
      Set

    Rate :
      Epsilon →
      DiscreteScale →
      Set

    rateComposesWithW2 :
      W2ContinuumResolutionRole

    w2RateBoundary :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w2BridgeOrObstruction :
      W2PM.W2CanonicalPressureMetricP2ObstructionReceipt

    rateBoundary :
      List String

record ContinuumLimitAnalyticPrimitives
  (rate : ContinuumLimitEpsilonRateSurface)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate

  field
    LatticePoint :
      Set

    ContinuumPoint :
      Set

    DiscreteField :
      Set

    ContinuumField :
      Set

    DiscreteMetric :
      Set

    ContinuumMetric :
      Set

    DiscreteConnection :
      Set

    ContinuumConnection :
      Set

    DiscreteEinsteinTensor :
      Set

    ContinuumEinsteinTensor :
      Set

    latticeEmbedding :
      LatticePoint →
      ContinuumPoint

    continuumFieldLimit :
      DiscreteScale →
      DiscreteField →
      ContinuumField →
      Set

    metricErrorBound :
      Epsilon →
      DiscreteScale →
      DiscreteMetric →
      ContinuumMetric →
      Set

    connectionErrorBound :
      Epsilon →
      DiscreteScale →
      DiscreteConnection →
      ContinuumConnection →
      Set

    einsteinTensorContinuity :
      Epsilon →
      DiscreteScale →
      DiscreteEinsteinTensor →
      ContinuumEinsteinTensor →
      Set

    w2ResolvedRate :
      Epsilon →
      DiscreteScale →
      Set

record ContinuumLimitTheoremCandidate : Setω where
  field
    status :
      ContinuumLimitCandidateStatus

    epsilonRateSurface :
      ContinuumLimitEpsilonRateSurface

    analyticPrimitives :
      ContinuumLimitAnalyticPrimitives epsilonRateSurface →
      Set

    w2ResolutionRole :
      W2ContinuumResolutionRole

    w2Status :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w2BridgeOrObstructionReceipt :
      W2PM.W2CanonicalPressureMetricP2ObstructionReceipt

    p2LimitConvergenceStatus :
      G3P2.G3P2LimitConvergenceStatus

    discreteEinsteinDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    einsteinEquationInterface :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    missingPrimitives :
      List ContinuumLimitMissingPrimitive

    theoremRequest :
      String

    nonPromotionBoundary :
      List String

    w2AuthorityUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    w2PromotionReceiptImpossible :
      W2.NaturalP2ConvergencePromotionReceipt →
      ⊥

canonicalContinuumLimitEpsilonRateSurface :
  ContinuumLimitEpsilonRateSurface
canonicalContinuumLimitEpsilonRateSurface =
  record
    { DiscreteScale =
        Nat
    ; Epsilon =
        Nat
    ; Rate =
        λ ε scale →
          Nat
    ; rateComposesWithW2 =
        w2ResolutionAffectsRateNotExistence
    ; w2RateBoundary =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2BridgeOrObstruction =
        W2PM.canonicalW2PressureMetricP2ObstructionReceipt
    ; rateBoundary =
        "W2 supplies the current bridge-or-obstruction and rate boundary only"
        ∷ "Resolving W2 changes the available convergence rate surface"
        ∷ "The continuum-limit existence request still needs lattice embedding, field convergence, metric and connection error bounds, and Einstein tensor continuity"
        ∷ []
    }

continuumLimitAnalyticPrimitivesRequest :
  ContinuumLimitAnalyticPrimitives
    canonicalContinuumLimitEpsilonRateSurface →
  Set
continuumLimitAnalyticPrimitivesRequest primitives =
  ContinuumLimitAnalyticPrimitives.LatticePoint primitives

canonicalContinuumLimitTheoremCandidate :
  ContinuumLimitTheoremCandidate
canonicalContinuumLimitTheoremCandidate =
  record
    { status =
        theoremRequestOnlyW2RateBlockedNoPromotion
    ; epsilonRateSurface =
        canonicalContinuumLimitEpsilonRateSurface
    ; analyticPrimitives =
        continuumLimitAnalyticPrimitivesRequest
    ; w2ResolutionRole =
        w2ResolutionAffectsRateNotExistence
    ; w2Status =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2BridgeOrObstructionReceipt =
        W2PM.canonicalW2PressureMetricP2ObstructionReceipt
    ; p2LimitConvergenceStatus =
        G3P2.selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion
    ; discreteEinsteinDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; einsteinEquationInterface =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; missingPrimitives =
        missingLatticeEmbedding
        ∷ missingContinuumFieldConvergence
        ∷ missingMetricErrorBound
        ∷ missingConnectionErrorBound
        ∷ missingEinsteinTensorContinuity
        ∷ missingW2BridgeOrObstructionResolution
        ∷ []
    ; theoremRequest =
        "Continuum limit theorem candidate: given latticeEmbedding, continuumFieldConvergence, metricErrorBound, connectionErrorBound, EinsteinTensorContinuity, and a W2 bridge-or-obstruction resolution supplying the needed rate, construct metric/connection/Einstein convergence without promoting W2 or unification here"
    ; nonPromotionBoundary =
        "No W2 authority token is constructed"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed"
        ∷ "W2 resolution is recorded as affecting convergence rate, not theorem existence"
        ∷ "No lattice embedding is constructed"
        ∷ "No continuum field convergence primitive is constructed"
        ∷ "No metricErrorBound, connectionErrorBound, or Einstein tensor continuity theorem is constructed"
        ∷ "No curved GR, Einstein-equation, GR/QFT, or unification promotion receipt is constructed"
        ∷ []
    ; w2AuthorityUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; w2PromotionReceiptImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    }

continuumLimitCandidateExactStatus :
  ContinuumLimitTheoremCandidate.status
    canonicalContinuumLimitTheoremCandidate
  ≡
  theoremRequestOnlyW2RateBlockedNoPromotion
continuumLimitCandidateExactStatus = refl

continuumLimitCandidateW2Role :
  ContinuumLimitTheoremCandidate.w2ResolutionRole
    canonicalContinuumLimitTheoremCandidate
  ≡
  w2ResolutionAffectsRateNotExistence
continuumLimitCandidateW2Role = refl
