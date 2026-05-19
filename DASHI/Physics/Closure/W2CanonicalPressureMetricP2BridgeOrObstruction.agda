module DASHI.Physics.Closure.W2CanonicalPressureMetricP2BridgeOrObstruction where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_,_)

import DASHI.Physics.Closure.CanonicalDynamicsLawTheorem as CDT
import DASHI.Physics.Closure.CanonicalP2OfflineL2ObstructionCertificate as CPOL2
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI

------------------------------------------------------------------------
-- W2 / P2 bridge-or-obstruction decision.
--
-- The candidate family is intentionally the explicit offline-L2 admissible
-- family narrowed by the landed certificate.  It says that a Nat -> Nat bridge
-- from the canonical pressure scalar to the realization-indexed metric scalar
-- is admissible only if it also supplies the below-delta normalized-shadow
-- p2-key forcing bridge.  The certificate proves that no such admissible
-- candidate exists.

canonicalPressureScalar : Nat
canonicalPressureScalar =
  PGFSI.shiftFlowPotential SPTI.shiftStartPoint

realizationIndexedMetricScalar : Nat
realizationIndexedMetricScalar =
  CDT.realizedShiftFlowDistanceToFixedPoint (zero , SPTI.shiftStartPoint)

record ExplicitP2AdmissibleCandidate
  (β : Nat → Nat)
  : Setω where
  field
    sourceScalar :
      canonicalPressureScalar ≡ canonicalPressureScalar

    targetScalar :
      realizationIndexedMetricScalar ≡ realizationIndexedMetricScalar

    landsAtMetricScalar :
      β canonicalPressureScalar ≡ realizationIndexedMetricScalar

    belowδForcesP2Key :
      CPOL2.OfflineL2P2BridgeCandidate
        CPOL2.normalizedShadowBelowδ_p2

canonicalCandidateFamily : (Nat → Nat) → Setω
canonicalCandidateFamily =
  ExplicitP2AdmissibleCandidate

canonicalCandidateFamilyImpossible :
  (β : Nat → Nat) →
  canonicalCandidateFamily β →
  ⊥
canonicalCandidateFamilyImpossible β candidate =
  CPOL2.CanonicalP2OfflineL2ObstructionCertificate.allBelowδCandidatesImpossible
    CPOL2.canonicalP2OfflineL2ObstructionCertificate
    (ExplicitP2AdmissibleCandidate.belowδForcesP2Key candidate)

record P2Obstructionω
  {A B : Set}
  (Candidate : (A → B) → Setω)
  : Setω where
  field
    canonVal : A
    targetVal : B

    noBridge :
      ∀ β → Candidate β → β canonVal P0.≢ targetVal

data P2BridgeOrObstructionω
  {A B : Set}
  (Candidate : (A → B) → Setω)
  : Setω where
  positiveω :
    P0.P2Bridge {A} {B} →
    P2BridgeOrObstructionω Candidate
  obstructedω :
    P2Obstructionω {A} {B} Candidate →
    P2BridgeOrObstructionω Candidate

canonicalPressureMetricP2Obstruction :
  P2Obstructionω {Nat} {Nat} canonicalCandidateFamily
canonicalPressureMetricP2Obstruction =
  record
    { canonVal =
        canonicalPressureScalar
    ; targetVal =
        realizationIndexedMetricScalar
    ; noBridge =
        λ β candidate _ →
          canonicalCandidateFamilyImpossible β candidate
    }

W2KillEvidence :
  P2BridgeOrObstructionω {Nat} {Nat} canonicalCandidateFamily
W2KillEvidence =
  obstructedω canonicalPressureMetricP2Obstruction

record W2CanonicalPressureMetricP2ObstructionReceipt : Setω where
  field
    bridgeOrObstruction :
      P2BridgeOrObstructionω {Nat} {Nat} canonicalCandidateFamily

    canonicalDynamicsLaw :
      CDT.CanonicalDynamicsLawTheorem

    realizationMetricFamily :
      CDT.RealizationIndexedPointedMetricConvergenceTarget

    offlineL2Certificate :
      CPOL2.CanonicalP2OfflineL2ObstructionCertificate

    candidateFamilyEmpty :
      (β : Nat → Nat) →
      canonicalCandidateFamily β →
      ⊥

    promotionAuthorityUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    promotionReceiptImpossible :
      W2.NaturalP2ConvergencePromotionReceipt →
      ⊥

    status : String
    boundary : List String

canonicalW2PressureMetricP2ObstructionReceipt :
  W2CanonicalPressureMetricP2ObstructionReceipt
canonicalW2PressureMetricP2ObstructionReceipt =
  record
    { bridgeOrObstruction =
        W2KillEvidence
    ; canonicalDynamicsLaw =
        CDT.canonicalDynamicsLawTheorem
    ; realizationMetricFamily =
        CDT.CanonicalDynamicsLawTheorem.realizationMetricConvergenceFamily
          CDT.canonicalDynamicsLawTheorem
    ; offlineL2Certificate =
        CPOL2.canonicalP2OfflineL2ObstructionCertificate
    ; candidateFamilyEmpty =
        canonicalCandidateFamilyImpossible
    ; promotionAuthorityUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; promotionReceiptImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    ; status =
        "obstruction"
    ; boundary =
        "W2KillEvidence is a bridge-or-obstruction decision over the explicit offline-L2 admissible Nat-to-Nat candidate family"
        ∷ "The result is obstructed because every admissible candidate must provide the below-delta p2-key forcing bridge rejected by CanonicalP2OfflineL2ObstructionCertificate"
        ∷ "The realization-indexed metric family is consumed as landed CW2 structure, not promoted to carrier-general convergence"
        ∷ "NaturalP2ConvergencePromotionAuthorityToken remains constructorless"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed here"
        ∷ []
    }
