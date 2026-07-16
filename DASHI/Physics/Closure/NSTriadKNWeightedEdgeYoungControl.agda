module DASHI.Physics.Closure.NSTriadKNWeightedEdgeYoungControl where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalEdgeTransferOperator as Edge
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Weighted edge Young / Schur-complement control.
--
-- The symbolic scalar interface has no inverse, absolute-value triangle law,
-- or Cauchy--Schwarz theorem.  Those are kept in this authority rather than
-- being silently assumed by either the Fourier or diagnostic Gram lanes.
------------------------------------------------------------------------

record PositiveEdgeWeightAuthority (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    _≤_ : Scalar.Scalar S → Scalar.Scalar S → Set
    abs : Scalar.Scalar S → Scalar.Scalar S
    half : Scalar.Scalar S → Scalar.Scalar S
    inverseWeight : Edge.TriadEdgeField S → Edge.TriadEdgeField S
    weightedNormSq : Edge.TriadEdgeField S → Edge.TriadEdgeField S → Scalar.Scalar S

    -- This is exactly the positive 2-by-2 block/Schur-complement inequality
    -- on one triad edge fibre.  A concrete ordered-field instance must prove
    -- it from W > 0; it is not supplied by the diagnostic Lneg/Labs order.
    weightedEdgeYoung :
      (dz dT : Edge.TriadEdgeField S) →
      _≤_ (abs (Edge.edgePairing S dz dT))
        (half (Scalar._+_ S
          (weightedNormSq dz dz)
          (weightedNormSq (inverseWeight dT) dT)))

open PositiveEdgeWeightAuthority public

edgeWeightedMultiplierQuadratic :
  (S : Scalar.ExactOrderedScalar) →
  PositiveEdgeWeightAuthority S →
  Edge.TriadEdgeField S → Scalar.Scalar S
edgeWeightedMultiplierQuadratic S W dz = weightedNormSq W dz dz

edgeTransferFluxDualNorm :
  (S : Scalar.ExactOrderedScalar) →
  PositiveEdgeWeightAuthority S →
  Edge.TriadEdgeField S → Scalar.Scalar S
edgeTransferFluxDualNorm S W dT =
  weightedNormSq W (inverseWeight W dT) dT

physicalWeightedErrorTriadYoung :
  (S : Scalar.ExactOrderedScalar) → (W : PositiveEdgeWeightAuthority S) →
  (M : Nat) → (z : Energy.AdmissibleFourierMultiplier S M) →
  (T : Energy.ZeroSumTriadTransferField S) → (σ : Energy.ZeroSumTriad) →
  _≤_ W
    (abs W (Edge.edgePairing S
      (Edge.multiplierEdgeDifference S M z σ)
      (Edge.modalTransferEdgeDifference S T σ)))
    (half W (Scalar._+_ S
      (edgeWeightedMultiplierQuadratic S W
        (Edge.multiplierEdgeDifference S M z σ))
      (edgeTransferFluxDualNorm S W
        (Edge.modalTransferEdgeDifference S T σ)))
physicalWeightedErrorTriadYoung S W M z T σ =
  weightedEdgeYoung W
    (Edge.multiplierEdgeDifference S M z σ)
    (Edge.modalTransferEdgeDifference S T σ)

