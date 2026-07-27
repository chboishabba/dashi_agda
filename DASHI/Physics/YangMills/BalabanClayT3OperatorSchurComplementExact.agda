module DASHI.Physics.YangMills.BalabanClayT3OperatorSchurComplementExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3

------------------------------------------------------------------------
-- Exact operator Schur algebra.
--
-- E. V. Haynsworth,
-- "Determination of the inertia of a partitioned Hermitian matrix",
-- Linear Algebra and its Applications 1 (1968), 73--81.
-- DOI: 10.1016/0024-3795(68)90050-5
--
-- This module proves the algebraic identity
--
--   H_eff = H_cc - H_cf H_ff^{-1} H_fc.
--
-- That identity is not the difficult Balaban theorem.  The physical content is
-- a positive constant c_f, uniform in blocking scale, lattice spacing, volume
-- and patch regime, such that
--
--   c_f ||h||^2 <= <h , H_ff h>
--
-- after the prescribed gauge modes are removed.  The reduction from reference
-- coercivity plus a relative perturbation bound is implemented separately in
-- BalabanClayT3UniformFluctuationSchurExact.
------------------------------------------------------------------------

record OperatorSchurData (Coarse Fluctuation Bound : Set) : Set₁ where
  field
    coarseHessian : Coarse → Coarse
    mixedHessian : Coarse → Fluctuation
    mixedAdjoint : Fluctuation → Coarse
    fluctuationHessian fluctuationGreen : Fluctuation → Fluctuation

    subtractCoarse : Coarse → Coarse → Coarse
    subtractBound : Bound → Bound → Bound
    coarseInner : Coarse → Coarse → Bound
    fluctuationInner : Fluctuation → Fluctuation → Bound

    fluctuationInverseLeft : ∀ fluctuation →
      fluctuationGreen (fluctuationHessian fluctuation) ≡ fluctuation
    fluctuationInverseRight : ∀ fluctuation →
      fluctuationHessian (fluctuationGreen fluctuation) ≡ fluctuation

    coarseInnerSubtract : ∀ coarse left right →
      coarseInner coarse (subtractCoarse left right)
      ≡ subtractBound (coarseInner coarse left) (coarseInner coarse right)

    mixedAdjointExact : ∀ coarse fluctuation →
      coarseInner coarse (mixedAdjoint fluctuation)
      ≡ fluctuationInner (mixedHessian coarse) fluctuation

    FluctuationCoercive : Set
    fluctuationCoercive : FluctuationCoercive

    GaugeCovariant : (Coarse → Coarse) → Set
    KernelExactlyPrescribedGaugeModes : Set
    NextScaleNormalizationMatches : Set

    schurGaugeCovariantProof :
      GaugeCovariant
        (λ coarse → subtractCoarse (coarseHessian coarse)
          (mixedAdjoint (fluctuationGreen (mixedHessian coarse))))
    kernelExactlyPrescribedGaugeModes : KernelExactlyPrescribedGaugeModes
    nextScaleNormalizationMatches : NextScaleNormalizationMatches

open OperatorSchurData public

schurHessian :
  ∀ {Coarse Fluctuation Bound} →
  OperatorSchurData Coarse Fluctuation Bound → Coarse → Coarse
schurHessian dataSet coarse =
  subtractCoarse dataSet (coarseHessian dataSet coarse)
    (mixedAdjoint dataSet
      (fluctuationGreen dataSet (mixedHessian dataSet coarse)))

operatorSchurEnergyExact :
  ∀ {Coarse Fluctuation Bound}
    (dataSet : OperatorSchurData Coarse Fluctuation Bound)
    coarse →
  coarseInner dataSet coarse (schurHessian dataSet coarse)
  ≡ subtractBound dataSet
      (coarseInner dataSet coarse (coarseHessian dataSet coarse))
      (fluctuationInner dataSet
        (mixedHessian dataSet coarse)
        (fluctuationGreen dataSet (mixedHessian dataSet coarse)))
operatorSchurEnergyExact dataSet coarse =
  trans
    (coarseInnerSubtract dataSet coarse
      (coarseHessian dataSet coarse)
      (mixedAdjoint dataSet
        (fluctuationGreen dataSet (mixedHessian dataSet coarse))))
    (let
      mixedTerm = fluctuationGreen dataSet (mixedHessian dataSet coarse)
     in
      cong
        (subtractBound dataSet
          (coarseInner dataSet coarse (coarseHessian dataSet coarse)))
        (mixedAdjointExact dataSet coarse mixedTerm))

operatorExactSchurComplement :
  ∀ {Coarse Fluctuation Bound} →
  (dataSet : OperatorSchurData Coarse Fluctuation Bound) →
  P3.ExactSchurComplement Coarse Fluctuation Bound
operatorExactSchurComplement dataSet = record
  { P3.ExactSchurComplement.coarseHessian = coarseHessian dataSet
  ; P3.ExactSchurComplement.mixedHessian = mixedHessian dataSet
  ; P3.ExactSchurComplement.fluctuationHessian = fluctuationHessian dataSet
  ; P3.ExactSchurComplement.fluctuationGreen = fluctuationGreen dataSet
  ; P3.ExactSchurComplement.schurHessian = schurHessian dataSet
  ; P3.ExactSchurComplement.coarseInner = coarseInner dataSet
  ; P3.ExactSchurComplement.fluctuationInner = fluctuationInner dataSet
  ; P3.ExactSchurComplement.subtract = subtractBound dataSet
  ; P3.ExactSchurComplement.fluctuationInverseLeft =
      fluctuationInverseLeft dataSet
  ; P3.ExactSchurComplement.fluctuationInverseRight =
      fluctuationInverseRight dataSet
  ; P3.ExactSchurComplement.schurEnergyExact =
      operatorSchurEnergyExact dataSet
  ; P3.ExactSchurComplement.FluctuationCoercive =
      FluctuationCoercive dataSet
  ; P3.ExactSchurComplement.fluctuationCoercive =
      fluctuationCoercive dataSet
  ; P3.ExactSchurComplement.GaugeCovariant = GaugeCovariant dataSet
  ; P3.ExactSchurComplement.schurGaugeCovariant =
      schurGaugeCovariantProof dataSet
  ; P3.ExactSchurComplement.KernelExactlyPrescribedGaugeModes =
      KernelExactlyPrescribedGaugeModes dataSet
  ; P3.ExactSchurComplement.kernelExactlyPrescribedGaugeModes =
      kernelExactlyPrescribedGaugeModes dataSet
  ; P3.ExactSchurComplement.NextScaleNormalizationMatches =
      NextScaleNormalizationMatches dataSet
  ; P3.ExactSchurComplement.nextScaleNormalizationMatches =
      nextScaleNormalizationMatches dataSet
  }

operatorSchurEnergyIdentityLevel : ProofLevel
operatorSchurEnergyIdentityLevel = machineChecked

operatorSchurP3AdapterLevel : ProofLevel
operatorSchurP3AdapterLevel = machineChecked

operatorSchurAlgebraVersusCoercivityBoundaryLevel : ProofLevel
operatorSchurAlgebraVersusCoercivityBoundaryLevel = machineChecked

physicalFluctuationSchurInputsLevel : ProofLevel
physicalFluctuationSchurInputsLevel = conditional
