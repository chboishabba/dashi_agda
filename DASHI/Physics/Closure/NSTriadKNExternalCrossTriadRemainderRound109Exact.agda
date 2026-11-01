module DASHI.Physics.Closure.NSTriadKNExternalCrossTriadRemainderRound109Exact where

------------------------------------------------------------------------
-- ROUND109 / LITERAL EXTERNAL CROSS-TRIAD REMAINDER
--
-- Round95 already defines, on one selected physical triad, the full projected
-- Galerkin forcing and the selected self forcing.  The external forcing is the
-- SAME-OBJECT residual
--
--   N_ext = N_full - N_self.
--
-- This module unfolds that statement all the way to the literal output-fiber
-- convolution sum and proves the corresponding amplitude-forcing residual
-- identity
--
--   F_ext = F_full - F_self.
--
-- Thus the next analytic theorem is not about an arbitrary quartic forcing:
-- it is about the cross-triad remainder of the exact output-fiber convolution
-- after one explicit Waleffe self channel has been removed.
--
-- Separately, Round95 already proves that the three-leg ENERGY replenishment
-- of the selected triad is exactly its external-network replenishment because
-- the selected self orbit has zero net energy transfer.  We reuse that physical
-- same-object theorem here; we do not infer that the PHASE self term vanishes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadExternalReplenishmentIdentityRound95Exact as Replenish

externalForcingKIsLiteralOutputFiberResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingK system tau
  ≡ C3.complex3Subtract
      (Galerkin.sumVectors
        (Galerkin.mapTriadTerms system
          (Galerkin.concreteTriadsAt system (Physical.k tau))))
      (Split.selfForcingK system tau)
externalForcingKIsLiteralOutputFiberResidual system tau = refl

externalForcingPIsLiteralOutputFiberResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingP system tau
  ≡ C3.complex3Subtract
      (Galerkin.sumVectors
        (Galerkin.mapTriadTerms system
          (Galerkin.concreteTriadsAt system (Physical.p tau))))
      (Split.selfForcingP system tau)
externalForcingPIsLiteralOutputFiberResidual system tau = refl

externalForcingQIsLiteralOutputFiberResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingQ system tau
  ≡ C3.complex3Subtract
      (Galerkin.sumVectors
        (Galerkin.mapTriadTerms system
          (Galerkin.concreteTriadsAt system (Physical.q tau))))
      (Split.selfForcingQ system tau)
externalForcingQIsLiteralOutputFiberResidual system tau = refl

externalAmplitudeForcingIsFullMinusSelf :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalAmplitudeForcing system tau
  ≡ C3.complexSubtract
      (Split.fullAmplitudeForcing system tau)
      (Split.selfAmplitudeForcing system tau)
externalAmplitudeForcingIsFullMinusSelf {F = F} system tau =
  sym
    (trans
      (cong
        (λ full → C3.complexSubtract full (Split.selfAmplitudeForcing system tau))
        (Split.fullAmplitudeForcingSplitsExactly system tau))
      (R.solve 2
        (λ self external →
          ((self R.⊕ external) R.⊕ (R.⊝ self)) R.⊜ external)
        refl
        (Split.selfAmplitudeForcing system tau)
        (Split.externalAmplitudeForcing system tau)))
  where module R = Ring.Solver F

selectedTriadFullEnergyReplenishmentIsExternalNetwork :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Reality.RealityCondition (Galerkin.velocityAt system) →
  Reality.DivergenceFreeCondition E (Galerkin.velocityAt system) →
  Replenish.totalFullPower system tau ≡ Replenish.totalExternalPower system tau
selectedTriadFullEnergyReplenishmentIsExternalNetwork =
  Replenish.fullThreeLegReplenishmentIsExternalNetwork

round109LiteralExternalOutputFiberResidualClosed : Bool
round109LiteralExternalOutputFiberResidualClosed = true

round109ExternalAmplitudeForcingResidualClosed : Bool
round109ExternalAmplitudeForcingResidualClosed = true

round109SelectedTriadEnergyReplenishmentIsExternalClosed : Bool
round109SelectedTriadEnergyReplenishmentIsExternalClosed =
  Replenish.round95FullThreeLegReplenishmentEqualsExternalNetwork

-- Analytic payment of this literal cross-triad residual is the live physical
-- discovery step.  This module only identifies the exact finite object.
round109PhysicalExternalCrossTriadRemainderPaymentClosed : Bool
round109PhysicalExternalCrossTriadRemainderPaymentClosed = false

round109LiteralExternalOutputFiberResidualClosedIsTrue :
  round109LiteralExternalOutputFiberResidualClosed ≡ true
round109LiteralExternalOutputFiberResidualClosedIsTrue = refl

round109ExternalAmplitudeForcingResidualClosedIsTrue :
  round109ExternalAmplitudeForcingResidualClosed ≡ true
round109ExternalAmplitudeForcingResidualClosedIsTrue = refl

round109SelectedTriadEnergyReplenishmentIsExternalClosedIsTrue :
  round109SelectedTriadEnergyReplenishmentIsExternalClosed ≡ true
round109SelectedTriadEnergyReplenishmentIsExternalClosedIsTrue = refl

round109PhysicalExternalCrossTriadRemainderPaymentClosedIsFalse :
  round109PhysicalExternalCrossTriadRemainderPaymentClosed ≡ false
round109PhysicalExternalCrossTriadRemainderPaymentClosedIsFalse = refl
