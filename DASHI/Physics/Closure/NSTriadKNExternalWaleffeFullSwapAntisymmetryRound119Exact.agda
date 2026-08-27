module DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact where

------------------------------------------------------------------------
-- ROUND119 / FULL THREE-SLOT EXTERNAL WALEFFE SWAP ANTISYMMETRY
--
-- Round118 proves the K-slot quartic cell changes sign when the SELECTED
-- incidence is swapped.  The same fact holds for the complete three-slot
-- external Waleffe amplitude forcing once the P/Q forcing slots are exchanged
-- with the selected inputs.
--
--   tau=(p,q->k) |-> swap(tau)=(q,p->k),
--
--   extK(swap tau) = extK(tau),
--   extP(swap tau) = extQ(tau),
--   extQ(swap tau) = extP(tau),
--
-- hence
--
--   F_ext(swap tau) = - F_ext(tau).
--
-- This signed cancellation is only exploitable by a consumer that preserves
-- the complete swap orbit until after summation.  A per-cell positive part does
-- not cancel with the positive part of its negative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as Residual
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118

complex3AddCommutative :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.complex3Add u v ≡ C3.complex3Add v u
complex3AddCommutative
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (Algebra.complexAddCommutative ux vx)
    (Algebra.complexAddCommutative uy vy)
    (Algebra.complexAddCommutative uz vz)

pEnergyLegSwapIsQEnergyLeg :
  (tau : Physical.PhysicalTriadIncidence) →
  Orbit.pEnergyLeg (Symmetry.swapTriad tau) ≡ Orbit.qEnergyLeg tau
pEnergyLegSwapIsQEnergyLeg tau =
  KFree.physicalIncidenceExtPQ
    (Orbit.pEnergyLeg (Symmetry.swapTriad tau))
    (Orbit.qEnergyLeg tau)
    refl refl

qEnergyLegSwapIsPEnergyLeg :
  (tau : Physical.PhysicalTriadIncidence) →
  Orbit.qEnergyLeg (Symmetry.swapTriad tau) ≡ Orbit.pEnergyLeg tau
qEnergyLegSwapIsPEnergyLeg tau =
  KFree.physicalIncidenceExtPQ
    (Orbit.qEnergyLeg (Symmetry.swapTriad tau))
    (Orbit.pEnergyLeg tau)
    refl refl

selfForcingKSwapInvariant :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.selfForcingK system (Symmetry.swapTriad tau)
  ≡ Split.selfForcingK system tau
selfForcingKSwapInvariant system tau =
  let
    first = Audit.projectedOrderedTerm system tau
    second = Audit.projectedOrderedTerm system (Symmetry.swapTriad tau)
  in
  trans
    (Residual.selfForcingKIsTwoSelectedOrderedTerms
      system (Symmetry.swapTriad tau))
    (trans
      (cong
        (C3.complex3Add second)
        (cong (Audit.projectedOrderedTerm system)
          (Round38.swapTriadInvolutiveExact tau)))
      (trans
        (complex3AddCommutative second first)
        (sym (Residual.selfForcingKIsTwoSelectedOrderedTerms system tau))))

selfForcingPSwapIsQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.selfForcingP system (Symmetry.swapTriad tau)
  ≡ Split.selfForcingQ system tau
selfForcingPSwapIsQ system tau =
  cong (Split.selfForcingForIncidence system)
    (pEnergyLegSwapIsQEnergyLeg tau)

selfForcingQSwapIsP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.selfForcingQ system (Symmetry.swapTriad tau)
  ≡ Split.selfForcingP system tau
selfForcingQSwapIsP system tau =
  cong (Split.selfForcingForIncidence system)
    (qEnergyLegSwapIsPEnergyLeg tau)

externalForcingKSwapInvariant :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingK system (Symmetry.swapTriad tau)
  ≡ Split.externalForcingK system tau
externalForcingKSwapInvariant system tau =
  cong₂ C3.complex3Subtract refl (selfForcingKSwapInvariant system tau)

externalForcingPSwapIsQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingP system (Symmetry.swapTriad tau)
  ≡ Split.externalForcingQ system tau
externalForcingPSwapIsQ system tau =
  cong₂ C3.complex3Subtract refl (selfForcingPSwapIsQ system tau)

externalForcingQSwapIsP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingQ system (Symmetry.swapTriad tau)
  ≡ Split.externalForcingP system tau
externalForcingQSwapIsP system tau =
  cong₂ C3.complex3Subtract refl (selfForcingQSwapIsP system tau)

networkForcingSwapPQIsNegative :
  ∀ {r} {F : C3.RealField r}
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  Tangent.networkForcing uK uQ uP fK fQ fP
  ≡ C3.complexNegate
      (Tangent.networkForcing uK uP uQ fK fP fQ)
networkForcingSwapPQIsNegative {F = F} uK uP uQ fK fP fQ =
  let
    A = C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)
    B = C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ)
    C = C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)
  in
  trans
    (cong₂ C3.complexAdd
      (cong₂ C3.complexAdd
        (trans
          (cong (C3.hermitianPairing3 fK)
            (R118.crossAnticommutative uP uQ))
          (Additive.hermitianPairingNegateRight fK
            (Cross.complex3Cross uP uQ)))
        (trans
          (cong (C3.hermitianPairing3 uK)
            (R118.crossAnticommutative uP fQ))
          (Additive.hermitianPairingNegateRight uK
            (Cross.complex3Cross uP fQ))))
      (trans
        (cong (C3.hermitianPairing3 uK)
          (R118.crossAnticommutative fP uQ))
        (Additive.hermitianPairingNegateRight uK
          (Cross.complex3Cross fP uQ))))
    (R.solve 3
      (λ A B C →
        ((R.⊝ A) R.⊕ (R.⊝ C)) R.⊕ (R.⊝ B)
        R.⊜ R.⊝ ((A R.⊕ B) R.⊕ C))
      refl A B C)
  where module R = Ring.Solver F

externalAmplitudeForcingSwapIsNegative :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalAmplitudeForcing system (Symmetry.swapTriad tau)
  ≡ C3.complexNegate (Split.externalAmplitudeForcing system tau)
externalAmplitudeForcingSwapIsNegative system tau
  rewrite externalForcingKSwapInvariant system tau
        | externalForcingPSwapIsQ system tau
        | externalForcingQSwapIsP system tau =
  networkForcingSwapPQIsNegative
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (Split.externalForcingK system tau)
    (Split.externalForcingP system tau)
    (Split.externalForcingQ system tau)

round119ExternalModeForcingSwapCovarianceClosed : Bool
round119ExternalModeForcingSwapCovarianceClosed = true

round119FullExternalWaleffeSwapAntisymmetryClosed : Bool
round119FullExternalWaleffeSwapAntisymmetryClosed = true

round119SignedSwapCancellationCanPrecedePositivePart : Bool
round119SignedSwapCancellationCanPrecedePositivePart = true

round119AdversePerCellPositivePartCancelsBySwap : Bool
round119AdversePerCellPositivePartCancelsBySwap = false

round119ExternalModeForcingSwapCovarianceClosedIsTrue :
  round119ExternalModeForcingSwapCovarianceClosed ≡ true
round119ExternalModeForcingSwapCovarianceClosedIsTrue = refl

round119FullExternalWaleffeSwapAntisymmetryClosedIsTrue :
  round119FullExternalWaleffeSwapAntisymmetryClosed ≡ true
round119FullExternalWaleffeSwapAntisymmetryClosedIsTrue = refl

round119SignedSwapCancellationCanPrecedePositivePartIsTrue :
  round119SignedSwapCancellationCanPrecedePositivePart ≡ true
round119SignedSwapCancellationCanPrecedePositivePartIsTrue = refl

round119AdversePerCellPositivePartCancelsBySwapIsFalse :
  round119AdversePerCellPositivePartCancelsBySwap ≡ false
round119AdversePerCellPositivePartCancelsBySwapIsFalse = refl
