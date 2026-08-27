module DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact where

------------------------------------------------------------------------
-- ROUND112 / ACTUAL EXTERNAL WALEFFE FUNCTIONAL ON THREE RESIDUAL FIBRES
--
-- Round111 identifies the k-slot external Galerkin forcing with the literal
-- output fibre after deleting the selected self swap-orbit.  Apply that theorem
-- cyclically to tau, pEnergyLeg tau and qEnergyLeg tau.  The result is the
-- actual Round94 Waleffe network forcing evaluated on three explicit residual
-- convolution vectors.
--
-- This closes the carrier/functional bookkeeping seam:
--
--   F_ext(tau)
--     = networkForcing(u_k,u_p,u_q,
--         sum R_k, sum R_p, sum R_q).
--
-- It does NOT identify this trilinear Waleffe functional with the old odd-P/Q
-- commutator functional.  That conversion, if valid after the critical packet
-- weighting/reindexing, is the next exact theorem to prove.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong₃; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as Residual

record ThreeLegResidualMembership
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    kMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)
    kSwapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau)
    kSwapDifferent : Symmetry.swapTriad tau ≢ tau

    pMember : Orbit.pEnergyLeg tau ∈
      Audit.concreteTriadsAt system (Physical.p tau)
    pSwapMember : Symmetry.swapTriad (Orbit.pEnergyLeg tau) ∈
      Audit.concreteTriadsAt system (Physical.p tau)
    pSwapDifferent :
      Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau

    qMember : Orbit.qEnergyLeg tau ∈
      Audit.concreteTriadsAt system (Physical.q tau)
    qSwapMember : Symmetry.swapTriad (Orbit.qEnergyLeg tau) ∈
      Audit.concreteTriadsAt system (Physical.q tau)
    qSwapDifferent :
      Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau

open ThreeLegResidualMembership public

externalResidualK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegResidualMembership system tau → C3.Complex3 F
externalResidualK system tau M =
  Residual.externalResidualVector system tau
    (kMember M) (kSwapMember M) (kSwapDifferent M)

externalResidualP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegResidualMembership system tau → C3.Complex3 F
externalResidualP system tau M =
  Residual.externalResidualVector system (Orbit.pEnergyLeg tau)
    (pMember M) (pSwapMember M) (pSwapDifferent M)

externalResidualQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegResidualMembership system tau → C3.Complex3 F
externalResidualQ system tau M =
  Residual.externalResidualVector system (Orbit.qEnergyLeg tau)
    (qMember M) (qSwapMember M) (qSwapDifferent M)

externalForcingPAsKOfPEnergyLeg :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingP system tau
  ≡ Split.externalForcingK system (Orbit.pEnergyLeg tau)
externalForcingPAsKOfPEnergyLeg system tau = refl

externalForcingQAsKOfQEnergyLeg :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.externalForcingQ system tau
  ≡ Split.externalForcingK system (Orbit.qEnergyLeg tau)
externalForcingQAsKOfQEnergyLeg system tau = refl

externalForcingKIsResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (M : ThreeLegResidualMembership system tau) →
  Split.externalForcingK system tau ≡ externalResidualK system tau M
externalForcingKIsResidual system tau M =
  Residual.externalForcingKIsSelfOrbitRemovedOutputFibre system tau
    (kMember M) (kSwapMember M) (kSwapDifferent M)

externalForcingPIsResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (M : ThreeLegResidualMembership system tau) →
  Split.externalForcingP system tau ≡ externalResidualP system tau M
externalForcingPIsResidual system tau M =
  trans
    (externalForcingPAsKOfPEnergyLeg system tau)
    (Residual.externalForcingKIsSelfOrbitRemovedOutputFibre
      system (Orbit.pEnergyLeg tau)
      (pMember M) (pSwapMember M) (pSwapDifferent M))

externalForcingQIsResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (M : ThreeLegResidualMembership system tau) →
  Split.externalForcingQ system tau ≡ externalResidualQ system tau M
externalForcingQIsResidual system tau M =
  trans
    (externalForcingQAsKOfQEnergyLeg system tau)
    (Residual.externalForcingKIsSelfOrbitRemovedOutputFibre
      system (Orbit.qEnergyLeg tau)
      (qMember M) (qSwapMember M) (qSwapDifferent M))

externalResidualNetworkForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegResidualMembership system tau → C3.Complex F
externalResidualNetworkForcing system tau M =
  Tangent.networkForcing
    (Audit.velocity system (Physical.k tau))
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (externalResidualK system tau M)
    (externalResidualP system tau M)
    (externalResidualQ system tau M)

externalAmplitudeForcingIsResidualNetworkForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (M : ThreeLegResidualMembership system tau) →
  Split.externalAmplitudeForcing system tau
  ≡ externalResidualNetworkForcing system tau M
externalAmplitudeForcingIsResidualNetworkForcing system tau M =
  cong₃
    (Tangent.networkForcing
      (Audit.velocity system (Physical.k tau))
      (Audit.velocity system (Physical.p tau))
      (Audit.velocity system (Physical.q tau)))
    (externalForcingKIsResidual system tau M)
    (externalForcingPIsResidual system tau M)
    (externalForcingQIsResidual system tau M)

round112ExternalWaleffeFunctionalOnResidualCarriersClosed : Bool
round112ExternalWaleffeFunctionalOnResidualCarriersClosed = true

round112ExternalWaleffeFunctionalAlreadyEqualsOddPQCommutator : Bool
round112ExternalWaleffeFunctionalAlreadyEqualsOddPQCommutator = false

round112ExternalWaleffeFunctionalOnResidualCarriersClosedIsTrue :
  round112ExternalWaleffeFunctionalOnResidualCarriersClosed ≡ true
round112ExternalWaleffeFunctionalOnResidualCarriersClosedIsTrue = refl

round112ExternalWaleffeFunctionalAlreadyEqualsOddPQCommutatorIsFalse :
  round112ExternalWaleffeFunctionalAlreadyEqualsOddPQCommutator ≡ false
round112ExternalWaleffeFunctionalAlreadyEqualsOddPQCommutatorIsFalse = refl
