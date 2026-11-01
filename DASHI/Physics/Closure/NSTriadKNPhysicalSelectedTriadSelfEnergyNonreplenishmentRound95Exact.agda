module DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadSelfEnergyNonreplenishmentRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND95 / LITERAL SELF-TRIAD NONREPLENISHMENT
--
-- Round95 split the actual Galerkin forcing at the three legs of one physical
-- triad into the selected triad's own ordered-pair interaction and an external
-- remainder.  This file identifies the three self energy pairings with the
-- repository's already-proved exact ordered-pair transfer orbit and invokes
-- the literal resonance/reality/divergence-free cancellation theorem.
--
-- Therefore, on the ACTUAL Complex3 Fourier carrier,
--
--   T_k^self + T_p^self + T_q^self = 0.
--
-- This is the same-object statement needed by the replenishment recut: an
-- internally interacting triad redistributes energy among its three legs but
-- cannot replenish their total.  Any sustained increase of the selected
-- three-leg energy must come from the external network remainder (before
-- viscosity, which is separately dissipative).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split

selfEnergyTransferAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selfEnergyTransferAt {F = F} {E = E} {I = I} system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.k tau))
      (Split.selfForcingForIncidence system tau))

selfEnergyTransferIsOrderedPairTransfer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  selfEnergyTransferAt system tau
  ≡ Audit.orderedPairSignedTransferAt E I tau (Galerkin.velocityAt system)
selfEnergyTransferIsOrderedPairTransfer system tau = refl

selectedTriadSelfEnergyPower :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selectedTriadSelfEnergyPower {F = F} system tau =
  C3.complexAdd
    (C3.complexAdd
      (selfEnergyTransferAt system tau)
      (selfEnergyTransferAt system (Orbit.pEnergyLeg tau)))
    (selfEnergyTransferAt system (Orbit.qEnergyLeg tau))

selectedTriadSelfEnergyPowerIsLiteralOrbitPower :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  selectedTriadSelfEnergyPower system tau
  ≡
  C3.complexAdd
    (C3.complexAdd
      (Audit.orderedPairSignedTransferAt E I tau (Galerkin.velocityAt system))
      (Audit.orderedPairSignedTransferAt E I
        (Orbit.pEnergyLeg tau) (Galerkin.velocityAt system)))
    (Audit.orderedPairSignedTransferAt E I
      (Orbit.qEnergyLeg tau) (Galerkin.velocityAt system))
selectedTriadSelfEnergyPowerIsLiteralOrbitPower system tau =
  cong₂ C3.complexAdd
    (cong₂ C3.complexAdd
      (selfEnergyTransferIsOrderedPairTransfer system tau)
      (selfEnergyTransferIsOrderedPairTransfer system (Orbit.pEnergyLeg tau)))
    (selfEnergyTransferIsOrderedPairTransfer system (Orbit.qEnergyLeg tau))

selectedTriadSelfEnergyCannotReplenish :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.RealityCondition (Galerkin.velocityAt system) →
  Audit.DivergenceFreeCondition E (Galerkin.velocityAt system) →
  selectedTriadSelfEnergyPower system tau ≡ C3.complexZero F
selectedTriadSelfEnergyCannotReplenish {E = E} {I = I}
    system tau reality divergenceFree =
  trans
    (selectedTriadSelfEnergyPowerIsLiteralOrbitPower system tau)
    (Audit.completeTriadCancellation
      (Energy.exactTriadEnergyCancellation E I tau)
      (Galerkin.velocityAt system) reality divergenceFree)

round95LiteralSelectedTriadSelfEnergyNonreplenishmentClosed : Bool
round95LiteralSelectedTriadSelfEnergyNonreplenishmentClosed = true

round95OnlyExternalNetworkCanReplenishSelectedTriadTotal : Bool
round95OnlyExternalNetworkCanReplenishSelectedTriadTotal = true

round95LiteralSelectedTriadSelfEnergyNonreplenishmentClosedIsTrue :
  round95LiteralSelectedTriadSelfEnergyNonreplenishmentClosed ≡ true
round95LiteralSelectedTriadSelfEnergyNonreplenishmentClosedIsTrue = refl

round95OnlyExternalNetworkCanReplenishSelectedTriadTotalIsTrue :
  round95OnlyExternalNetworkCanReplenishSelectedTriadTotal ≡ true
round95OnlyExternalNetworkCanReplenishSelectedTriadTotalIsTrue = refl
