module DASHI.Physics.YangMills.YMMassGapRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanSU2GeometryQ0Bundle
import DASHI.Physics.YangMills.BalabanFiniteOneStepFrontierBundle
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SUNLane
open import DASHI.Physics.YangMills.YMMassGapTarget
open import DASHI.Physics.YangMills.LatticeYangMills
open import DASHI.Physics.YangMills.BalabanRGLane
open import DASHI.Physics.YangMills.OSAxiomBundle
open import DASHI.Physics.YangMills.WightmanReconstructionLane
open import DASHI.Physics.YangMills.MassGapSpectralStatement
open import DASHI.Physics.YangMills.O4RestorationLane

------------------------------------------------------------------------
-- Authoritative route composition.
--
-- The route now consumes the 2026 operator/domain frontier explicitly.  This
-- prevents historical source-intake or finite-carrier closures from bypassing
-- the literal physical Hamiltonian / continuum gap obligations.
------------------------------------------------------------------------

record YMMassGapRoute (N : Nat) : Setω where
  field
    sunLane : SUNLane N
    target : YMMassGapTarget N
    lattice : LatticeYangMills N
    balabanRG : BalabanRGLane
    osBundle : OSAxiomBundle
    wightman : WightmanReconstructionLane
    spectralGap : MassGapSpectralStatement
    o4Restoration : O4RestorationLane

    operatorContinuumFrontier : Frontier.YMOperatorContinuumFrontier

    -- Closed generic machinery genuinely returned by Lean.
    generatorUniquenessAvailable : Bool
    symmetryNullPreservationAvailable : Bool
    gaugeInvariantCarrierAvailable : Bool
    boundedStrongLimitGapTransportAvailable : Bool

    -- Physical bridge obligations still required by this route.
    physicalPartialDomainHamiltonianClosed : Bool
    ymEqualsOSEvolutionClosed : Bool
    unboundedContinuumGapTransportClosed : Bool
    finiteToContinuumConstructionClosed : Bool
    physicalContinuumOSWightmanClosed : Bool

    logSobolev : Bool
    witten : Bool
    qit : Bool
    clayYangMillsPromotedRoute : Bool

    generatorUniquenessAvailableIsTrue : generatorUniquenessAvailable ≡ true
    symmetryNullPreservationAvailableIsTrue : symmetryNullPreservationAvailable ≡ true
    gaugeInvariantCarrierAvailableIsTrue : gaugeInvariantCarrierAvailable ≡ true
    boundedStrongLimitGapTransportAvailableIsTrue :
      boundedStrongLimitGapTransportAvailable ≡ true

    physicalPartialDomainHamiltonianClosedIsFalse :
      physicalPartialDomainHamiltonianClosed ≡ false
    ymEqualsOSEvolutionClosedIsFalse : ymEqualsOSEvolutionClosed ≡ false
    unboundedContinuumGapTransportClosedIsFalse :
      unboundedContinuumGapTransportClosed ≡ false
    finiteToContinuumConstructionClosedIsFalse :
      finiteToContinuumConstructionClosed ≡ false
    physicalContinuumOSWightmanClosedIsFalse :
      physicalContinuumOSWightmanClosed ≡ false

    logSobolevIsFalse : logSobolev ≡ false
    wittenIsFalse : witten ≡ false
    qitIsFalse : qit ≡ false
    clayYangMillsPromotedRouteIsFalse : clayYangMillsPromotedRoute ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalYMMassGapRoute : (N : Nat) → YMMassGapRoute N
canonicalYMMassGapRoute N = record
  { sunLane = canonicalSUNLane N
  ; target = canonicalYMMassGapTarget N
  ; lattice = canonicalLatticeYangMills N
  ; balabanRG = canonicalBalabanRGLane
  ; osBundle = canonicalOSAxiomBundle
  ; wightman = canonicalWightmanReconstructionLane
  ; spectralGap = canonicalMassGapSpectralStatement
  ; o4Restoration = canonicalO4RestorationLane
  ; operatorContinuumFrontier = Frontier.canonicalYMOperatorContinuumFrontier
  ; generatorUniquenessAvailable =
      Frontier.generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps
        Frontier.canonicalYMOperatorContinuumFrontier
  ; symmetryNullPreservationAvailable =
      Frontier.symmetryImpliesNullPreservationClosedForTotalLinearMaps
        Frontier.canonicalYMOperatorContinuumFrontier
  ; gaugeInvariantCarrierAvailable =
      Frontier.gaugeInvariantL2CarrierClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; boundedStrongLimitGapTransportAvailable =
      Frontier.boundedStrongLimitFormGapTransportClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalPartialDomainHamiltonianClosed =
      Frontier.genuinePartialDomainHamiltonianFormalized
        Frontier.canonicalYMOperatorContinuumFrontier
  ; ymEqualsOSEvolutionClosed =
      Frontier.ymEvolutionEqualsOSReconstructedEvolutionClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; unboundedContinuumGapTransportClosed =
      Frontier.unboundedClosedFormOrResolventGapTransportClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; finiteToContinuumConstructionClosed =
      Frontier.finiteToContinuumYMConstructionClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalContinuumOSWightmanClosed =
      Frontier.continuumOSWightmanPackageClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; logSobolev = false
  ; witten = false
  ; qit = false
  ; clayYangMillsPromotedRoute = false
  ; generatorUniquenessAvailableIsTrue = refl
  ; symmetryNullPreservationAvailableIsTrue = refl
  ; gaugeInvariantCarrierAvailableIsTrue = refl
  ; boundedStrongLimitGapTransportAvailableIsTrue = refl
  ; physicalPartialDomainHamiltonianClosedIsFalse = refl
  ; ymEqualsOSEvolutionClosedIsFalse = refl
  ; unboundedContinuumGapTransportClosedIsFalse = refl
  ; finiteToContinuumConstructionClosedIsFalse = refl
  ; physicalContinuumOSWightmanClosedIsFalse = refl
  ; logSobolevIsFalse = refl
  ; wittenIsFalse = refl
  ; qitIsFalse = refl
  ; clayYangMillsPromotedRouteIsFalse = refl
  ; noClayPromotion = refl
  }
