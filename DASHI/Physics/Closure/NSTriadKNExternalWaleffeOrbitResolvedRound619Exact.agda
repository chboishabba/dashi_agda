{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact where

------------------------------------------------------------------------
-- ROUND619 / TOTAL THREE-LEG EXTERNAL WALEFFE ORBIT RESOLUTION
--
-- R112's ThreeLegResidualMembership is intentionally nonfixed-only.
-- R618 now gives an exact external-forcing representation for either:
--
--   * a two-element selected swap orbit; or
--   * a swap-fixed selected orbit with the required multiplicity correction.
--
-- Apply that total representation independently to tau, pEnergyLeg tau and
-- qEnergyLeg tau.  This removes the need for a globally inhabited nonfixed-only
-- R112 witness family while preserving the exact selected-self multiplicity.
--
-- No estimate, absolute value, or analytic cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (cong₃; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNExternalSelfOrbitMultiplicityRound618Exact as R618
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact as R616

record ThreeLegOrbitResolvedSelection
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    kMember :
      tau ∈ Audit.concreteTriadsAt system (Physical.k tau)

    kOrbit : R618.SwapOrbitCase tau
    pOrbit : R618.SwapOrbitCase (Orbit.pEnergyLeg tau)
    qOrbit : R618.SwapOrbitCase (Orbit.qEnergyLeg tau)

open ThreeLegOrbitResolvedSelection public

pMemberResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  ThreeLegOrbitResolvedSelection system tau →
  Orbit.pEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.p tau)
pMemberResolved S = R616.pEnergyLegOwnFibreMember (kMember S)

qMemberResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  ThreeLegOrbitResolvedSelection system tau →
  Orbit.qEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.q tau)
qMemberResolved S = R616.qEnergyLegOwnFibreMember (kMember S)

externalResidualKResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegOrbitResolvedSelection system tau →
  C3.Complex3 F
externalResidualKResolved system tau S =
  R618.orbitResolvedExternalVector
    system tau (kMember S) (kOrbit S)

externalResidualPResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegOrbitResolvedSelection system tau →
  C3.Complex3 F
externalResidualPResolved system tau S =
  R618.orbitResolvedExternalVector
    system (Orbit.pEnergyLeg tau)
    (pMemberResolved S)
    (pOrbit S)

externalResidualQResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegOrbitResolvedSelection system tau →
  C3.Complex3 F
externalResidualQResolved system tau S =
  R618.orbitResolvedExternalVector
    system (Orbit.qEnergyLeg tau)
    (qMemberResolved S)
    (qOrbit S)

externalForcingKIsOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (S : ThreeLegOrbitResolvedSelection system tau) →
  Split.externalForcingK system tau
  ≡ externalResidualKResolved system tau S
externalForcingKIsOrbitResolved system tau S =
  R618.externalForcingKIsOrbitResolved
    system tau (kMember S) (kOrbit S)

externalForcingPIsOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (S : ThreeLegOrbitResolvedSelection system tau) →
  Split.externalForcingP system tau
  ≡ externalResidualPResolved system tau S
externalForcingPIsOrbitResolved system tau S =
  trans
    refl
    (R618.externalForcingKIsOrbitResolved
      system
      (Orbit.pEnergyLeg tau)
      (pMemberResolved S)
      (pOrbit S))

externalForcingQIsOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (S : ThreeLegOrbitResolvedSelection system tau) →
  Split.externalForcingQ system tau
  ≡ externalResidualQResolved system tau S
externalForcingQIsOrbitResolved system tau S =
  trans
    refl
    (R618.externalForcingKIsOrbitResolved
      system
      (Orbit.qEnergyLeg tau)
      (qMemberResolved S)
      (qOrbit S))

externalResidualNetworkForcingResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  ThreeLegOrbitResolvedSelection system tau →
  C3.Complex F
externalResidualNetworkForcingResolved system tau S =
  Tangent.networkForcing
    (Audit.velocity system (Physical.k tau))
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (externalResidualKResolved system tau S)
    (externalResidualPResolved system tau S)
    (externalResidualQResolved system tau S)

externalAmplitudeForcingIsOrbitResolvedNetwork :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (S : ThreeLegOrbitResolvedSelection system tau) →
  Split.externalAmplitudeForcing system tau
  ≡ externalResidualNetworkForcingResolved system tau S
externalAmplitudeForcingIsOrbitResolvedNetwork system tau S =
  cong₃
    (Tangent.networkForcing
      (Audit.velocity system (Physical.k tau))
      (Audit.velocity system (Physical.p tau))
      (Audit.velocity system (Physical.q tau)))
    (externalForcingKIsOrbitResolved system tau S)
    (externalForcingPIsOrbitResolved system tau S)
    (externalForcingQIsOrbitResolved system tau S)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round619ThreeLegExternalRepresentationTotalOverOrbitCases : Bool
round619ThreeLegExternalRepresentationTotalOverOrbitCases = true

round619RequiresGlobalNonfixedR112WitnessFamily : Bool
round619RequiresGlobalNonfixedR112WitnessFamily = false

round619PreservesFixedOrbitMultiplicityCorrection : Bool
round619PreservesFixedOrbitMultiplicityCorrection = true

round619IntroducesEstimate : Bool
round619IntroducesEstimate = false

round619ThreeLegExternalRepresentationTotalOverOrbitCasesIsTrue :
  round619ThreeLegExternalRepresentationTotalOverOrbitCases ≡ true
round619ThreeLegExternalRepresentationTotalOverOrbitCasesIsTrue = refl

round619RequiresGlobalNonfixedR112WitnessFamilyIsFalse :
  round619RequiresGlobalNonfixedR112WitnessFamily ≡ false
round619RequiresGlobalNonfixedR112WitnessFamilyIsFalse = refl

round619PreservesFixedOrbitMultiplicityCorrectionIsTrue :
  round619PreservesFixedOrbitMultiplicityCorrection ≡ true
round619PreservesFixedOrbitMultiplicityCorrectionIsTrue = refl

round619IntroducesEstimateIsFalse :
  round619IntroducesEstimate ≡ false
round619IntroducesEstimateIsFalse = refl
