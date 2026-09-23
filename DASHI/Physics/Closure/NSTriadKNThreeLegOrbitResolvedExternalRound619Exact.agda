{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNThreeLegOrbitResolvedExternalRound619Exact where

------------------------------------------------------------------------
-- ROUND619 / TOTAL THREE-LEG EXTERNAL FORCING WITH FIXED-ORBIT CORRECTIONS
--
-- R618 gives a total proof-relevant representation of the k-leg external
-- forcing for either swap-orbit case:
--
--   nonfixed -> the R111 self-orbit-removed residual vector;
--   fixed    -> one-point residual minus the selected ordered term.
--
-- R112 already identifies the physical p/q external forcings definitionally
-- with the k-leg external forcing of pEnergyLeg/qEnergyLeg.  R616 constructs
-- those energy legs' own-fibre memberships from the selected incidence's
-- literal own-fibre membership.
--
-- Therefore all three external forcing legs admit the same total orbit-resolved
-- representation without assuming the three exceptional diagonals are absent.
-- No estimate, norm, sign, Bony bound, or cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact as R616
import DASHI.Physics.Closure.NSTriadKNExternalSelfOrbitMultiplicityRound618Exact as R618

record ThreeLegSwapOrbitCases
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor three-leg-swap-orbit-cases
  field
    kOrbitCase : R618.SwapOrbitCase tau
    pOrbitCase : R618.SwapOrbitCase (Orbit.pEnergyLeg tau)
    qOrbitCase : R618.SwapOrbitCase (Orbit.qEnergyLeg tau)

open ThreeLegSwapOrbitCases public

externalKOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  R618.SwapOrbitCase tau →
  C3.Complex3 F
externalKOrbitResolved system tau tauMember orbitCase =
  R618.orbitResolvedExternalVector system tau tauMember orbitCase

externalPOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  R618.SwapOrbitCase (Orbit.pEnergyLeg tau) →
  C3.Complex3 F
externalPOrbitResolved system tau tauMember orbitCase =
  R618.orbitResolvedExternalVector
    system
    (Orbit.pEnergyLeg tau)
    (R616.pEnergyLegOwnFibreMember tauMember)
    orbitCase

externalQOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  R618.SwapOrbitCase (Orbit.qEnergyLeg tau) →
  C3.Complex3 F
externalQOrbitResolved system tau tauMember orbitCase =
  R618.orbitResolvedExternalVector
    system
    (Orbit.qEnergyLeg tau)
    (R616.qEnergyLegOwnFibreMember tauMember)
    orbitCase

externalForcingKIsThreeLegOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (cases : ThreeLegSwapOrbitCases tau) →
  Split.externalForcingK system tau
  ≡ externalKOrbitResolved system tau tauMember (kOrbitCase cases)
externalForcingKIsThreeLegOrbitResolved system tau tauMember cases =
  R618.externalForcingKIsOrbitResolved
    system tau tauMember (kOrbitCase cases)

externalForcingPIsThreeLegOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (cases : ThreeLegSwapOrbitCases tau) →
  Split.externalForcingP system tau
  ≡ externalPOrbitResolved system tau tauMember (pOrbitCase cases)
externalForcingPIsThreeLegOrbitResolved system tau tauMember cases =
  trans
    (R112.externalForcingPAsKOfPEnergyLeg system tau)
    (R618.externalForcingKIsOrbitResolved
      system
      (Orbit.pEnergyLeg tau)
      (R616.pEnergyLegOwnFibreMember tauMember)
      (pOrbitCase cases))

externalForcingQIsThreeLegOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (cases : ThreeLegSwapOrbitCases tau) →
  Split.externalForcingQ system tau
  ≡ externalQOrbitResolved system tau tauMember (qOrbitCase cases)
externalForcingQIsThreeLegOrbitResolved system tau tauMember cases =
  trans
    (R112.externalForcingQAsKOfQEnergyLeg system tau)
    (R618.externalForcingKIsOrbitResolved
      system
      (Orbit.qEnergyLeg tau)
      (R616.qEnergyLegOwnFibreMember tauMember)
      (qOrbitCase cases))

record ThreeLegOrbitResolvedExternalForcing
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (cases : ThreeLegSwapOrbitCases tau) : Set r where
  constructor three-leg-orbit-resolved-external-forcing
  field
    kExact :
      Split.externalForcingK system tau
      ≡ externalKOrbitResolved system tau tauMember (kOrbitCase cases)
    pExact :
      Split.externalForcingP system tau
      ≡ externalPOrbitResolved system tau tauMember (pOrbitCase cases)
    qExact :
      Split.externalForcingQ system tau
      ≡ externalQOrbitResolved system tau tauMember (qOrbitCase cases)

threeLegOrbitResolvedExternalForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (cases : ThreeLegSwapOrbitCases tau) →
  ThreeLegOrbitResolvedExternalForcing system tau tauMember cases
threeLegOrbitResolvedExternalForcing system tau tauMember cases =
  record
    { kExact =
        externalForcingKIsThreeLegOrbitResolved
          system tau tauMember cases
    ; pExact =
        externalForcingPIsThreeLegOrbitResolved
          system tau tauMember cases
    ; qExact =
        externalForcingQIsThreeLegOrbitResolved
          system tau tauMember cases
    }

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round619AllThreeExternalLegsOrbitResolved : Bool
round619AllThreeExternalLegsOrbitResolved = true

round619RequiresExceptionalLociAbsent : Bool
round619RequiresExceptionalLociAbsent = false

round619FixedOrbitCorrectionRetained : Bool
round619FixedOrbitCorrectionRetained = true

round619ConstructsR112NonfixedWitnessInFixedCases : Bool
round619ConstructsR112NonfixedWitnessInFixedCases = false

round619IntroducesEstimate : Bool
round619IntroducesEstimate = false

round619ExternalPaymentClosed : Bool
round619ExternalPaymentClosed = false

round619AllThreeExternalLegsOrbitResolvedIsTrue :
  round619AllThreeExternalLegsOrbitResolved ≡ true
round619AllThreeExternalLegsOrbitResolvedIsTrue = refl

round619RequiresExceptionalLociAbsentIsFalse :
  round619RequiresExceptionalLociAbsent ≡ false
round619RequiresExceptionalLociAbsentIsFalse = refl

round619FixedOrbitCorrectionRetainedIsTrue :
  round619FixedOrbitCorrectionRetained ≡ true
round619FixedOrbitCorrectionRetainedIsTrue = refl

round619ConstructsR112NonfixedWitnessInFixedCasesIsFalse :
  round619ConstructsR112NonfixedWitnessInFixedCases ≡ false
round619ConstructsR112NonfixedWitnessInFixedCasesIsFalse = refl

round619IntroducesEstimateIsFalse :
  round619IntroducesEstimate ≡ false
round619IntroducesEstimateIsFalse = refl

round619ExternalPaymentClosedIsFalse :
  round619ExternalPaymentClosed ≡ false
round619ExternalPaymentClosedIsFalse = refl
