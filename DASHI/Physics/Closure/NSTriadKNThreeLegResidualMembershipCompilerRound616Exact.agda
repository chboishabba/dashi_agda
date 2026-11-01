{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact where

------------------------------------------------------------------------
-- ROUND616 / CANONICAL R112 THREE-LEG RESIDUAL MEMBERSHIP COMPILER
--
-- R112's ThreeLegResidualMembership contains nine proof fields:
--
--   k/p/q selected membership,
--   k/p/q swap membership,
--   k/p/q swap-nonfixedness.
--
-- On the actual finite physical carrier the six membership fields are not
-- independent physical assumptions.  Starting from the selected incidence in
-- its own literal output fibre:
--
--   * R38 transports the incidence through pEnergyLeg / qEnergyLeg on the
--     complete physical enumeration;
--   * the exact p/q energy-leg output identities return those incidences to
--     their literal p/q output fibres;
--   * R224 supplies swap closure of every literal output fibre.
--
-- Therefore only the three nonfixedness witnesses remain as genuine inputs.
-- No estimate, norm, cardinality bound, or nonlinear theorem is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre35
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112

------------------------------------------------------------------------
-- Membership transport helpers.
------------------------------------------------------------------------

ownFibreMemberToEnumeration :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  tau ∈ Physical.physicalTriadEnumeration (Audit.cutoff system)
ownFibreMemberToEnumeration member =
  KFree.cubeMemberToStd
    (Fibre35.physicalOutputFiberMemberEnumeration
      (KFree.stdMemberToCube member))

pEnergyLegOwnFibreMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Orbit.pEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.p tau)
pEnergyLegOwnFibreMember {system = system} {tau = tau} member =
  KFree.cubeMemberToStd
    (Output.physicalOutputFiberComplete
      (KFree.stdMemberToCube
        (R38.pEnergyLegMember
          (ownFibreMemberToEnumeration member)))
      (Orbit.pEnergyLegOutput tau))

qEnergyLegOwnFibreMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Orbit.qEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.q tau)
qEnergyLegOwnFibreMember {system = system} {tau = tau} member =
  KFree.cubeMemberToStd
    (Output.physicalOutputFiberComplete
      (KFree.stdMemberToCube
        (R38.qEnergyLegMember
          (ownFibreMemberToEnumeration member)))
      (Orbit.qEnergyLegOutput tau))

------------------------------------------------------------------------
-- Main compiler: six memberships are generated, three nonfixedness witnesses
-- remain explicit.
------------------------------------------------------------------------

threeLegResidualMembershipFromOwnFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (kNonfixed : Symmetry.swapTriad tau ≢ tau) →
  (pNonfixed :
    Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau) →
  (qNonfixed :
    Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau) →
  R112.ThreeLegResidualMembership system tau
threeLegResidualMembershipFromOwnFibre
    system tau tauMember kNonfixed pNonfixed qNonfixed =
  let
    pMember = pEnergyLegOwnFibreMember tauMember
    qMember = qEnergyLegOwnFibreMember tauMember
  in
  record
    { R112.kMember = tauMember
    ; R112.kSwapMember = R224.swapOutputFibreMember tauMember
    ; R112.kSwapDifferent = kNonfixed
    ; R112.pMember = pMember
    ; R112.pSwapMember = R224.swapOutputFibreMember pMember
    ; R112.pSwapDifferent = pNonfixed
    ; R112.qMember = qMember
    ; R112.qSwapMember = R224.swapOutputFibreMember qMember
    ; R112.qSwapDifferent = qNonfixed
    }

------------------------------------------------------------------------
-- Actual fixed-output loop form.
------------------------------------------------------------------------

canonicalFibreMemberToOwnFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (tau : Physical.PhysicalTriadIncidence) →
  tau ∈ Output.physicalOutputFiber (Audit.cutoff system) output →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau)
canonicalFibreMemberToOwnFibre system output tau member =
  subst
    (λ selectedOutput →
      tau ∈ Output.physicalOutputFiber (Audit.cutoff system) selectedOutput)
    (sym (Output.physicalOutputFiberSound (KFree.stdMemberToCube member)))
    member

threeLegResidualMembershipFromCanonicalFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (tau : Physical.PhysicalTriadIncidence) →
  (member : tau ∈ Output.physicalOutputFiber (Audit.cutoff system) output) →
  (kNonfixed : Symmetry.swapTriad tau ≢ tau) →
  (pNonfixed :
    Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau) →
  (qNonfixed :
    Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau) →
  R112.ThreeLegResidualMembership system tau
threeLegResidualMembershipFromCanonicalFibre
    system output tau member kNonfixed pNonfixed qNonfixed =
  threeLegResidualMembershipFromOwnFibre
    system tau
    (canonicalFibreMemberToOwnFibre system output tau member)
    kNonfixed pNonfixed qNonfixed

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round616SixR112MembershipFieldsCompilerOwned : Bool
round616SixR112MembershipFieldsCompilerOwned = true

round616R112WitnessReducedToThreeNonfixednessInputs : Bool
round616R112WitnessReducedToThreeNonfixednessInputs = true

round616CanonicalResidualWitnessFamilyFullyInstalled : Bool
round616CanonicalResidualWitnessFamilyFullyInstalled = false

round616RemainingDebtIsOnlyThreeNonfixednessWitnesses : Bool
round616RemainingDebtIsOnlyThreeNonfixednessWitnesses = true

round616IntroducesEstimate : Bool
round616IntroducesEstimate = false

round616SixR112MembershipFieldsCompilerOwnedIsTrue :
  round616SixR112MembershipFieldsCompilerOwned ≡ true
round616SixR112MembershipFieldsCompilerOwnedIsTrue = refl

round616R112WitnessReducedToThreeNonfixednessInputsIsTrue :
  round616R112WitnessReducedToThreeNonfixednessInputs ≡ true
round616R112WitnessReducedToThreeNonfixednessInputsIsTrue = refl

round616CanonicalResidualWitnessFamilyFullyInstalledIsFalse :
  round616CanonicalResidualWitnessFamilyFullyInstalled ≡ false
round616CanonicalResidualWitnessFamilyFullyInstalledIsFalse = refl

round616RemainingDebtIsOnlyThreeNonfixednessWitnessesIsTrue :
  round616RemainingDebtIsOnlyThreeNonfixednessWitnesses ≡ true
round616RemainingDebtIsOnlyThreeNonfixednessWitnessesIsTrue = refl

round616IntroducesEstimateIsFalse :
  round616IntroducesEstimate ≡ false
round616IntroducesEstimateIsFalse = refl
