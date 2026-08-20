module DASHI.Physics.Closure.NSTriadKNTimeDependentFineStructuredBalanceRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Jean Duchon; Raoul Robert.
-- Title: "Inertial energy dissipation for weak solutions of incompressible
-- Euler and Navier-Stokes equations".
-- Nonlinearity 13 (2000), 249--255.
-- DOI: 10.1088/0951-7715/13/1/312.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- ROUND74 / SAME-TIME FINE STRUCTURED BALANCE
--
-- Duchon--Robert is relevant as provenance for exact localized energy balances
-- and explicit defect terms, but its weak-solution defect is NOT identified
-- with DASHI's independent kernel/boundary atoms.
--
-- The repository already contains two stronger same-object ingredients for the
-- finite Galerkin lane:
--
--   * Round30: one DynamicPhysicalShellBalance at each trajectory time;
--   * Round72: the static five-source pairing at that time refines exactly into
--     the official Round62 LocalizedPDEAtom / SignedConstituent language.
--
-- This file composes them.  Modulo the genuine HH-good/HH-bad owner selection,
-- every time slice now has an exact one-list physical source expansion and the
-- dynamic balance can be rewritten directly against that list.
--
-- Remaining dynamic work is therefore narrower: instantiate Round30 from the
-- selected trajectory/chain rule, construct the HH owner decision, and emit the
-- literal localization kernel/tail/boundary atoms.  Static five-source
-- refinement is no longer part of that frontier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact as Dynamic
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as FineTriadic
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsFineFiveSourceAtomsRound72Exact as FineFive

finePhysicalAtomsAt :
  ∀ {timeLevel : Level} {Time : Set timeLevel} →
  (dataSet : Dynamic.PhysicalTimeDependentShellBalance Time) →
  (hhAt : Time → FineTriadic.HHOwnerSelection) →
  Time → List Structured.LocalizedPDEAtom
finePhysicalAtomsAt dataSet hhAt time =
  FineFive.fineFiveSourceAtoms
    (Shell.staticPairing (Dynamic.balanceAt dataSet time))
    (hhAt time)

finePhysicalSignedTotalAt :
  ∀ {timeLevel : Level} {Time : Set timeLevel} →
  (dataSet : Dynamic.PhysicalTimeDependentShellBalance Time) →
  (hhAt : Time → FineTriadic.HHOwnerSelection) →
  Time → ℚ
finePhysicalSignedTotalAt dataSet hhAt time =
  Signed.signedConstituentTotal
    (Structured.flattenAtoms (finePhysicalAtomsAt dataSet hhAt time))

finePhysicalSignedTotalIsGlobalPairing :
  ∀ {timeLevel : Level} {Time : Set timeLevel}
    (dataSet : Dynamic.PhysicalTimeDependentShellBalance Time)
    (hhAt : Time → FineTriadic.HHOwnerSelection)
    (time : Time) →
  finePhysicalSignedTotalAt dataSet hhAt time
  ≡ Shell.globalBilinearPairing
      (Shell.staticPairing (Dynamic.balanceAt dataSet time))
finePhysicalSignedTotalIsGlobalPairing dataSet hhAt time =
  let
    pairing = Shell.staticPairing (Dynamic.balanceAt dataSet time)
  in
  trans
    (FineFive.flattenedFineFiveSourceTotalExact pairing (hhAt time))
    (sym (Shell.globalPairingMeaning pairing))

fineStructuredDynamicBalanceAt :
  ∀ {timeLevel : Level} {Time : Set timeLevel}
    (dataSet : Dynamic.PhysicalTimeDependentShellBalance Time)
    (hhAt : Time → FineTriadic.HHOwnerSelection)
    (time : Time) →
  Shell.energyDerivative (Dynamic.balanceAt dataSet time)
    + Shell.diffusion (Dynamic.balanceAt dataSet time)
  ≡
  finePhysicalSignedTotalAt dataSet hhAt time
    + Shell.lowerBoundary (Dynamic.balanceAt dataSet time)
    + Shell.upperBoundary (Dynamic.balanceAt dataSet time)
fineStructuredDynamicBalanceAt dataSet hhAt time =
  let
    balance = Dynamic.balanceAt dataSet time
  in
  trans
    (Shell.globalDynamicBalance balance)
    (cong
      (λ source →
        source + Shell.lowerBoundary balance + Shell.upperBoundary balance)
      (sym (finePhysicalSignedTotalIsGlobalPairing dataSet hhAt time)))

round74TimeDependentStaticFiveSourcesEmitOfficialFineList : Bool
round74TimeDependentStaticFiveSourcesEmitOfficialFineList = true

round74FineListDynamicBalanceConstructedModuloTrajectoryAndHHSelection : Bool
round74FineListDynamicBalanceConstructedModuloTrajectoryAndHHSelection = true

round74DuchonRobertDefectIdentifiedWithDASHIKernel : Bool
round74DuchonRobertDefectIdentifiedWithDASHIKernel = false

round74SelectedTrajectoryInstantiatesRound30Balance : Bool
round74SelectedTrajectoryInstantiatesRound30Balance = false

round74FineListDynamicBalanceConstructedModuloTrajectoryAndHHSelectionIsTrue :
  round74FineListDynamicBalanceConstructedModuloTrajectoryAndHHSelection ≡ true
round74FineListDynamicBalanceConstructedModuloTrajectoryAndHHSelectionIsTrue = refl

round74DuchonRobertDefectIdentifiedWithDASHIKernelIsFalse :
  round74DuchonRobertDefectIdentifiedWithDASHIKernel ≡ false
round74DuchonRobertDefectIdentifiedWithDASHIKernelIsFalse = refl
