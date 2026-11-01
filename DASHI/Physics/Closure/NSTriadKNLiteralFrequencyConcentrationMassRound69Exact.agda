module DASHI.Physics.Closure.NSTriadKNLiteralFrequencyConcentrationMassRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- ROUND 69 / LITERAL FREQUENCY CONCENTRATION MASS
--
-- Before asking for physical-space Carleman propagation, retain the finest
-- already-constructed frequency authority: the classified physical output
-- fibre.  Every cell still contains its literal PhysicalTriadIncidence and
-- therefore its p,q,k coordinates and shell classification.
--
-- For any literal triad functional a(tau), define the nonnegative frequency
-- mass on a classified fibre by
--
--       sum_tau a(tau)^2.
--
-- Classification does not alter this mass: erasing the classifications gives
-- exactly the original physical output fibre, and the squared-mass folds agree
-- definitionally by recursion.  This is a genuine nonnegative concentration
-- candidate on actual Fourier incidences, not an arbitrary Duhamel selector.
--
-- The hard missing theorem is now precise: excess critical-ratio remainder
-- must force a lower bound on this mass in a suitably localized subfibre (and,
-- for Barker-Prange/Tao propagation, ultimately a physical-space analogue).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

rawSquaredMass :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
rawSquaredMass value [] = 0ℚ
rawSquaredMass value (tau ∷ rest) =
  L2.square (value tau) + rawSquaredMass value rest

classifiedSquaredMass :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Support.ClassifiedPhysicalTriad → ℚ
classifiedSquaredMass value [] = 0ℚ
classifiedSquaredMass value (classified ∷ rest) =
  L2.square (value (Support.incidence classified))
    + classifiedSquaredMass value rest

classifyPreservesSquaredMass :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (triads : List Physical.PhysicalTriadIncidence) →
  classifiedSquaredMass value (Support.classifyPhysicalTriads triads)
  ≡ rawSquaredMass value triads
classifyPreservesSquaredMass value [] = refl
classifyPreservesSquaredMass value (tau ∷ rest) =
  cong (L2.square (value tau) +_)
    (classifyPreservesSquaredMass value rest)

physicalOutputFrequencyMass :
  Nat → Z3.FourierMode →
  (Physical.PhysicalTriadIncidence → ℚ) → ℚ
physicalOutputFrequencyMass cutoff output value =
  classifiedSquaredMass value
    (Support.classifiedPhysicalOutputFiber cutoff output)

physicalOutputFrequencyMassIsRawFibreMass :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  physicalOutputFrequencyMass cutoff output value
  ≡ rawSquaredMass value (Output.physicalOutputFiber cutoff output)
physicalOutputFrequencyMassIsRawFibreMass cutoff output value =
  classifyPreservesSquaredMass value
    (Output.physicalOutputFiber cutoff output)

rawSquaredMassNonnegative :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (triads : List Physical.PhysicalTriadIncidence) →
  0ℚ ≤ rawSquaredMass value triads
rawSquaredMassNonnegative value [] = ℚP.≤-refl
rawSquaredMassNonnegative value (tau ∷ rest) =
  L2.addNonnegative
    (L2.squareNonnegative (value tau))
    (rawSquaredMassNonnegative value rest)

physicalOutputFrequencyMassNonnegative :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  0ℚ ≤ physicalOutputFrequencyMass cutoff output value
physicalOutputFrequencyMassNonnegative cutoff output value =
  let
    rawNN = rawSquaredMassNonnegative value
      (Output.physicalOutputFiber cutoff output)
  in
  subst
    (0ℚ ≤_)
    (sym (physicalOutputFrequencyMassIsRawFibreMass cutoff output value))
    rawNN

round69LiteralFrequencyConcentrationMassConstructed : Bool
round69LiteralFrequencyConcentrationMassConstructed = true

round69RemainderForcesLocalizedFrequencyMassConstructed : Bool
round69RemainderForcesLocalizedFrequencyMassConstructed = false

round69PhysicalSpaceConcentrationPropagationConstructed : Bool
round69PhysicalSpaceConcentrationPropagationConstructed = false

round69LiteralFrequencyConcentrationMassConstructedIsTrue :
  round69LiteralFrequencyConcentrationMassConstructed ≡ true
round69LiteralFrequencyConcentrationMassConstructedIsTrue = refl

round69RemainderForcesLocalizedFrequencyMassConstructedIsFalse :
  round69RemainderForcesLocalizedFrequencyMassConstructed ≡ false
round69RemainderForcesLocalizedFrequencyMassConstructedIsFalse = refl
