module DASHI.Physics.Closure.NSTriadKNLocalizedPDETriadicConcentrationMassRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 69 / CONCENTRATION MASS ON THE ONE STRUCTURED PDE LIST
--
-- Round62 already defined the right D/F authority: ONE LocalizedPDEAtom list
-- containing physical five-source atoms, tail, duplicate/cancelling/independent
-- kernel atoms and classified lower/upper boundary atoms.  Do not introduce a
-- parallel concentration carrier.
--
-- This module measures the nonnegative squared mass of the TRIADIC physical
-- atoms in that exact list.  A triadic physicalAtom stores a FiveSourceCell of
-- the form `triadicSource classified`, and the classified object retains the
-- literal PhysicalTriadIncidence (p,q,k plus its shell class certificate).
-- Differentiated commutator cells remain physical source atoms but are kept out
-- of this first triadic concentration mass; kernel/tail/boundary atoms are also
-- excluded rather than silently taxed as concentration.
--
-- The resulting quantity is nonnegative by construction.  The hard PDE theorem
-- is now sharply same-object:
--
--   excess Xi remainder <= / forces lower bound on
--   triadicConcentrationMass atoms
--
-- for the structured atom list emitted by the actual localized trajectory
-- identity.  No free Duhamel selector is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

triadicConcentrationMass : List Structured.LocalizedPDEAtom → ℚ
triadicConcentrationMass [] = 0ℚ
triadicConcentrationMass
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) =
  L2.square value + triadicConcentrationMass rest
triadicConcentrationMass
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass (Structured.tailAtom value ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass (Structured.duplicateKernelAtom value ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass
    (Structured.cancellingKernelPair left right cancellation ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass (Structured.independentKernelAtom value ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass
    (Structured.lowerBoundaryAtom reason value ∷ rest) =
  triadicConcentrationMass rest
triadicConcentrationMass
    (Structured.upperBoundaryAtom reason value ∷ rest) =
  triadicConcentrationMass rest

triadicConcentrationMassNonnegative :
  (atoms : List Structured.LocalizedPDEAtom) →
  0ℚ ≤ triadicConcentrationMass atoms
triadicConcentrationMassNonnegative [] = ℚP.≤-refl
triadicConcentrationMassNonnegative
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) =
  L2.addNonnegative
    (L2.squareNonnegative value)
    (triadicConcentrationMassNonnegative rest)
triadicConcentrationMassNonnegative
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative (Structured.tailAtom value ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative
    (Structured.duplicateKernelAtom value ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative
    (Structured.cancellingKernelPair left right cancellation ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative
    (Structured.independentKernelAtom value ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative
    (Structured.lowerBoundaryAtom reason value ∷ rest) =
  triadicConcentrationMassNonnegative rest
triadicConcentrationMassNonnegative
    (Structured.upperBoundaryAtom reason value ∷ rest) =
  triadicConcentrationMassNonnegative rest

-- Exact singleton calibration makes clear that the quantity measures the value
-- stored by the literal physicalAtom, not an independently supplied functional.
triadicSingletonMass :
  ∀ classified selected compatible value →
  triadicConcentrationMass
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ [])
  ≡ L2.square value
triadicSingletonMass classified selected compatible value =
  ℚP.+-identityʳ (L2.square value)

commutatorSingletonDoesNotEnterTriadicMass :
  ∀ output selected compatible value →
  triadicConcentrationMass
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ [])
  ≡ 0ℚ
commutatorSingletonDoesNotEnterTriadicMass output selected compatible value = refl

round69StructuredTriadicConcentrationMassConstructed : Bool
round69StructuredTriadicConcentrationMassConstructed = true

round69CriticalRemainderForcesStructuredTriadicMass : Bool
round69CriticalRemainderForcesStructuredTriadicMass = false

round69StructuredTriadicConcentrationMassConstructedIsTrue :
  round69StructuredTriadicConcentrationMassConstructed ≡ true
round69StructuredTriadicConcentrationMassConstructedIsTrue = refl

round69CriticalRemainderForcesStructuredTriadicMassIsFalse :
  round69CriticalRemainderForcesStructuredTriadicMass ≡ false
round69CriticalRemainderForcesStructuredTriadicMassIsFalse = refl
