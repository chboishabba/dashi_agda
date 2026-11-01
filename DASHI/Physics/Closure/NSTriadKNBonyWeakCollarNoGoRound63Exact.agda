module DASHI.Physics.Closure.NSTriadKNBonyWeakCollarNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 COLLAR FALSIFIER
--
-- The mature physical classifier uses the STRICT predicate
--
--   natLess (j_low + 3) j_high = true.
--
-- Replacing it by the weak inequality j_low+3<=j_high changes the class at the
-- three-shell boundary.  The existing concrete witness has
--
--   j(q)=0, j(p)=3, j(k)=3.
--
-- Thus the weak HL inequality holds exactly, while the authoritative physical
-- classifier returns CC/comparable.  This file keeps that off-by-one semantic
-- mismatch executable so future Bony adapters cannot silently use the weak
-- collar as if it were equivalent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Raw

farPhysicalTriad : Physical.PhysicalTriadIncidence
farPhysicalTriad =
  Physical.physicalTriad Raw.farP Raw.farInput Raw.farOutput Raw.farResonance

weakHLBoundaryHolds :
  Shell.shellIndex Raw.farInput + Shell.Csep
  ≤ Shell.shellIndex Raw.farP
weakHLBoundaryHolds
  rewrite Raw.farInputShellIsZero = Nat.≤-refl

authoritativeClassAtBoundaryIsComparable :
  Support.triadicSourceClass farPhysicalTriad ≡ Support.CC
authoritativeClassAtBoundaryIsComparable = refl

weakAndStrictCollarsAreNotInterchangeable : Bool
weakAndStrictCollarsAreNotInterchangeable = true

weakAndStrictCollarsAreNotInterchangeableIsTrue :
  weakAndStrictCollarsAreNotInterchangeable ≡ true
weakAndStrictCollarsAreNotInterchangeableIsTrue = refl
