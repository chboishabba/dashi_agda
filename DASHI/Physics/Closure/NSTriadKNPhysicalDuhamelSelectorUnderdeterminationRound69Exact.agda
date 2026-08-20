module DASHI.Physics.Closure.NSTriadKNPhysicalDuhamelSelectorUnderdeterminationRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- ROUND 69 / SAME-TRAJECTORY SELECTOR UNDERDETERMINATION
--
-- The present Round59 `PhysicalLocalizedDuhamelSource` does bind all selectors
-- to one physical time-dependent shell balance, but the selector FUNCTIONS are
-- still unconstrained fields.  Consequently the same physical shell data and
-- the same literal-trajectory authority can be equipped with generatedSelector
-- constantly 0 or constantly 1.
--
-- This is an exact falsifier for treating `generatedAt` as physical
-- concentration before the localized PDE identity is constructed.  The next
-- source type must derive generated/leakage/defect from the literal signed
-- constituent list; it cannot merely carry arbitrary projection functions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (0ℚ; 1ℚ)

import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 as Source

zeroGeneratedSource :
  Source.PhysicalLocalizedDuhamelSource →
  Source.PhysicalLocalizedDuhamelSource
zeroGeneratedSource source = record
  { physicalShellData = Source.physicalShellData source
  ; shellAt = Source.shellAt source
  ; defectSelector = Source.defectSelector source
  ; inheritedSelector = Source.inheritedSelector source
  ; generatedSelector = λ _ → 0ℚ
  ; leakageSelector = Source.leakageSelector source
  ; parameter = Source.parameter source
  ; ceiling = Source.ceiling source
  ; alpha = Source.alpha source
  ; beta = Source.beta source
  ; literalTrajectoryAuthority = Source.literalTrajectoryAuthority source
  }

oneGeneratedSource :
  Source.PhysicalLocalizedDuhamelSource →
  Source.PhysicalLocalizedDuhamelSource
oneGeneratedSource source = record
  { physicalShellData = Source.physicalShellData source
  ; shellAt = Source.shellAt source
  ; defectSelector = Source.defectSelector source
  ; inheritedSelector = Source.inheritedSelector source
  ; generatedSelector = λ _ → 1ℚ
  ; leakageSelector = Source.leakageSelector source
  ; parameter = Source.parameter source
  ; ceiling = Source.ceiling source
  ; alpha = Source.alpha source
  ; beta = Source.beta source
  ; literalTrajectoryAuthority = Source.literalTrajectoryAuthority source
  }

zeroSourceKeepsPhysicalShellData : ∀ source →
  Source.physicalShellData (zeroGeneratedSource source)
  ≡ Source.physicalShellData source
zeroSourceKeepsPhysicalShellData source = refl

oneSourceKeepsPhysicalShellData : ∀ source →
  Source.physicalShellData (oneGeneratedSource source)
  ≡ Source.physicalShellData source
oneSourceKeepsPhysicalShellData source = refl

zeroSourceKeepsLiteralTrajectoryAuthority : ∀ source →
  Source.literalTrajectoryAuthority (zeroGeneratedSource source)
  ≡ Source.literalTrajectoryAuthority source
zeroSourceKeepsLiteralTrajectoryAuthority source = refl

oneSourceKeepsLiteralTrajectoryAuthority : ∀ source →
  Source.literalTrajectoryAuthority (oneGeneratedSource source)
  ≡ Source.literalTrajectoryAuthority source
oneSourceKeepsLiteralTrajectoryAuthority source = refl

zeroGeneratedAt :
  (source : Source.PhysicalLocalizedDuhamelSource) →
  (q : Nat) →
  Source.generatedAt (zeroGeneratedSource source) q ≡ 0ℚ
zeroGeneratedAt source q = refl

oneGeneratedAt :
  (source : Source.PhysicalLocalizedDuhamelSource) →
  (q : Nat) →
  Source.generatedAt (oneGeneratedSource source) q ≡ 1ℚ
oneGeneratedAt source q = refl

-- The physical shell balance, shell index, threshold and trajectory authority
-- are unchanged simultaneously; only the alleged generated physical quantity
-- changes.  This is exactly the seam the Round69 localized-identity producer
-- must eliminate.
sameTrajectoryFreeGeneratedSelectorFalsifier : Bool
sameTrajectoryFreeGeneratedSelectorFalsifier = true

round69CurrentDuhamelSourceSufficientForPhysicalConcentration : Bool
round69CurrentDuhamelSourceSufficientForPhysicalConcentration = false

sameTrajectoryFreeGeneratedSelectorFalsifierIsTrue :
  sameTrajectoryFreeGeneratedSelectorFalsifier ≡ true
sameTrajectoryFreeGeneratedSelectorFalsifierIsTrue = refl

round69CurrentDuhamelSourceSufficientForPhysicalConcentrationIsFalse :
  round69CurrentDuhamelSourceSufficientForPhysicalConcentration ≡ false
round69CurrentDuhamelSourceSufficientForPhysicalConcentrationIsFalse = refl
