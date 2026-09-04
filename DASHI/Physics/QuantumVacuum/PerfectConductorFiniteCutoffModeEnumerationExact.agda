module DASHI.Physics.QuantumVacuum.PerfectConductorFiniteCutoffModeEnumerationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using ()
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Finite
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset

------------------------------------------------------------------------
-- FINITE-CUTOFF PERFECT-CONDUCTOR MODE ENUMERATION
--
-- The regulated Casimir calculation consumes finite mode lists at each cutoff.
-- This owner therefore separates finite cutoff exhaustiveness from continuum
-- Hilbert-space completeness.  At fixed finite transverse and longitudinal
-- bounds, every tuple
--
--   (k_perp label, n, TE/TM)
--
-- is enumerated constructively by a finite Cartesian product.  The Fin-coordinate
-- enumeration and completeness theorem are reused directly from DASHI's generic
-- FiniteProductEnumerationExact owner.
------------------------------------------------------------------------

polarisationList : List Cutset.Polarisation
polarisationList = Cutset.TE ∷ Cutset.TM ∷ []

polarisationComplete : (p : Cutset.Polarisation) → p ∈ polarisationList
polarisationComplete Cutset.TE = Any.here refl
polarisationComplete Cutset.TM = Any.there (Any.here refl)

FiniteModeCoordinate : Nat → Nat → Set
FiniteModeCoordinate transverseBound longitudinalBound =
  Fin transverseBound × (Fin longitudinalBound × Cutset.Polarisation)

longitudinalPolarisationCoordinates :
  (longitudinalBound : Nat) →
  List (Fin longitudinalBound × Cutset.Polarisation)
longitudinalPolarisationCoordinates longitudinalBound =
  cartesianProductWith _,_
    (Finite.allFin longitudinalBound)
    polarisationList

finiteModeCoordinates :
  (transverseBound longitudinalBound : Nat) →
  List (FiniteModeCoordinate transverseBound longitudinalBound)
finiteModeCoordinates transverseBound longitudinalBound =
  cartesianProductWith _,_
    (Finite.allFin transverseBound)
    (longitudinalPolarisationCoordinates longitudinalBound)

longitudinalPolarisationComplete :
  ∀ {longitudinalBound} →
  (n : Fin longitudinalBound) →
  (p : Cutset.Polarisation) →
  (n , p) ∈ longitudinalPolarisationCoordinates longitudinalBound
longitudinalPolarisationComplete n p =
  ∈-cartesianProductWith⁺ _,_
    (Finite.allFinComplete n)
    (polarisationComplete p)

finiteModeCoordinatesComplete :
  ∀ {transverseBound longitudinalBound} →
  (k : Fin transverseBound) →
  (n : Fin longitudinalBound) →
  (p : Cutset.Polarisation) →
  (k , (n , p)) ∈
    finiteModeCoordinates transverseBound longitudinalBound
finiteModeCoordinatesComplete k n p =
  ∈-cartesianProductWith⁺ _,_
    (Finite.allFinComplete k)
    (longitudinalPolarisationComplete n p)

record FiniteCutoffModeEnumerationReceipt : Set₁ where
  field
    transverseBound longitudinalBound : Nat
    coordinates : List (FiniteModeCoordinate transverseBound longitudinalBound)
    coordinatesExact :
      coordinates ≡ finiteModeCoordinates transverseBound longitudinalBound
    exhaustive :
      (k : Fin transverseBound) →
      (n : Fin longitudinalBound) →
      (p : Cutset.Polarisation) →
      (k , (n , p)) ∈ coordinates

open FiniteCutoffModeEnumerationReceipt public

canonicalFiniteCutoffModeEnumeration :
  (transverseBound longitudinalBound : Nat) →
  FiniteCutoffModeEnumerationReceipt
canonicalFiniteCutoffModeEnumeration transverseBound longitudinalBound = record
  { transverseBound = transverseBound
  ; longitudinalBound = longitudinalBound
  ; coordinates = finiteModeCoordinates transverseBound longitudinalBound
  ; coordinatesExact = refl
  ; exhaustive = finiteModeCoordinatesComplete
  }

data FiniteCutoffExhaustivenessAutomaticallyIsContinuumCompleteness : Set where

finiteDoesNotProveContinuumCompleteness :
  FiniteCutoffExhaustivenessAutomaticallyIsContinuumCompleteness → ⊥
finiteDoesNotProveContinuumCompleteness ()
