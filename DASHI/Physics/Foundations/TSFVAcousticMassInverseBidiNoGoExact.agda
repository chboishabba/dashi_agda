{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVAcousticMassInverseBidiNoGoExact where

------------------------------------------------------------------------
-- P02/P03/P07: SOURCE-NATIVE ACOUSTIC BIDI NONPROMOTION.
--
-- Reuses the ACTUAL selected three-axis scalar-lattice continuum
-- principal quadratic in TSFVSelectedLatticeAcousticKKFlatControlExact.
-- A measured principal symbol / null cone is insensitive to mass².
-- The full retarded Fourier denominator DOES distinguish different
-- masses (already at zero frequency/momentum). Thus reproducing a
-- physical (3,1) propagation cone alone cannot identify a unique
-- quantum H, vacuum, OS reconstruction or microscopic observer.
--
-- This is exact rational algebra on the selected analytic CONTROL,
-- not an independently measured original TSVF source. No new free
-- Hamiltonian, physical gauge theory or source-specific mass is
-- postulated by this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.TSFVSelectedLatticeAcousticKKFlatControlExact as Acoustic

-- The same ORIGINAL continuum principal in both models, even
-- when the selected lower-order dynamical coefficients differ.
selectedAcousticPrincipalForAnyMass :
  (massSquared : ℚ) (omega kx ky kz : ℚ) → ℚ
selectedAcousticPrincipalForAnyMass massSquared =
  Acoustic.sourceMeasuredWavePrincipal

allMassesShareSelectedAcousticPrincipal :
  ∀ mass1 mass2 omega kx ky kz →
    selectedAcousticPrincipalForAnyMass mass1 omega kx ky kz
    ≡
    selectedAcousticPrincipalForAnyMass mass2 omega kx ky kz
allMassesShareSelectedAcousticPrincipal
    mass1 mass2 omega kx ky kz = refl

-- The full source operator contains a lower-order mass² term,
-- which does not enter the hyperbolic principal quadratic.
selectedAcousticFullFourierDenominator :
  (massSquared omega kx ky kz : ℚ) → ℚ
selectedAcousticFullFourierDenominator massSquared omega kx ky kz =
  Acoustic.sourceMeasuredWavePrincipal omega kx ky kz
  + massSquared

-- Zero momentum and zero frequency provide an exact MASS readout.
selectedZeroFourierReadoutIsMass :
  ∀ massSquared →
    selectedAcousticFullFourierDenominator
      massSquared 0ℚ 0ℚ 0ℚ 0ℚ
    ≡ massSquared
selectedZeroFourierReadoutIsMass massSquared =
  Ring.solve-∀ massSquared

-- If two COMPLETE frequency-response operators agreed at every
-- Fourier point, their physically selected squared masses
-- must agree. This is a derived constraint on any inverse theory.
fullSelectedResponseEqualityForcesSameMass :
  ∀ mass1 mass2 →
    (∀ omega kx ky kz →
      selectedAcousticFullFourierDenominator
        mass1 omega kx ky kz
      ≡
      selectedAcousticFullFourierDenominator
        mass2 omega kx ky kz) →
    mass1 ≡ mass2
fullSelectedResponseEqualityForcesSameMass mass1 mass2 equality =
  trans
    (sym (selectedZeroFourierReadoutIsMass mass1))
    (trans
      (equality 0ℚ 0ℚ 0ℚ 0ℚ)
      (selectedZeroFourierReadoutIsMass mass2))

-- Therefore equality of a physically measured principal (3,1)
-- quadratic does NOT justify upgrading the underlying source to
-- a unique quantum Hamiltonian or a same-OS-H theorem.
differentMassCannotShareEntireResponse :
  ∀ mass1 mass2 →
    (mass1 ≡ mass2 → ⊥) →
    (∀ omega kx ky kz →
      selectedAcousticFullFourierDenominator
        mass1 omega kx ky kz
      ≡
      selectedAcousticFullFourierDenominator
        mass2 omega kx ky kz) →
    ⊥
differentMassCannotShareEntireResponse mass1 mass2 different equal =
  different (fullSelectedResponseEqualityForcesSameMass mass1 mass2 equal)

-- Missing physical producer: actual TSVF state and a measured
-- retarded response including finite-frequency lower-order
-- observables, with its selected Hilbert/OS identification.
