module DASHI.Unified.String369QuinticC3InvariantSpectrumBoundaryExact where

------------------------------------------------------------------------
-- ATTRIBUTION (2026-11-18):
-- CLASSICAL: Burnside, cyclic character/projective invariant theory,
-- Jacobian ring of smooth quintic, holomorphic Lefschetz/orbifold Euler
-- formulas, Calabi-Yau index/heterotic standard embedding.
-- EXISTING DASHI: original Fermat-quintic Jacobian owner, named
-- QuinticThreefoldCandidate, TriadicDepthOneCharacters,
-- TOE369C3RealizationGraphExact, CalabiYauPhysicalProducerCutset,
-- KKE6EtaCSWZSameBundleConsumerExact.
-- USER: 369/C3 observer selection may change accessible SM spectrum.
-- NEW: numeric finite-count consequence and necessary three-generation
-- negative control for this EXACT specified standard embedding.
-- The monomial orbit count and fixed-locus geometry were computed by
-- scripts/check_string369_quintic_c3_invariant_modes_exact.py.
-- These arithmetic theorems DO NOT kernel-prove monomial enumeration,
-- an equivariant Dirac index, an orbifold CFT or physical string model.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_+_; _*_; _∸_)
open import Data.Empty using (⊥)

import DASHI.Geometry.QuinticThreefoldCandidate as Quintic

reusedQuinticComplexDimension :
  Quintic.hypersurfaceComplexDimension Quintic.quinticThreefoldCandidate ≡ 3
reusedQuinticComplexDimension = Quintic.quinticComplexDimensionIsThree

-- Projective homogeneous degree-five polynomial space has dimension
-- 126; its C3 fixed monomials number 9. The degree-five Jacobian ideal
-- has dimension 25 and four fixed monomials. Thus 48-11=37 invariant
-- deformation directions. The written source proof here is ARITHMETIC.
polynomialFiveDimension : Nat
polynomialFiveDimension = 126

polynomialFiveFixedUnderC3 : Nat
polynomialFiveFixedUnderC3 = 9

polynomialFiveInvariantOrbits : Nat
polynomialFiveInvariantOrbits = 48

jacobianFiveDimension : Nat
jacobianFiveDimension = 25

jacobianFiveFixedUnderC3 : Nat
jacobianFiveFixedUnderC3 = 4

jacobianFiveInvariantOrbits : Nat
jacobianFiveInvariantOrbits = 11

invariantDeformations : Nat
invariantDeformations =
  polynomialFiveInvariantOrbits ∸ jacobianFiveInvariantOrbits

invariantDeformationsAre37 :
  invariantDeformations ≡ 37
invariantDeformationsAre37 = refl

-- Explicit cyclic representation dimensions: 37, 32, 32.
nontrivialCharacterMultiplicity : Nat
nontrivialCharacterMultiplicity = 32

fullDeformationDimension :
  invariantDeformations +
    nontrivialCharacterMultiplicity + nontrivialCharacterMultiplicity
    ≡ 101
fullDeformationDimension = refl

-- Standard-embedding untwisted C3-invariant net chiral count
-- 37-1=36; this DOES NOT include twisted sectors or physical
-- gauge/parity orbifold projections.
invariantKahlerDimension : Nat
invariantKahlerDimension = 1

untwistedInvariantDifference : Nat
untwistedInvariantDifference =
  invariantDeformations ∸ invariantKahlerDimension

untwistedIndexMagnitudeIs36 :
  untwistedInvariantDifference ≡ 36
untwistedIndexMagnitudeIs36 = refl

untwistedIndexIsNotThree :
  untwistedInvariantDifference ≡ 3 → ⊥
untwistedIndexIsNotThree ()

-- For THIS selected cyclic permutation, the projective fixed locus is
-- a smooth plane quintic curve of genus six plus two isolated points.
-- Euler fixed=-8; ordinary quotient Euler=-72; orbifold Euler=-88.
-- Store POSITIVE MAGNITUDES; their negative signs are in the
-- source-derived geometric formulas, not encoded by Nat arithmetic.
fixedCurveGenus : Nat
fixedCurveGenus = 6

fixedLocusEulerNegativeMagnitude : Nat
fixedLocusEulerNegativeMagnitude = 8

coarseQuotientEulerNegativeMagnitude : Nat
coarseQuotientEulerNegativeMagnitude = 72

orbifoldEulerNegativeMagnitude : Nat
orbifoldEulerNegativeMagnitude = 88

orbifoldEulerMagnitudeIs88 :
  orbifoldEulerNegativeMagnitude ≡ 88
orbifoldEulerMagnitudeIs88 = refl

-- IMPORTANT: -88 is an orbifold topological invariant for the chosen
-- group action; it is NOT automatically a heterotic physical chiral
-- index or a complete three-family twisted-sector spectrum.
