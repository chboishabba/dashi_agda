module DASHI.Physics.YangMills.BalabanClayT4HypercubicLatticePerturbationMethodExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / METHOD IDENTIFICATION
--
-- M. Göckeler, R. Horsley, E.-M. Ilgenfritz, H. Perlt, P. Rakow,
-- G. Schierholz and A. Schiller,
-- "Lattice Operators for Moments of the Structure Functions and their
-- Transformation under the Hypercubic Group", Physical Review D 54 (1996),
-- 5705--5714. DOI: 10.1103/PhysRevD.54.5705.
-- This is a lattice-QCD source for the standard residual hypercubic-group
-- terminology after continuum rotational symmetry is reduced by the lattice.
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4. arXiv:hep-lat/0211036.
-- The review covers high-precision one-loop lattice integrals and explains the
-- coordinate-space method of Lüscher and Weisz in detail.
--
-- Martin Lüscher and Peter Weisz,
-- "Coordinate space methods for the evaluation of Feynman diagrams in
-- lattice field theories", Nuclear Physics B 445 (1995), 429--450.
-- DOI: 10.1016/0550-3213(95)00185-U. arXiv:hep-lat/9502017.
--
-- IMPORTANT METHOD BOUNDARY
--
-- The Lüscher--Weisz coordinate-space recursion method and DASHI's finite
-- generated-box orbit quotient are NOT identified.  They are distinct standard
-- ways of exploiting lattice structure in perturbative calculations.  The
-- source role here is methodological/provenance only.
--
-- DASHI CONTRIBUTION
--
-- Bind the already-constructed generated Brillouin-grid action to the standard
-- four-dimensional hypercubic/hyperoctahedral point-group presentation:
--
--      B4 = (C2)^4 semidirect S4.
--
-- On the concrete generator carrier this is visible as four coordinate sign
-- flips plus three adjacent transpositions.  The existing action module proves
-- each generator involutive and constructs paths to orbit representatives; the
-- exact orbit/quadrature modules then consume that same action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as H4

signFlipGenerators : List H4.HypercubicGenerator
signFlipGenerators = H4.flip0 ∷ H4.flip1 ∷ H4.flip2 ∷ H4.flip3 ∷ []

adjacentPermutationGenerators : List H4.HypercubicGenerator
adjacentPermutationGenerators = H4.swap01 ∷ H4.swap12 ∷ H4.swap23 ∷ []

signFlipGeneratorCountExact : length signFlipGenerators ≡ 4
signFlipGeneratorCountExact = refl

adjacentPermutationGeneratorCountExact :
  length adjacentPermutationGenerators ≡ 3
adjacentPermutationGeneratorCountExact = refl

-- Every concrete generator is one of the two standard B4 generator families.
data StandardHypercubicGenerator : H4.HypercubicGenerator → Set where
  sign0 : StandardHypercubicGenerator H4.flip0
  sign1 : StandardHypercubicGenerator H4.flip1
  sign2 : StandardHypercubicGenerator H4.flip2
  sign3 : StandardHypercubicGenerator H4.flip3
  perm01 : StandardHypercubicGenerator H4.swap01
  perm12 : StandardHypercubicGenerator H4.swap12
  perm23 : StandardHypercubicGenerator H4.swap23

allGeneratedActionsAreStandardHypercubic :
  ∀ generator → StandardHypercubicGenerator generator
allGeneratedActionsAreStandardHypercubic H4.flip0 = sign0
allGeneratedActionsAreStandardHypercubic H4.flip1 = sign1
allGeneratedActionsAreStandardHypercubic H4.flip2 = sign2
allGeneratedActionsAreStandardHypercubic H4.flip3 = sign3
allGeneratedActionsAreStandardHypercubic H4.swap01 = perm01
allGeneratedActionsAreStandardHypercubic H4.swap12 = perm12
allGeneratedActionsAreStandardHypercubic H4.swap23 = perm23

hypercubicB4GeneratorIdentificationLevel : ProofLevel
hypercubicB4GeneratorIdentificationLevel = machineChecked

-- Literature terminology/method provenance is imported; the repository's
-- orbit action/count/evaluation theorems remain the actual executable content.
hypercubicLatticeSymmetryTerminologyLevel : ProofLevel
hypercubicLatticeSymmetryTerminologyLevel = standardImported

luscherWeiszCoordinateSpaceMethodLevel : ProofLevel
luscherWeiszCoordinateSpaceMethodLevel = standardImported
