module DASHI.Algebra.Quantum.SaxonQFiniteQutritLogicalEncodingExact where

-- Source-specific *candidate* logical subspace for a spin-one carrier.
-- Reuses the existing repository qutrit basis and Dirac pairing.
-- The selected levels are a mathematical convention, NOT a measured
-- assignment of a SAXON Q nitrogen nuclear-spin computational register.
-- Attribution: FiniteQutrit is earlier DASHI work; this restricted
-- embedding and decoding receipt: Johl Brown and OpenAI assistant,
-- 2026-10-26. Experiment: Gemsheim et al., arXiv:2609.13022.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Quantum.FiniteQutrit as Q
import DASHI.Algebra.Quantum.Dirac as Dirac

data LogicalLevel : Set where
  l0 : LogicalLevel
  l1 : LogicalLevel

encode : LogicalLevel → Q.QutritBasis
encode l0 = Q.ket0
encode l1 = Q.ket1

-- A decoder must track leakage. It cannot silently map the third
-- qutrit level into the computational two-dimensional subspace.
data DecodeResult : Set where
  accepted : LogicalLevel → DecodeResult
  leaked : DecodeResult

decode : Q.QutritBasis → DecodeResult
decode Q.ket0 = accepted l0
decode Q.ket1 = accepted l1
decode Q.ket2 = leaked

decodeEncode : ∀ x → decode (encode x) ≡ accepted x
decodeEncode l0 = refl
decodeEncode l1 = refl

thirdLevelIsLeakage : decode Q.ket2 ≡ leaked
thirdLevelIsLeakage = refl

-- Explicit *basis*-level no-aliasing result (not an isometry of
-- arbitrary complex superpositions).
logicalBasisDistinct : encode l0 ≡ encode l1 → Q.ket0 ≡ Q.ket1
logicalBasisDistinct p = p

-- Existing Dirac kernel certifies orthogonality of selected basis.
logicalBasisOrthogonal :
  Q.basisPair (Dirac.bra (encode l0))
              (Dirac.ket (encode l1))
  ≡ Q.amp0
logicalBasisOrthogonal = refl

-- This file proves only finite basis-level encoding/decoding.
-- Full unitary isometry, density matrices, pulse leakage bounds and
-- manufacturer-specific basis identification are still open.
