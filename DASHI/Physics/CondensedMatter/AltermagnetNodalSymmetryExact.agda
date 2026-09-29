module DASHI.Physics.CondensedMatter.AltermagnetNodalSymmetryExact where

------------------------------------------------------------------------
-- A finite *candidate* illustration of nodal spin degeneracy versus
-- momentum-selective spin splitting.  There is no interpolation, DFT
-- parameter fitting, or claim that the actual symmetry generator of
-- Co1/4TaSe2 has been represented here.
--
-- Source roles kept separate:
-- Mandujano et al. 2024: experimental nuclear space group P63/mmc,
--   type-A antiferromagnetism, and neutron diffraction (reported TN 173 K).
--   https://www.nist.gov/publications/itinerant-type-antiferromagnet-order-co14tase2
-- Sprague et al. 2026: ARPES/DFT spin splitting and TN 178 K.
--   DOI 10.1038/s41467-026-76784-x
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Empty using (⊥)

import DASHI.Physics.CondensedMatter.AltermagnetCoQuarterTaSeTwo as AM

data SampleK : Set where
  nodalA nodalB splitA splitB : SampleK

-- An abstract momentum-space operation exchanges the two split sectors,
-- and separately exchanges two nodal sectors.
mirrorK : SampleK → SampleK
mirrorK nodalA = nodalB
mirrorK nodalB = nodalA
mirrorK splitA = splitB
mirrorK splitB = splitA

mirrorKInvolution : (k : SampleK) → mirrorK (mirrorK k) ≡ k
mirrorKInvolution nodalA = refl
mirrorKInvolution nodalB = refl
mirrorKInvolution splitA = refl
mirrorKInvolution splitB = refl

-- Artificial integer energies for a *logical* model; no energy units.
-- Degeneracy at the nodal samples; opposed splittings at the other pair.
level : SampleK → AM.Spin → Nat
level nodalA AM.up = zero
level nodalA AM.down = zero
level nodalB AM.up = zero
level nodalB AM.down = zero
level splitA AM.up = zero
level splitA AM.down = suc zero
level splitB AM.up = suc zero
level splitB AM.down = zero

spinSpaceCovariance : (k : SampleK) (s : AM.Spin) →
  level (mirrorK k) (AM.reverseSpin s) ≡ level k s
spinSpaceCovariance nodalA AM.up = refl
spinSpaceCovariance nodalA AM.down = refl
spinSpaceCovariance nodalB AM.up = refl
spinSpaceCovariance nodalB AM.down = refl
spinSpaceCovariance splitA AM.up = refl
spinSpaceCovariance splitA AM.down = refl
spinSpaceCovariance splitB AM.up = refl
spinSpaceCovariance splitB AM.down = refl

nodalAEqual : level nodalA AM.up ≡ level nodalA AM.down
nodalAEqual = refl

nodalBEqual : level nodalB AM.up ≡ level nodalB AM.down
nodalBEqual = refl

-- Agda's empty pattern rules out equating distinct Nat constructors.
splitANotEqual : level splitA AM.up ≡ level splitA AM.down → ⊥
splitANotEqual ()

splitBNotEqual : level splitB AM.up ≡ level splitB AM.down → ⊥
splitBNotEqual ()
