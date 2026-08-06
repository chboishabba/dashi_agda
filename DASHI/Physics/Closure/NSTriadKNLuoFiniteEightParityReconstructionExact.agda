module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightParityReconstructionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Qixiang Yang.
-- Title: "Symmetry and Rigidity: Only One Kind of Symmetry Allow Non-Zero
-- Real Symmetric Solution".
-- arXiv:2002.12828v2 (2020).
-- DOI: none assigned in the cited preprint version.
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- PURPOSE
-- Give a literal finite version of Yang's eight-sector parity decomposition.
-- Every scalar function on the reflection group (Z/2Z)^3 is reconstructed as
-- the sum of its eight character sectors.  The theorem uses the normalized
-- Haar/Fourier coefficients already constructed in round seven and proves all
-- eight point identities by exact rational algebra.
--
-- This is a genuine decomposition theorem on the finite reflection carrier.
-- Extending it to arbitrary functions on R^3 or T^3 requires the corresponding
-- reflection actions and function-space convergence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact as Haar

paritySector :
  (Haar.BitTorus3 → ℚ) →
  Haar.BitTorus3 →
  Haar.BitTorus3 →
  ℚ
paritySector value mode point =
  Haar.fourierCoefficient value mode * Haar.character mode point

reconstructEightParitySectors :
  (Haar.BitTorus3 → ℚ) → Haar.BitTorus3 → ℚ
reconstructEightParitySectors value point =
    paritySector value Haar.p000 point
  + paritySector value Haar.p001 point
  + paritySector value Haar.p010 point
  + paritySector value Haar.p011 point
  + paritySector value Haar.p100 point
  + paritySector value Haar.p101 point
  + paritySector value Haar.p110 point
  + paritySector value Haar.p111 point

reconstructionAtoms :
  (Haar.BitTorus3 → ℚ) → List ℚ
reconstructionAtoms value =
    value Haar.p000 ∷ value Haar.p001
  ∷ value Haar.p010 ∷ value Haar.p011
  ∷ value Haar.p100 ∷ value Haar.p101
  ∷ value Haar.p110 ∷ value Haar.p111
  ∷ []

finiteEightParityReconstruction :
  (value : Haar.BitTorus3 → ℚ) →
  (point : Haar.BitTorus3) →
  reconstructEightParitySectors value point ≡ value point
finiteEightParityReconstruction value (Haar.bit3 false false false) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 false false true) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 false true false) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 false true true) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 true false false) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 true false true) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 true true false) =
  solve (reconstructionAtoms value)
finiteEightParityReconstruction value (Haar.bit3 true true true) =
  solve (reconstructionAtoms value)
