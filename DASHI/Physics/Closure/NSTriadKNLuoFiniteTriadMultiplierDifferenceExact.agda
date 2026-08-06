module DASHI.Physics.Closure.NSTriadKNLuoFiniteTriadMultiplierDifferenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Ciprian Foias.
-- Title: "Navier--Stokes Equations".
-- University of Chicago Press, 1988.
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Turn cyclic triad cancellation into an exact multiplier-difference formula.
-- If three transfers satisfy
--
--   T_k + T_p + T_q = 0,
--
-- then every weighted transfer can be anchored at the q-leg:
--
--   sigma_k T_k + sigma_p T_p + sigma_q T_q
--     = (sigma_k-sigma_q) T_k + (sigma_p-sigma_q) T_p.
--
-- This is the Fourier-side commutator identity.  It proves why cancellation
-- must be retained before absolute values and identifies the precise symbol
-- differences from which an inverse frequency could arise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

record CyclicTransferData : Set where
  constructor cyclic-transfer-data
  field
    transferK transferP transferQ : ℚ
    cyclicCancellation : transferK + transferP + transferQ ≡ 0ℚ

open CyclicTransferData public

weightedTransfer :
  CyclicTransferData → ℚ → ℚ → ℚ → ℚ
weightedTransfer transferData sigmaK sigmaP sigmaQ =
  sigmaK * transferK transferData
  + sigmaP * transferP transferData
  + sigmaQ * transferQ transferData

anchoredDifferenceTransfer :
  CyclicTransferData → ℚ → ℚ → ℚ → ℚ
anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ =
  (sigmaK - sigmaQ) * transferK transferData
  + (sigmaP - sigmaQ) * transferP transferData

cyclicMultiplierDifferenceIdentity :
  (transferData : CyclicTransferData) →
  (sigmaK sigmaP sigmaQ : ℚ) →
  weightedTransfer transferData sigmaK sigmaP sigmaQ
  ≡ anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
cyclicMultiplierDifferenceIdentity transferData sigmaK sigmaP sigmaQ =
  begin
    weightedTransfer transferData sigmaK sigmaP sigmaQ
  ≡⟨ solve
       ( sigmaK
       ∷ sigmaP
       ∷ sigmaQ
       ∷ transferK transferData
       ∷ transferP transferData
       ∷ transferQ transferData
       ∷ []) ⟩
    anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
      + sigmaQ
        * (transferK transferData
          + transferP transferData
          + transferQ transferData)
  ≡⟨ cong
       (λ total →
         anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
         + sigmaQ * total)
       (cyclicCancellation transferData) ⟩
    anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
      + sigmaQ * 0ℚ
  ≡⟨ solve
       ( anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
       ∷ sigmaQ
       ∷ []) ⟩
    anchoredDifferenceTransfer transferData sigmaK sigmaP sigmaQ
  ∎

equalMultiplierTriadCancels :
  (transferData : CyclicTransferData) →
  (sigma : ℚ) →
  weightedTransfer transferData sigma sigma sigma ≡ 0ℚ
equalMultiplierTriadCancels transferData sigma =
  begin
    weightedTransfer transferData sigma sigma sigma
  ≡⟨ solve
       ( sigma
       ∷ transferK transferData
       ∷ transferP transferData
       ∷ transferQ transferData
       ∷ []) ⟩
    sigma
      * (transferK transferData
        + transferP transferData
        + transferQ transferData)
  ≡⟨ cong (sigma *_) (cyclicCancellation transferData) ⟩
    sigma * 0ℚ
  ≡⟨ solve (sigma ∷ []) ⟩
    0ℚ
  ∎

constantShiftDoesNotChangeWeightedTransfer :
  (transferData : CyclicTransferData) →
  (sigmaK sigmaP sigmaQ shift : ℚ) →
  weightedTransfer transferData
    (sigmaK + shift)
    (sigmaP + shift)
    (sigmaQ + shift)
  ≡ weightedTransfer transferData sigmaK sigmaP sigmaQ
constantShiftDoesNotChangeWeightedTransfer
  transferData sigmaK sigmaP sigmaQ shift =
  begin
    weightedTransfer transferData
      (sigmaK + shift)
      (sigmaP + shift)
      (sigmaQ + shift)
  ≡⟨ solve
       ( sigmaK
       ∷ sigmaP
       ∷ sigmaQ
       ∷ shift
       ∷ transferK transferData
       ∷ transferP transferData
       ∷ transferQ transferData
       ∷ []) ⟩
    weightedTransfer transferData sigmaK sigmaP sigmaQ
      + shift
        * (transferK transferData
          + transferP transferData
          + transferQ transferData)
  ≡⟨ cong
       (λ total →
         weightedTransfer transferData sigmaK sigmaP sigmaQ
         + shift * total)
       (cyclicCancellation transferData) ⟩
    weightedTransfer transferData sigmaK sigmaP sigmaQ
      + shift * 0ℚ
  ≡⟨ solve
       ( weightedTransfer transferData sigmaK sigmaP sigmaQ
       ∷ shift
       ∷ []) ⟩
    weightedTransfer transferData sigmaK sigmaP sigmaQ
  ∎
