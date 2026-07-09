module DASHI.Physics.ClaySupportingProfileSchurPipeline where

------------------------------------------------------------------------
-- Elementary, fully-proved profile Schur pipeline (NS §III).
--
-- Companion to `...ClaySupportingSchurOperatorBound`,
-- `...ClaySupportingForcedTailRowColumnBounds` and
-- `...ClaySupportingResidualDomination`.  Every declaration here is a
-- genuine Agda proof over concrete ℕ data: there are NO `postulate`s
-- and NO added axioms.
--
-- This module packages the four-profile Schur-test + recombination
-- pipeline into a clean record-and-theorem interface.  The pipeline
-- stages are:
--
--   Stage 1 — per-profile Schur test:
--     Given profile α with operator norm ‖M_α‖, row sum r_α and
--     column sum c_α, the Schur test supplies
--       ‖M_α‖² ≤ r_α·c_α.
--     Combined with the cleared N⁻² row/column bounds
--       (N+1)²·r_α ≤ C_α,   (N+1)²·c_α ≤ C_α,
--     the per-profile operator bound follows:
--       (N+1)²·‖M_α‖ ≤ C_α.
--
--   Stage 2 — subadditivity recombination:
--     The total kernel M = Σ_α M_α satisfies ‖M‖ ≤ Σ_α ‖M_α‖
--     (operator norm subadditivity), so
--       (N+1)²·‖M‖ ≤ Σ_α C_α.
--
-- The record types `SingleProfileInput` and `FourProfileN2Inputs`
-- document what each profile must supply.  The theorem
-- `profileSchurPipeline` (functionally identical to
-- `ClaySupportingSchurOperatorBound.fourProfileSchurBound`) delivers
-- the total bound.
--
-- Honesty boundary (unchanged and deliberate): this does NOT discharge
-- any open analytic Clay leaf.  The per-profile Schur tests and the
-- operator-norm subadditivity are genuine analytic facts about ℓ²
-- operators (the former is the Schur test, the latter is the triangle
-- inequality).  The per-profile N⁻² row/column bounds are the open
-- inputs from `...ForcedTailRowColumnBounds` and
-- `...ResidualDomination` under their own open hypotheses.  What is
-- proved here is that once those 16 hypotheses are all supplied, the
-- total weighted-Schur operator bound follows by the pipeline algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.ClaySupportingSchurOperatorBound
  using (fourProfileSchurBound)

------------------------------------------------------------------------
-- §1.  Per-profile input record.
--
-- Each profile α contributes its operator norm, its row and column sum
-- quantities, its cleared N⁻² constant C_α, and the two analytic facts
-- that tie them together.

record SingleProfileInput (N C : ℕ) : Set where
  field
    op    : ℕ            -- profile operator norm ‖M_α‖
    r c   : ℕ            -- row-sum and column-sum (Schur test quantities)
    -- Schur test:  ‖M_α‖·‖M_α‖ ≤ r_α·c_α
    schurTest : op * op ≤ r * c
    -- Cleared N⁻² row/column bounds
    rowN2 : (suc N * suc N) * r ≤ C
    colN2 : (suc N * suc N) * c ≤ C

------------------------------------------------------------------------
-- §2.  Four-profile input record.
--
-- Packages all four profiles with type-level documentation of which
-- C constant each profile contributes.

record FourProfileN2Inputs (N : ℕ) (CFT CAdv CTr CRes : ℕ) : Set where
  field
    FT   : SingleProfileInput N CFT
    adv  : SingleProfileInput N CAdv
    tr   : SingleProfileInput N CTr
    res  : SingleProfileInput N CRes

------------------------------------------------------------------------
-- §3.  Pipeline theorem.
--
-- Functionally identical to `fourProfileSchurBound`.  The pipeline name
-- documents that this is the end-to-end flow from per-profile N⁻² row/
-- column inputs (Stage 1) through subadditivity (Stage 2) to the total
-- weighted-Schur operator bound.

profileSchurPipeline :
  (opTot opFT opAdv opTr opRes N : ℕ)
  (rFT cFT rAdv cAdv rTr cTr rRes cRes : ℕ)
  (CFT CAdv CTr CRes : ℕ) →
  opTot ≤ ((opFT + opAdv) + opTr) + opRes →
  opFT  * opFT  ≤ rFT  * cFT  →
  opAdv * opAdv ≤ rAdv * cAdv →
  opTr  * opTr  ≤ rTr  * cTr  →
  opRes * opRes ≤ rRes * cRes →
  (suc N * suc N) * rFT  ≤ CFT  → (suc N * suc N) * cFT  ≤ CFT  →
  (suc N * suc N) * rAdv ≤ CAdv → (suc N * suc N) * cAdv ≤ CAdv →
  (suc N * suc N) * rTr  ≤ CTr  → (suc N * suc N) * cTr  ≤ CTr  →
  (suc N * suc N) * rRes ≤ CRes → (suc N * suc N) * cRes ≤ CRes →
  (suc N * suc N) * opTot ≤ ((CFT + CAdv) + CTr) + CRes
profileSchurPipeline = fourProfileSchurBound
