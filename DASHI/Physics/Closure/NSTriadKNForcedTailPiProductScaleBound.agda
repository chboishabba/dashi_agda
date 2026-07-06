module DASHI.Physics.Closure.NSTriadKNForcedTailPiProductScaleBound where

----------------------------------------------------------------------
-- Forced-tail π-product scale bound (Lemma 2).
--
-- This module documents the analytic estimate that connects the exact
-- forced-tail triad weight formula to the classwise scaling target:
--
--   τ ∈ I^FT_{N,c}  ⇒  m_N(τ) ≤ D_FT(N,c)^{-1}
--
-- The triad weight formula (from the repeated-pair incidence kernel):
--
--   m_N(τ) = (√(π_i π_j π_l)/3) · max(cos(φ_i+φ_j-φ_l), 0)
--
-- where π_i, π_j, π_l are the spectral interaction eigenvalues at the
-- three triad wavevectors (k, p, q).
--
-- Since max(cos,0) ≤ 1 trivially, the bridge reduces to:
--
--   √(π_i π_j π_l) ≤ 3 · D_FT(N,c)^{-1}
--
-- Squaring:
--
--   π_i π_j π_l ≤ 9 · D_FT(N,c)^{-2}
--
-- Classwise targets (multiplicative form):
--
--   tailEnd:    π_i π_j π_l ≤ 9 · N^{-4}
--   nearTail:   π_i π_j π_l ≤ 9 · N^{-6}
--   transition: π_i π_j π_l ≤ 9 · N^{-8}
--   degenerate: π_i π_j π_l ≤ 9 · N^{-4}
--
-- In ℕ-scaled form (multiply by D_FT(N,c)² = N^{4+2a_c}):
--
--   tailEnd:    (π_i π_j π_l) · N⁴ ≤ 9
--   nearTail:   (π_i π_j π_l) · N⁶ ≤ 9
--   transition: (π_i π_j π_l) · N⁸ ≤ 9
--   degenerate: (π_i π_j π_l) · N⁴ ≤ 9
--
-- Postulate status:
--   The π-values and their bounds are NOT yet proved inside Agda.
--   They are postulated from the external NS spectral analysis
--   (forced-tail class hypotheses: tail separation, shell scaling,
--   projection normalisation).  The postulates are defined in
--   NSTriadKNForcedTailConcreteIncidenceType.agda §7.
--
--   The bridge theorem (Lemma 1) is proved structurally in
--   ConcreteIncidenceType §8 using these postulates.
--   The analytic heart is therefore the inhabitation of
--   piProductForcedTailScaleBound, which requires a concrete
--   spectral decomposition of the forced-tail triad configuration.

-- Re-export the key postulates from the concrete incidence module
-- where they are defined alongside the forced-tail triad incidence.
open import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType
  using ( triadPiScaledFactor
        ; piProductForcedTailScaleBound
        ; cosPositivePartFactor
        ; cosPositivePartBound
        ; actualKernelBoundedByScaledProxy
        ; actualForcedTailKernelWeight
        )
  public

-- Marker: the π-product scale bound is currently a postulate.
-- Set to true once the spectral analysis is formalised.
open import Agda.Builtin.Bool using (Bool; false)
piProductScaleBoundAvailable : Bool
piProductScaleBoundAvailable = false
