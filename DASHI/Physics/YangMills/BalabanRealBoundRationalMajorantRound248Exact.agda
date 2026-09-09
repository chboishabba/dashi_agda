{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRealBoundRationalMajorantRound248Exact where

------------------------------------------------------------------------
-- ROUND248 / STANDARD ANALYSIS: FINITE REAL BOUND -> RATIONAL MAJORANT
--
-- Source estimates are naturally real-valued; the Row-A bookkeeping is exact
-- rational arithmetic.  Choosing a rational above a finite real number is an
-- Archimedean property of ℝ, not a Yang--Mills estimate.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed

record ArchimedeanRationalMajorant
    (embedding : Embed.OrderedRationalRealRingEmbedding) : Set₁ where
  field
    majorant : ℝ → ℚ

    majorizes : ∀ bound →
      bound ≤ℝ Embed.embed embedding (majorant bound)

    nonnegativeMajorant : ∀ {bound} →
      0ℝ ≤ℝ bound →
      0ℚ ≤ majorant bound

open ArchimedeanRationalMajorant public

archimedeanRationalMajorantLevel : ProofLevel
archimedeanRationalMajorantLevel = standardImported

-- This module contains no YM-specific theorem.  A consumer must separately
-- prove that its real source estimate is the literal physical quantity being
-- bounded; this authority only converts the scalar bound carrier.
realBoundToRationalMajorantCompilerLevel : ProofLevel
realBoundToRationalMajorantCompilerLevel = machineChecked
