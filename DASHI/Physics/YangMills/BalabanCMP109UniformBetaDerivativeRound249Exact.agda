{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109UniformBetaDerivativeRound249Exact where

------------------------------------------------------------------------
-- ROUND249 / CMP109 UNIFORM BETA-DERIVATIVE SOURCE AUTHORITY
--
-- CMP109 Sect.1, after (1.22), states that beta_{j+1}(g_j) is smooth (or
-- analytic) on a positive interval and uniformly bounded there together with
-- all derivatives.  This is published source authority.
--
-- The YM-specific seam is NOT proving differentiability again.  It is binding
-- the repository's selected local beta map to that literal source beta on the
-- same scale/history.  Once bound, R248 converts a finite real source bound to
-- an exact nonnegative rational Row-A constant.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanRealBoundRationalMajorantRound248Exact as Majorant

record CMP109UniformBetaDerivativeSource
    (embedding : Embed.OrderedRationalRealRingEmbedding)
    (arch : Majorant.ArchimedeanRationalMajorant embedding) : Set₁ where
  field
    realDerivativeBound : ℝ
    realDerivativeBoundNonnegative : 0ℝ ≤ℝ realDerivativeBound

    -- Consumer-indexed source semantics: this proposition means that the
    -- selected repository beta map is the literal CMP109 beta_{j+1}(g_j) on the
    -- source interval, and that its first derivative is bounded by
    -- `realDerivativeBound` uniformly in the declared cutoff/scale family.
    SelectedBetaIsLiteralCMP109 : Set
    selectedBetaIsLiteralCMP109 : SelectedBetaIsLiteralCMP109

open CMP109UniformBetaDerivativeSource public

rationalDerivativeBound :
  ∀ {embedding arch} →
  CMP109UniformBetaDerivativeSource embedding arch → ℚ
rationalDerivativeBound {arch = arch} source =
  Majorant.majorant arch (realDerivativeBound source)

rationalDerivativeBoundNonnegative :
  ∀ {embedding arch}
    (source : CMP109UniformBetaDerivativeSource embedding arch) →
  0ℚ ≤ rationalDerivativeBound source
rationalDerivativeBoundNonnegative {arch = arch} source =
  Majorant.nonnegativeMajorant arch (realDerivativeBoundNonnegative source)

cmp109UniformBetaDerivativePublishedSourceLevel : ProofLevel
cmp109UniformBetaDerivativePublishedSourceLevel = standardImported

cmp109RealToRationalDerivativeCompilerLevel : ProofLevel
cmp109RealToRationalDerivativeCompilerLevel = machineChecked

-- Same-object repository/source binding remains physical.  The derivative
-- existence/uniform boundedness itself is not a new Row-A analytic theorem.
literalSelectedBetaIsCMP109SourceLevel : ProofLevel
literalSelectedBetaIsCMP109SourceLevel = conditional
