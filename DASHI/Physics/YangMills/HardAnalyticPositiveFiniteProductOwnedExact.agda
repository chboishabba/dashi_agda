module DASHI.Physics.YangMills.HardAnalyticPositiveFiniteProductOwnedExact where

------------------------------------------------------------------------
-- OWNED REPLACEMENT FOR THE HARD-ANALYTIC FINITE-PRODUCT PLACEHOLDER
--
-- `HardAnalyticDischargeProgram` defines the same binary positivity law as
-- `GraphCombinatorics.PositiveProduct`, but still carries an opaque
-- `PositiveFiniteProduct : Set` postulate.  The graph owner already proves the
-- actual recursive finite-list theorem.  This file pins that same-type donor
-- explicitly so the opaque placeholder can be removed rather than propagated.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _<ℝ_; 0ℝ)

import DASHI.Physics.YangMills.GraphCombinatorics as Graph
import DASHI.Physics.YangMills.HardAnalyticDischargeProgram as Hard

hardAndGraphPositiveProductSameType :
  Hard.PositiveProduct → Graph.PositiveProduct
hardAndGraphPositiveProductSameType h = h

hardPositiveFiniteProductOwned :
  Hard.PositiveProduct →
  (xs : List ℝ) →
  Graph.AllPositive xs →
  0ℝ <ℝ Graph.prod xs
hardPositiveFiniteProductOwned positiveProduct xs allPositive =
  Graph.lemmaPositiveFiniteProduct
    (hardAndGraphPositiveProductSameType positiveProduct)
    xs
    allPositive

------------------------------------------------------------------------
-- MAX-CUT
--
-- The finite-product positivity fact is not a genuine Yang--Mills analytic
-- leaf.  It is already recursively proved on the exact real/list carrier.
-- Remaining P08/P11 work must therefore start after this theorem, at the
-- actual p0/Gaussian/reference-weight/absorption dependencies rather than at
-- an opaque finite-product placeholder.
------------------------------------------------------------------------
