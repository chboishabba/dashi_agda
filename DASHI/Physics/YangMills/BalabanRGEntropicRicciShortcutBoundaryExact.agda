module DASHI.Physics.YangMills.BalabanRGEntropicRicciShortcutBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Matthias Erbar and Max Fathi,
-- "Poincare, modified logarithmic Sobolev and isoperimetric inequalities for
-- Markov chains with non-negative Ricci curvature",
-- Journal of Functional Analysis 274 (2018), 3056--3089.
-- DOI: 10.1016/j.jfa.2018.03.011.
--
-- DASHI CONTRIBUTION
--
-- Record the curvature route as a possible SHORTCUT, not a hidden promotion.
-- Erbar--Fathi proves diameter-controlled functional inequalities for suitable
-- finite Markov chains with non-negative entropic Ricci curvature.  Therefore
-- a cutoff-uniform curvature/diameter theorem for the literal RG chain could
-- bypass a separate hand-built conductance estimate.
--
-- But neither non-negative curvature nor a cutoff-uniform diameter bound is a
-- consequence of the existence of a positive neighbour system.  They remain
-- separate physical producer theorems.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record RGEntropicRicciCandidate : Set where
  field
    curvatureLowerBound : ℚ
    diameterUpperBound : ℚ
    curvatureNonnegative : 0ℚ ≤ curvatureLowerBound
    diameterNonnegative : 0ℚ ≤ diameterUpperBound
open RGEntropicRicciCandidate public

erbarFathiNonnegativeRicciFunctionalInequalitiesLevel : ProofLevel
erbarFathiNonnegativeRicciFunctionalInequalitiesLevel = standardImported

literalRGEntropicRicciLowerBoundLevel : ProofLevel
literalRGEntropicRicciLowerBoundLevel = conditional

cutoffUniformRGDiameterUpperBoundLevel : ProofLevel
cutoffUniformRGDiameterUpperBoundLevel = conditional

-- This route cannot erase the two-metric theorem: the diameter in the Markov
-- transport metric still has to be related to the physical observable metric
-- uniformly in lattice spacing before a Clay-scale physical gap follows.
curvatureDiameterToPhysicalMetricComparisonLevel : ProofLevel
curvatureDiameterToPhysicalMetricComparisonLevel = conditional
