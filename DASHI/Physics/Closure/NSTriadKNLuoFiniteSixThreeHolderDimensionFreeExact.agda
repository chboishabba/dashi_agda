module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderDimensionFreeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality on a finite counting-measure space.
-- Repository-original radical-free specialization; no DOI is assigned.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Promote the explicit nested-sum arbitrary-list theorem as the uniform finite
-- carrier used by the Galerkin lane. For every finite list of nonnegative
-- pairs,
--
--   (sum_i (a_i b_i)^2)^3
--     <= (sum_i a_i^6) (sum_i b_i^3)^2.
--
-- The constant is one and is independent of the list cardinality. The older
-- eight-point estimate with factor 64 remains only a regression theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (_*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderConstantOneV2Exact as Holder

finiteSixThreeHolderConstantOne :
  (items : List Holder.NonnegativePair) →
  Holder.cube (Holder.sumBy Holder.productMass items)
  ≤ Holder.sumBy Holder.leftSixthMass items
    * (Holder.sumBy Holder.rightCubeMass items
      * Holder.sumBy Holder.rightCubeMass items)
finiteSixThreeHolderConstantOne =
  Holder.finiteSixThreeHolderRadicalFree
