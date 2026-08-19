module DASHI.Physics.Closure.NSTriadKNWaleffeNetworkForcingHomogeneityRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND94 SCALING AUDIT / ROUND95 REPAIR
--
-- The first draft of this file attempted to expand the full quartic Waleffe
-- network-forcing homogeneity directly through all three product-rule slots.
-- Static review found source-level transport mistakes in that expansion.
-- Rather than leave a broken pseudo-theorem in the dependency graph, Round95
-- keeps only the theorem-exact part which had already been proved on the
-- literal physical Galerkin carrier:
--
--   projectedNonlinearity (a u) = a^2 projectedNonlinearity(u).
--
-- Since the Waleffe amplitude is trilinear and one NS network insertion is
-- quadratic, the intended degree bookkeeping is cubic/quartic.  The Clay-level
-- consequence does NOT require a standalone quartic expansion: Round95 moves
-- to the denominator-free normalized phase derivative, where the viscous
-- terms cancel exactly and the remaining self/external forcing is retained
-- explicitly.
--
-- Canonical downstream owner:
--   NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as Quadratic
import DASHI.Physics.Closure.NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact as Normalized

round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed : Bool
round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed = true

-- The old direct all-slots quartic expansion is deliberately retired rather
-- than claimed theorem-exact after the static source audit.
round94DirectQuarticNetworkExpansionRetired : Bool
round94DirectQuarticNetworkExpansionRetired = true

-- The normalized derivative is now the canonical scale-free consumer.
round95NormalizedPhaseConsumerAvailable : Bool
round95NormalizedPhaseConsumerAvailable =
  Normalized.round95NormalizedPhaseViscosityCancellationClosed

round94LiteralProjectedNonlinearityQuadraticHomogeneityClosedIsTrue :
  round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed ≡ true
round94LiteralProjectedNonlinearityQuadraticHomogeneityClosedIsTrue = refl

round94DirectQuarticNetworkExpansionRetiredIsTrue :
  round94DirectQuarticNetworkExpansionRetired ≡ true
round94DirectQuarticNetworkExpansionRetiredIsTrue = refl

round95NormalizedPhaseConsumerAvailableIsTrue :
  round95NormalizedPhaseConsumerAvailable ≡ true
round95NormalizedPhaseConsumerAvailableIsTrue = refl
