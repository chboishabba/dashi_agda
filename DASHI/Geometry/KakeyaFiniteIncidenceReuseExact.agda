module DASHI.Geometry.KakeyaFiniteIncidenceReuseExact where

------------------------------------------------------------------------
-- PROVENANCE AND CLAIM BOUNDARY
--
-- Historical mathematics: A.-L. Cauchy and H. A. Schwarz (finite
-- Cauchy--Schwarz); T. Wolff (Kakeya tube concentration framework);
-- L. Guth (graininess and polynomial-method work); H. Wang and
-- J. Zahl, "Volume estimates for unions of convex sets, and the
-- Kakeya set conjecture in three dimensions", arXiv:2502.17655 (2025).
-- Guth--Wang--Zahl, "A streamlined proof of the Kakeya set conjecture
-- in R^3", arXiv:2601.14411 (2026).
--
-- Repository-original contribution: exact naming/transport of already
-- proved rational finite incidence and Gram-defect inequalities.
--
-- IMPORTANT: This is finite algebra only. It does NOT establish
-- physical Euclidean delta-tube geometry, the Convex Wolff Axioms,
-- multiscale uniformity, Hausdorff/Minkowski dimension, maximal
-- estimates, or the Wang--Zahl theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

-- Each pair carries a rational occupancy weight and a rational
-- multiplicity. For geometric applications a separate adapter must
-- prove that these are the intended common-cell tube incidences.
Incidence : Set
Incidence = L2.Pair

FiniteIncidences : Set
FiniteIncidences = List Incidence

totalIncidence : FiniteIncidences → ℚ
totalIncidence = L2.pairDot

occupiedWeight : FiniteIncidences → ℚ
occupiedWeight = L2.leftNormSquared

overlapEnergy : FiniteIncidences → ℚ
overlapEnergy = L2.rightNormSquared

incidenceGramDefect : FiniteIncidences → ℚ
incidenceGramDefect = L2.gramDefect

-- Exact algebraic identity, stronger than the resulting inequality.
-- The defect is explicitly a sum of squares, not an assumed bound.
finiteIncidenceGramIdentity :
  ∀ data →
  occupiedWeight data * overlapEnergy data
  ≡ L2.square (totalIncidence data) + incidenceGramDefect data
finiteIncidenceGramIdentity = L2.finiteGramIdentity

finiteIncidenceGramDefectNonnegative :
  ∀ data → Data.Rational.Base.0ℚ ≤ incidenceGramDefect data
finiteIncidenceGramDefectNonnegative = L2.gramDefectNonnegative

-- This is the squared finite union/second-moment inequality. Turning
-- occupiedWeight into literal union volume requires independent cell
-- disjointness and coverage proofs.
finiteIncidenceSecondMoment :
  ∀ data →
  L2.square (totalIncidence data)
    ≤ occupiedWeight data * overlapEnergy data
finiteIncidenceSecondMoment = L2.finiteCauchySchwarzSquared

-- Reuse existing restricted-family argument for a selected subfamily.
-- Restriction monotonicity is *explicitly* a witness and is not inferred
-- from arbitrary coordinatewise deletions.
finiteRestrictedIncidenceSecondMoment :
  ∀ {full restricted} →
  L2.RestrictedPairFamily full restricted →
  L2.square (totalIncidence restricted)
    ≤ occupiedWeight full * overlapEnergy full
finiteRestrictedIncidenceSecondMoment =
  L2.finiteRestrictedCauchySchwarzSquared

record GeometricIncidenceAdapter : Set₁ where
  field
    incidences : FiniteIncidences
    -- Selected geometric data must be identified with the exact
    -- finite rational model, not merely named after it.
    geometricTotal : ℚ
    geometricUnionWeight : ℚ
    geometricOverlapEnergy : ℚ
    totalIdentified : geometricTotal ≡ totalIncidence incidences
    unionIdentified : geometricUnionWeight ≡ occupiedWeight incidences
    overlapIdentified : geometricOverlapEnergy ≡ overlapEnergy incidences

open GeometricIncidenceAdapter public

-- A precise interface: if an actual finite tube discretisation supplies
-- the three identifications, the quantitative second-moment inequality
-- follows with no additional analytic postulate.
geometricAdapterSecondMoment :
  ∀ adapter →
  L2.square (geometricTotal adapter)
    ≤ geometricUnionWeight adapter * geometricOverlapEnergy adapter
geometricAdapterSecondMoment adapter
  rewrite totalIdentified adapter
        | unionIdentified adapter
        | overlapIdentified adapter =
  finiteIncidenceSecondMoment (incidences adapter)

finiteIncidenceAlgebraFromPriorArt : Bool
finiteIncidenceAlgebraFromPriorArt = true

finiteIncidenceAlgebraFromPriorArtCorrect :
  finiteIncidenceAlgebraFromPriorArt ≡ true
finiteIncidenceAlgebraFromPriorArtCorrect = refl

geometricKakeyaConcentrationEstablishedHere : Bool
geometricKakeyaConcentrationEstablishedHere = false

geometricKakeyaConcentrationEstablishedHereCorrect :
  geometricKakeyaConcentrationEstablishedHere ≡ false
geometricKakeyaConcentrationEstablishedHereCorrect = refl
