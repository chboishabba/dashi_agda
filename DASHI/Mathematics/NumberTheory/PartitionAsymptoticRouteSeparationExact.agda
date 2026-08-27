module DASHI.Mathematics.NumberTheory.PartitionAsymptoticRouteSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- G. H. Hardy and S. Ramanujan,
-- "Asymptotic Formulae in Combinatory Analysis",
-- Proceedings of the London Mathematical Society (2) 17 (1918), 75--115.
-- DOI: 10.1112/plms/s2-17.1.75.
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- D. J. Newman,
-- "The Evaluation of the Constant in the Formula for the Number of
-- Partitions of n", American Journal of Mathematics 73 (1951), 599--601.
--
-- HISTORICAL CLAIM BOUNDARY
--
-- Hardy--Ramanujan obtain the sharp asymptotic by complex-analytic/circle
-- machinery.  Erdos gives an elementary route to the exponential shape with
-- a positive multiplicative constant but does not determine that constant.
-- Newman subsequently determines the constant elementarily.
--
-- DASHI CONTRIBUTION
--
-- Make proof route and achieved resolution separate types.  In particular,
-- an elementary proof of the growth shape cannot be silently relabelled as a
-- proof of the sharp Hardy--Ramanujan constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Route identity.

data PartitionAsymptoticRoute : Set where
  hardyRamanujanCircleRoute : PartitionAsymptoticRoute
  erdosElementaryRoute : PartitionAsymptoticRoute
  newmanElementaryConstantRoute : PartitionAsymptoticRoute

circleRouteIsNotErdosRoute :
  hardyRamanujanCircleRoute ≡ erdosElementaryRoute → ⊥
circleRouteIsNotErdosRoute ()

erdosRouteIsNotNewmanRoute :
  erdosElementaryRoute ≡ newmanElementaryConstantRoute → ⊥
erdosRouteIsNotNewmanRoute ()

circleRouteIsNotNewmanRoute :
  hardyRamanujanCircleRoute ≡ newmanElementaryConstantRoute → ⊥
circleRouteIsNotNewmanRoute ()

------------------------------------------------------------------------
-- Resolution identity.

data PartitionAsymptoticResolution : Set where
  logarithmicLeadingGrowth : PartitionAsymptoticResolution
  exponentialShapePositiveUnknownConstant : PartitionAsymptoticResolution
  sharpHardyRamanujanConstant : PartitionAsymptoticResolution

routeResolution : PartitionAsymptoticRoute → PartitionAsymptoticResolution
routeResolution hardyRamanujanCircleRoute = sharpHardyRamanujanConstant
routeResolution erdosElementaryRoute = exponentialShapePositiveUnknownConstant
routeResolution newmanElementaryConstantRoute = sharpHardyRamanujanConstant

hardyRamanujanResolutionIsSharp :
  routeResolution hardyRamanujanCircleRoute ≡ sharpHardyRamanujanConstant
hardyRamanujanResolutionIsSharp = refl

erdosResolutionLeavesConstantOpen :
  routeResolution erdosElementaryRoute
  ≡ exponentialShapePositiveUnknownConstant
erdosResolutionLeavesConstantOpen = refl

newmanResolutionIsSharp :
  routeResolution newmanElementaryConstantRoute ≡ sharpHardyRamanujanConstant
newmanResolutionIsSharp = refl

erdosResolutionIsNotSharp :
  routeResolution erdosElementaryRoute ≡ sharpHardyRamanujanConstant → ⊥
erdosResolutionIsNotSharp ()

------------------------------------------------------------------------
-- Formula labels are documentation only; theorem ownership remains in the
-- typed obligations below rather than in String equality.

hardyRamanujanFormula : String
hardyRamanujanFormula =
  "p(n) ~ exp(pi * sqrt(2*n/3)) / (4*n*sqrt(3))"

erdosFormulaShape : String
erdosFormulaShape =
  "p(n) ~ alpha * exp(pi * sqrt(2*n/3)) / n, for some alpha > 0"

record PartitionAsymptoticRouteBoundary : Set₁ where
  field
    hardyRamanujanCircleMethod : Set
    hardyRamanujanSharpAsymptotic : Set

    erdosPartitionIdentity : Set
    erdosElementaryUpperLowerBounds : Set
    erdosPositiveConstantExistence : Set

    newmanElementaryConstantEvaluation : Set

    -- This explicitly records that the two routes may converge on the same
    -- final asymptotic theorem without becoming the same proof route.
    commonSharpConclusion : Set

open PartitionAsymptoticRouteBoundary public
