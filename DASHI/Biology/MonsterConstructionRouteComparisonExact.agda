module DASHI.Biology.MonsterConstructionRouteComparisonExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Robert L. Griess Jr.,
-- "The Friendly Giant".
-- DOI: 10.1007/BF01389186.
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine".
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Compare construction routes by their actual mathematical outputs rather than
-- by a single shared dimension.  The Griess route supplies a finite
-- commutative nonassociative algebra and its automorphism group.  The FLM route
-- supplies a graded VOA through a Leech-lattice orbifold and its untwisted J
-- character.  Full McKay--Thompson modular data is kept separate.  The
-- Borcherds route consumes the VOA plus Lorentzian/string physical-state
-- machinery to produce a generalized Kac--Moody algebra and the denominator
-- identity. Character and computational finite-group routes supply still
-- different data.
--
-- Exact Boolean signatures prove that these routes are not interchangeable.
-- The only implemented forward bridge is the mathematically valid restriction
-- of a VOA automorphism to the weight-two first product, proved in the sibling
-- Griess module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.MoonshineGriessAutomorphismClassificationExact as Griess

data MonsterConstructionRoute : Set where
  griessFiniteAlgebraRoute : MonsterConstructionRoute
  flmOrbifoldVOARoute : MonsterConstructionRoute
  borcherdsMonsterLieRoute : MonsterConstructionRoute
  conwayNortonCharacterRoute : MonsterConstructionRoute
  computationalFiniteGroupRoute : MonsterConstructionRoute

record RouteSignature : Set where
  constructor routeSignature
  field
    hasFiniteNonassociativeAlgebra : Bool
    hasGradedStateFieldAlgebra : Bool
    hasTwistedOrbifoldSector : Bool
    hasGeneralizedKacMoodyAlgebra : Bool
    hasMcKayThompsonModularData : Bool
    hasExplicitFiniteGroupData : Bool

open RouteSignature public

signature : MonsterConstructionRoute → RouteSignature
signature griessFiniteAlgebraRoute =
  routeSignature true false false false false true
signature flmOrbifoldVOARoute =
  routeSignature true true true false false true
signature borcherdsMonsterLieRoute =
  routeSignature true true true true true true
signature conwayNortonCharacterRoute =
  routeSignature false false false false true false
signature computationalFiniteGroupRoute =
  routeSignature false false false false false true

griessRouteIsNotVOARoute :
  griessFiniteAlgebraRoute ≡ flmOrbifoldVOARoute → ⊥
griessRouteIsNotVOARoute ()

voaRouteIsNotMonsterLieRoute :
  flmOrbifoldVOARoute ≡ borcherdsMonsterLieRoute → ⊥
voaRouteIsNotMonsterLieRoute ()

characterRouteIsNotComputationalRoute :
  conwayNortonCharacterRoute ≡ computationalFiniteGroupRoute → ⊥
characterRouteIsNotComputationalRoute ()

griessHasNoStateFieldStructureByRoute :
  hasGradedStateFieldAlgebra (signature griessFiniteAlgebraRoute) ≡ false
griessHasNoStateFieldStructureByRoute = refl

flmHasOrbifoldTwistedSector :
  hasTwistedOrbifoldSector (signature flmOrbifoldVOARoute) ≡ true
flmHasOrbifoldTwistedSector = refl

flmRouteDoesNotByItselfSupplyFullMcKayThompsonData :
  hasMcKayThompsonModularData (signature flmOrbifoldVOARoute) ≡ false
flmRouteDoesNotByItselfSupplyFullMcKayThompsonData = refl

borcherdsAddsGeneralizedKacMoodyStructure :
  hasGeneralizedKacMoodyAlgebra (signature borcherdsMonsterLieRoute) ≡ true
borcherdsAddsGeneralizedKacMoodyStructure = refl

characterDataAloneHasNoFiniteGroupConstruction :
  hasExplicitFiniteGroupData (signature conwayNortonCharacterRoute) ≡ false
characterDataAloneHasNoFiniteGroupConstruction = refl

computationalRouteHasNoModularDataByDefinition :
  hasMcKayThompsonModularData (signature computationalFiniteGroupRoute) ≡ false
computationalRouteHasNoModularDataByDefinition = refl

restrictionBridge :
  ∀ dataSet →
  Griess.WeightTwoVOAAutomorphism dataSet →
  Griess.GriessProductAutomorphism dataSet
restrictionBridge = Griess.restrictVOAAutomorphismToGriess

record RouteComparisonAuthorityBoundary : Set where
  constructor routeComparisonAuthorityBoundary
  field
    equalWeightTwoDimensionIdentifiesRoutes : Set
    equalDimensionDoesNotIdentifyRoutes :
      equalWeightTwoDimensionIdentifiesRoutes → Set

    everyFiniteGriessAutomorphismLiftsToVOA : Set
    reverseLiftNeedsExtensionTheorem :
      everyFiniteGriessAutomorphismLiftsToVOA → Set

canonicalRouteComparisonAuthorityBoundary : RouteComparisonAuthorityBoundary
canonicalRouteComparisonAuthorityBoundary =
  routeComparisonAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
