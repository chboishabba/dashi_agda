module DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster",
-- Pure and Applied Mathematics 134, Academic Press, 1988.
-- ISBN: 978-0-12-267065-7; no DOI assigned.
--
-- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura,
-- "Z_3-orbifold construction of the Moonshine vertex operator algebra and
-- some maximal 3-local subgroups of the Monster",
-- Mathematische Zeitschrift 288 (2018), 75--100.
-- DOI: 10.1007/s00209-017-1878-z.
--
-- Scott Carnahan,
-- "51 constructions of the Moonshine module",
-- arXiv:1707.02954; no DOI assigned in this file.
--
-- DASHI CONTRIBUTION
--
-- Replace the basis-dependent arithmetic chart
--
--   196608 + 276 = 196884
--
-- by the orbifold-sector decomposition used by the FLM construction:
--
--   dim (V_Lambda^+)_2
--     = dim Sym^2(h) + one vector from each {lambda,-lambda} pair
--     = 300 + 196560/2
--     = 98580,
--
--   dim ((V_Lambda^T)^+)_2
--     = 24 * 2^12
--     = 98304,
--
--   98580 + 98304 = 196884.
--
-- The earlier 196608 subtotal remains exact arithmetic after choosing a basis,
-- but it is not promoted to either orbifold summand or to a Monster-invariant
-- submodule.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

heisenbergRank : Nat
heisenbergRank = 24

heisenbergRankIsTwentyFour : heisenbergRank ≡ 24
heisenbergRankIsTwentyFour = refl

symmetricSquareDimension : Nat
symmetricSquareDimension = 300

symmetricSquareDimensionIsThreeHundred :
  symmetricSquareDimension ≡ 300
symmetricSquareDimensionIsThreeHundred = refl

leechNormFourVectorCount : Nat
leechNormFourVectorCount = 196560

pairedNormFourOrbitCount : Nat
pairedNormFourOrbitCount = 98280

pairedNormFourOrbitCountDoublesToLeechCount :
  2 * pairedNormFourOrbitCount ≡ leechNormFourVectorCount
pairedNormFourOrbitCountDoublesToLeechCount = refl

untwistedInvariantWeightTwoDimension : Nat
untwistedInvariantWeightTwoDimension =
  symmetricSquareDimension + pairedNormFourOrbitCount

untwistedInvariantWeightTwoDimensionIs98580 :
  untwistedInvariantWeightTwoDimension ≡ 98580
untwistedInvariantWeightTwoDimensionIs98580 = refl

twistedGroundStateMultiplicity : Nat
twistedGroundStateMultiplicity = 4096

twistedGroundStateMultiplicityIsTwoPowerTwelve :
  twistedGroundStateMultiplicity ≡ 4096
twistedGroundStateMultiplicityIsTwoPowerTwelve = refl

twistedCurrentMultiplicity : Nat
twistedCurrentMultiplicity = 24

twistedInvariantWeightTwoDimension : Nat
twistedInvariantWeightTwoDimension =
  twistedCurrentMultiplicity * twistedGroundStateMultiplicity

twistedInvariantWeightTwoDimensionIs98304 :
  twistedInvariantWeightTwoDimension ≡ 98304
twistedInvariantWeightTwoDimensionIs98304 = refl

moonshineWeightTwoDimension : Nat
moonshineWeightTwoDimension =
  untwistedInvariantWeightTwoDimension
  + twistedInvariantWeightTwoDimension

moonshineWeightTwoDimensionIs196884 :
  moonshineWeightTwoDimension ≡ 196884
moonshineWeightTwoDimensionIs196884 = refl

publishedOrbifoldWeightTwoSplit :
  98580 + 98304 ≡ 196884
publishedOrbifoldWeightTwoSplit = refl

------------------------------------------------------------------------
-- The conformal line lies in the untwisted invariant summand.
------------------------------------------------------------------------

conformalLineDimension : Nat
conformalLineDimension = 1

untwistedNonconformalDimension : Nat
untwistedNonconformalDimension = 98579

untwistedConformalSplit :
  conformalLineDimension + untwistedNonconformalDimension ≡ 98580
untwistedConformalSplit = refl

monsterNontrivialWeightTwoDimension : Nat
monsterNontrivialWeightTwoDimension =
  untwistedNonconformalDimension + twistedInvariantWeightTwoDimension

monsterNontrivialWeightTwoDimensionIs196883 :
  monsterNontrivialWeightTwoDimension ≡ 196883
monsterNontrivialWeightTwoDimensionIs196883 = refl

conformalPlusMonsterReconstructsWeightTwo :
  conformalLineDimension + monsterNontrivialWeightTwoDimension
  ≡ moonshineWeightTwoDimension
conformalPlusMonsterReconstructsWeightTwo = refl

------------------------------------------------------------------------
-- The old 196608 chart is retained only as a basis-dependent coordinate sum.
------------------------------------------------------------------------

basisDependentCoordinateSubtotal : Nat
basisDependentCoordinateSubtotal = 196560 + 24 + 24

basisDependentCoordinateSubtotalIs196608 :
  basisDependentCoordinateSubtotal ≡ 196608
basisDependentCoordinateSubtotalIs196608 = refl

offDiagonalCoordinateCount : Nat
offDiagonalCoordinateCount = 276

coordinateSubtotalPlusOffDiagonalIs196884 :
  basisDependentCoordinateSubtotal + offDiagonalCoordinateCount ≡ 196884
coordinateSubtotalPlusOffDiagonalIs196884 = refl

coordinateSubtotalIsNotUntwistedOrbifoldSummand :
  basisDependentCoordinateSubtotal ≡ untwistedInvariantWeightTwoDimension → ⊥
coordinateSubtotalIsNotUntwistedOrbifoldSummand ()

coordinateSubtotalIsNotTwistedOrbifoldSummand :
  basisDependentCoordinateSubtotal ≡ twistedInvariantWeightTwoDimension → ⊥
coordinateSubtotalIsNotTwistedOrbifoldSummand ()

record OrbifoldWeightTwoAuthorityBoundary : Set where
  constructor orbifold-weight-two-authority-boundary
  field
    untwistedDimensionWitness :
      untwistedInvariantWeightTwoDimension ≡ 98580
    twistedDimensionWitness :
      twistedInvariantWeightTwoDimension ≡ 98304
    totalDimensionWitness : moonshineWeightTwoDimension ≡ 196884
    monsterQuotientDimensionWitness :
      monsterNontrivialWeightTwoDimension ≡ 196883
    coordinateSubtotalIsPublishedOrbifoldSummand : Bool
    coordinateSubtotalIsPublishedOrbifoldSummandIsFalse :
      coordinateSubtotalIsPublishedOrbifoldSummand ≡ false
    coordinateSubtotalIsMonsterInvariantSubmodule : Bool
    coordinateSubtotalIsMonsterInvariantSubmoduleIsFalse :
      coordinateSubtotalIsMonsterInvariantSubmodule ≡ false

canonicalOrbifoldWeightTwoAuthorityBoundary :
  OrbifoldWeightTwoAuthorityBoundary
canonicalOrbifoldWeightTwoAuthorityBoundary =
  orbifold-weight-two-authority-boundary
    untwistedInvariantWeightTwoDimensionIs98580
    twistedInvariantWeightTwoDimensionIs98304
    moonshineWeightTwoDimensionIs196884
    monsterNontrivialWeightTwoDimensionIs196883
    false refl
    false refl
