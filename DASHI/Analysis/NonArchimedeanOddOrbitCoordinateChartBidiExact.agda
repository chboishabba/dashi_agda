module DASHI.Analysis.NonArchimedeanOddOrbitCoordinateChartBidiExact where

------------------------------------------------------------------------
-- ODD-ORBIT COORDINATE CHART
--
-- Source `DFT.index_equiv` proves a useful carrier equivalence
--
--   ZMod(2^(n-1)) ~= ZMod(2^(n-2)) x ZMod 2
--
-- by cardinality through Fin/product reindexing.  That is NOT yet the semantic
-- chart in which the second coordinate names the two odd x3-orbits and the
-- first coordinate records orbit position.
--
-- The spectral derivation needs the latter.  This owner keeps the generic
-- product reindex and the genuine orbit chart separate until an explicit
-- same-object weld is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)

record CardinalityProductChart : Set₁ where
  field
    SourceIndex : Set
    PositionIndex : Set
    OrbitBit : Set
    toProduct : SourceIndex → PositionIndex × OrbitBit
    fromProduct : PositionIndex × OrbitBit → SourceIndex
    fromAfterTo : (x : SourceIndex) → fromProduct (toProduct x) ≡ x
    toAfterFrom : (x : PositionIndex × OrbitBit) → toProduct (fromProduct x) ≡ x

record GenuineOddOrbitChart : Set₁ where
  field
    OddResidue : Set
    OrbitPosition : Set
    OrbitLabel : Set

    timesThree : OddResidue → OddResidue
    encodeOrbit : OddResidue → OrbitPosition × OrbitLabel
    decodeOrbit : OrbitPosition × OrbitLabel → OddResidue

    decodeAfterEncode :
      (x : OddResidue) → decodeOrbit (encodeOrbit x) ≡ x

    encodeAfterDecode :
      (x : OrbitPosition × OrbitLabel) → encodeOrbit (decodeOrbit x) ≡ x

    orbitPositionAdvancesUnderTimesThree :
      (x : OddResidue) → Set

    orbitLabelPreservedUnderTimesThree :
      (x : OddResidue) → Set

record ProductToOrbitSameObject
    (cardinality : CardinalityProductChart)
    (orbit : GenuineOddOrbitChart) : Set₁ where
  field
    sourceIndexToOddResidue :
      CardinalityProductChart.SourceIndex cardinality →
      GenuineOddOrbitChart.OddResidue orbit

    oddResidueToSourceIndex :
      GenuineOddOrbitChart.OddResidue orbit →
      CardinalityProductChart.SourceIndex cardinality

    sourceRoundTrip :
      (x : CardinalityProductChart.SourceIndex cardinality) →
      oddResidueToSourceIndex (sourceIndexToOddResidue x) ≡ x

    oddRoundTrip :
      (x : GenuineOddOrbitChart.OddResidue orbit) →
      sourceIndexToOddResidue (oddResidueToSourceIndex x) ≡ x

    productCoordinatesAgreeWithOrbitCoordinates :
      (x : CardinalityProductChart.SourceIndex cardinality) → Set

open ProductToOrbitSameObject public

record OrbitChartBoundary : Set where
  constructor orbitChartBoundary
  field
    sourceCardinalityProductEquivalenceOwned : Bool
    sourceOrderOfThreeOwned : Bool
    sourceOddResidueCardinalityOwned : Bool
    exportedCanonicalTwoOrbitPartitionLocated : Bool
    sourceProductEquivalenceIsDefinitionallyOddOrbitChart : Bool
    explicitProductToOrbitSameObjectWeldOwned : Bool
    equalCardinalityMayPromoteOrbitSemantics : Bool

canonicalOrbitChartBoundary : OrbitChartBoundary
canonicalOrbitChartBoundary =
  orbitChartBoundary true true true false false false false

cardinalityDoesNotSupplyOrbitSemantics :
  OrbitChartBoundary.equalCardinalityMayPromoteOrbitSemantics
    canonicalOrbitChartBoundary
  ≡ false
cardinalityDoesNotSupplyOrbitSemantics = refl

canonicalPartitionStillNeedsExportedProducer :
  OrbitChartBoundary.exportedCanonicalTwoOrbitPartitionLocated
    canonicalOrbitChartBoundary
  ≡ false
canonicalPartitionStillNeedsExportedProducer = refl
