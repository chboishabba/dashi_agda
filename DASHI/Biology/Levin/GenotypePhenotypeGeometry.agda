module DASHI.Biology.Levin.GenotypePhenotypeGeometry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Coordinate-independent carrier boundary for evolutionary geometry.
--
-- The discrete genotype carrier, its continuous embedding, and phenotype
-- manifold are kept distinct.  No embedding is claimed to be canonical.

record GenotypePhenotypeGeometry : Set₁ where
  field
    DiscreteGenotype   : Set
    ContinuousGenotype : Set
    Phenotype          : Set
    TangentG           : Set
    TangentP           : Set
    CotangentG         : Set
    CotangentP         : Set
    Scalar             : Set

    embedGenotype : DiscreteGenotype → ContinuousGenotype
    phenotypeMap  : ContinuousGenotype → Phenotype

    pushTangent : TangentG → TangentP
    pullCotangent : CotangentP → CotangentG

    genotypeMetric  : TangentG → TangentG → Scalar
    phenotypeMetric : TangentP → TangentP → Scalar

    metricPullbackCompatible : Bool
    metricPullbackCompatibleIsTrue :
      metricPullbackCompatible ≡ true

    coordinateIndependent : Bool
    coordinateIndependentIsTrue :
      coordinateIndependent ≡ true

    embeddingIsCanonical : Bool
    embeddingIsCanonicalIsFalse :
      embeddingIsCanonical ≡ false

    geometryReading : String

open GenotypePhenotypeGeometry public

record GeometryBoundary : Set where
  field
    discreteIsNotContinuous : Bool
    discreteIsNotContinuousIsFalse : discreteIsNotContinuous ≡ false

    phenotypeDistanceIsNotRawSequenceDistance : Bool
    phenotypeDistanceIsNotRawSequenceDistanceIsFalse :
      phenotypeDistanceIsNotRawSequenceDistance ≡ false

    coordinateChoiceIsNotBiologicalLaw : Bool
    coordinateChoiceIsNotBiologicalLawIsFalse :
      coordinateChoiceIsNotBiologicalLaw ≡ false

canonicalGeometryBoundary : GeometryBoundary
canonicalGeometryBoundary = record
  { discreteIsNotContinuous = false
  ; discreteIsNotContinuousIsFalse = refl
  ; phenotypeDistanceIsNotRawSequenceDistance = false
  ; phenotypeDistanceIsNotRawSequenceDistanceIsFalse = refl
  ; coordinateChoiceIsNotBiologicalLaw = false
  ; coordinateChoiceIsNotBiologicalLawIsFalse = refl
  }
