module DASHI.Geometry.Kahler where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.ComplexManifold using (ComplexManifoldAuthority)

------------------------------------------------------------------------
-- Kähler structure over an already certified complex manifold.
--
-- Scalar and tangent algebra are intentionally supplied by the producer.
-- The record asks for the mathematical content that matters here: an
-- atlas-compatible complex structure J, a positive nondegenerate Hermitian
-- metric, the compatible real two-form, and closedness of that form.

data Never : Set where

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → Never

record KahlerAuthority
    {Point Coordinate : Set}
    (M : ComplexManifoldAuthority Point Coordinate)
    (RealScalar : Set)
    (Tangent : Point → Set)
    : Set₁ where
  constructor mkKahlerAuthority
  field
    zeroTangent : (x : Point) → Tangent x
    negateTangent : (x : Point) → Tangent x → Tangent x

    zeroScalar : RealScalar
    negateScalar : RealScalar → RealScalar

    complexStructure :
      (x : Point) →
      Tangent x →
      Tangent x

    complexStructureSquared :
      (x : Point) →
      (v : Tangent x) →
      complexStructure x (complexStructure x v) ≡ negateTangent x v

    TangentLinearEndomorphism :
      ((x : Point) → Tangent x → Tangent x) →
      Set

    complexStructureLinear :
      TangentLinearEndomorphism complexStructure

    AtlasCompatibleComplexStructure :
      ((x : Point) → Tangent x → Tangent x) →
      Set

    complexStructureAtlasCompatible :
      AtlasCompatibleComplexStructure complexStructure

    metric :
      (x : Point) →
      Tangent x →
      Tangent x →
      RealScalar

    MetricBilinear :
      ((x : Point) → Tangent x → Tangent x → RealScalar) →
      Set

    metricBilinear :
      MetricBilinear metric

    metricSymmetric :
      (x : Point) →
      (u v : Tangent x) →
      metric x u v ≡ metric x v u

    NondegenerateMetric :
      ((x : Point) → Tangent x → Tangent x → RealScalar) →
      Set

    metricNondegenerate :
      NondegenerateMetric metric

    PositiveScalar : RealScalar → Set

    metricPositive :
      (x : Point) →
      (v : Tangent x) →
      v ≢ zeroTangent x →
      PositiveScalar (metric x v v)

    hermitianCompatibility :
      (x : Point) →
      (u v : Tangent x) →
      metric x (complexStructure x u) (complexStructure x v)
        ≡ metric x u v

    kahlerForm :
      (x : Point) →
      Tangent x →
      Tangent x →
      RealScalar

    TwoFormBilinear :
      ((x : Point) → Tangent x → Tangent x → RealScalar) →
      Set

    kahlerFormBilinear :
      TwoFormBilinear kahlerForm

    kahlerFormAlternating :
      (x : Point) →
      (v : Tangent x) →
      kahlerForm x v v ≡ zeroScalar

    kahlerFormSkewSymmetric :
      (x : Point) →
      (u v : Tangent x) →
      kahlerForm x u v ≡ negateScalar (kahlerForm x v u)

    NondegenerateTwoForm :
      ((x : Point) → Tangent x → Tangent x → RealScalar) →
      Set

    kahlerFormNondegenerate :
      NondegenerateTwoForm kahlerForm

    ClosedTwoForm :
      ((x : Point) → Tangent x → Tangent x → RealScalar) →
      Set

    kahlerFormClosed :
      ClosedTwoForm kahlerForm

    kahlerCompatibility :
      (x : Point) →
      (u v : Tangent x) →
      kahlerForm x u v ≡ metric x (complexStructure x u) v

open KahlerAuthority public
