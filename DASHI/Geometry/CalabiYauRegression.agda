module DASHI.Geometry.CalabiYauRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)

open import DASHI.Geometry.ComplexManifold
open import DASHI.Geometry.Kahler
open import DASHI.Geometry.CalabiYau

------------------------------------------------------------------------
-- A fully constructive zero-dimensional point example.  Its role is to
-- exercise every interface field and eliminator without postulates; it is not
-- used to promote any positive-dimensional analytic Calabi-Yau construction.

record Truth : Set where
  constructor truth

data One : Set where
  one : One

oneDomain : One → One → Set
oneDomain _ _ = Truth

oneCharts : ComplexManifoldCharts One One
oneCharts =
  record
    { ChartIndex = One
    ; Domain = oneDomain
    ; OpenPointSubset = λ _ → Truth
    ; domainOpen = λ _ → truth
    ; cover = λ _ → mkChartCover one truth
    ; coordinate = λ _ _ _ → one
    ; Image = λ _ _ → Truth
    ; OpenCoordinateSubset = λ _ → Truth
    ; imageOpen = λ _ → truth
    ; inverseCoordinate = λ _ _ → one
    ; inverseInDomain = λ _ → truth
    ; chartLeftInverse = λ _ one _ → refl
    ; chartRightInverse = λ _ one _ → refl
    ; IsChartHomeomorphism = λ _ → Truth
    ; chartHomeomorphism = λ _ → truth
    ; Overlap = λ _ _ _ → Truth
    ; overlapReflexive = λ _ _ _ → truth
    ; overlapSymmetric = λ _ → truth
    ; transition = λ _ _ z → z
    ; transitionIdentity = λ _ _ → refl
    ; transitionInverse = λ _ _ → refl
    ; transitionCocycle = λ _ _ _ _ → refl
    ; coordinateChange = λ _ _ _ → refl
    }

oneHolomorphicTransitionLaws : HolomorphicTransitionLaws oneCharts
oneHolomorphicTransitionLaws =
  record
    { Holomorphic = λ _ → Truth
    ; holomorphicIdentity = truth
    ; holomorphicComposition = λ _ _ → truth
    ; transitionHolomorphic = λ _ → truth
    }

oneComplexManifold : ComplexManifoldAuthority One One
oneComplexManifold =
  record
    { complexDimension = zero
    ; coordinateDimension = λ _ → zero
    ; coordinateDimensionMatches = λ _ → refl
    ; complexCharts = oneCharts
    ; holomorphicTransitions = oneHolomorphicTransitionLaws
    }

oneTangent : One → Set
oneTangent _ = One

oneKahler : KahlerAuthority oneComplexManifold One oneTangent
oneKahler =
  record
    { zeroTangent = λ _ → one
    ; negateTangent = λ _ v → v
    ; zeroScalar = one
    ; negateScalar = λ scalar → scalar
    ; complexStructure = λ _ v → v
    ; complexStructureSquared = λ _ _ → refl
    ; TangentLinearEndomorphism = λ _ → Truth
    ; complexStructureLinear = truth
    ; AtlasCompatibleComplexStructure = λ _ → Truth
    ; complexStructureAtlasCompatible = truth
    ; metric = λ _ _ _ → one
    ; MetricBilinear = λ _ → Truth
    ; metricBilinear = truth
    ; metricSymmetric = λ _ _ _ → refl
    ; NondegenerateMetric = λ _ → Truth
    ; metricNondegenerate = truth
    ; PositiveScalar = λ _ → Truth
    ; metricPositive = λ _ _ _ → truth
    ; hermitianCompatibility = λ _ _ _ → refl
    ; kahlerForm = λ _ _ _ → one
    ; TwoFormBilinear = λ _ → Truth
    ; kahlerFormBilinear = truth
    ; kahlerFormAlternating = λ _ _ → refl
    ; kahlerFormSkewSymmetric = λ _ _ _ → refl
    ; NondegenerateTwoForm = λ _ → Truth
    ; kahlerFormNondegenerate = truth
    ; ClosedTwoForm = λ _ → Truth
    ; kahlerFormClosed = truth
    ; kahlerCompatibility = λ _ _ _ → refl
    }

oneChernCertificate : VanishingFirstChernClass One
oneChernCertificate =
  record
    { zeroClass = one
    ; firstChernClass = one
    ; RepresentsFirstChernClassOfHolomorphicTangent = λ _ → Truth
    ; firstChernClassRepresentsHolomorphicTangent = truth
    ; firstChernClassIsZero = refl
    }

oneVolumeFormAuthority :
  HolomorphicVolumeFormAuthority oneComplexManifold One
oneVolumeFormAuthority =
  record
    { IsTopDegreeForm = λ _ _ → Truth
    ; IsHolomorphicForm = λ _ → Truth
    ; VanishesAt = λ _ _ → ⊥
    ; TrivializesCanonicalBundle = λ _ → Truth
    ; holomorphicVolumeForm = one
    ; volumeFormHasTopDegree = truth
    ; volumeFormIsHolomorphic = truth
    ; volumeFormNowhereVanishes = λ _ ()
    ; volumeFormTrivializesCanonicalBundle = truth
    }

canonicalPointCalabiYau :
  CalabiYauAuthority One One One oneTangent One One
canonicalPointCalabiYau =
  record
    { complexManifold = oneComplexManifold
    ; kahler = oneKahler
    ; firstChernClassCertificate = oneChernCertificate
    ; volumeFormAuthority = oneVolumeFormAuthority
    ; CanonicalTrivialityCoherence = λ _ _ → Truth
    ; selectedDefinitionCoherence = truth
    }

canonicalPointDimensionIsZero :
  complexDimension (complexManifold canonicalPointCalabiYau) ≡ zero
canonicalPointDimensionIsZero = refl

canonicalPointCoordinateDimensionIsZero :
  coordinateDimension (complexManifold canonicalPointCalabiYau) one ≡ zero
canonicalPointCoordinateDimensionIsZero =
  coordinateDimensionMatches (complexManifold canonicalPointCalabiYau) one

canonicalPointFirstChernClassVanishes :
  firstChernClass (firstChernClassCertificate canonicalPointCalabiYau)
    ≡ zeroClass (firstChernClassCertificate canonicalPointCalabiYau)
canonicalPointFirstChernClassVanishes =
  calabiYauFirstChernClassVanishes canonicalPointCalabiYau

canonicalPointVolumeFormIsHolomorphic :
  IsHolomorphicForm
    (volumeFormAuthority canonicalPointCalabiYau)
    (holomorphicVolumeForm (volumeFormAuthority canonicalPointCalabiYau))
canonicalPointVolumeFormIsHolomorphic =
  calabiYauVolumeFormIsHolomorphic canonicalPointCalabiYau

canonicalPointVolumeFormNowhereVanishes :
  (x : One) →
  VanishesAt
    (volumeFormAuthority canonicalPointCalabiYau)
    (holomorphicVolumeForm (volumeFormAuthority canonicalPointCalabiYau))
    x →
  ⊥
canonicalPointVolumeFormNowhereVanishes =
  calabiYauVolumeFormNowhereVanishes canonicalPointCalabiYau
