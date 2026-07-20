module DASHI.Geometry.CalabiYau where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Geometry.ComplexManifold using
  (ComplexManifoldAuthority; complexDimension)
open import DASHI.Geometry.Kahler using (KahlerAuthority)

------------------------------------------------------------------------
-- Calabi-Yau authority package.
--
-- We use the noncompact-compatible structural definition requested by the
-- geometry promotion boundary: a complex manifold with holomorphic chart
-- transitions, Kähler data, c₁(T¹⁰M) = 0, and a nowhere-vanishing
-- holomorphic top form.  Compactness, Ricci-flatness, and Yau's existence
-- theorem are separate possible refinements and are not manufactured here.

record VanishingFirstChernClass
    (IntegralCohomology2 : Set)
    : Set₁ where
  constructor mkVanishingFirstChernClass
  field
    zeroClass : IntegralCohomology2
    firstChernClass : IntegralCohomology2

    RepresentsFirstChernClassOfHolomorphicTangent :
      IntegralCohomology2 →
      Set

    firstChernClassRepresentsHolomorphicTangent :
      RepresentsFirstChernClassOfHolomorphicTangent firstChernClass

    firstChernClassIsZero :
      firstChernClass ≡ zeroClass

open VanishingFirstChernClass public

record HolomorphicVolumeFormAuthority
    {Point Coordinate : Set}
    (M : ComplexManifoldAuthority Point Coordinate)
    (TopForm : Set)
    : Set₁ where
  constructor mkHolomorphicVolumeFormAuthority
  field
    IsTopDegreeForm : Nat → TopForm → Set
    IsHolomorphicForm : TopForm → Set
    VanishesAt : TopForm → Point → Set
    TrivializesCanonicalBundle : TopForm → Set

    holomorphicVolumeForm : TopForm

    volumeFormHasTopDegree :
      IsTopDegreeForm (complexDimension M) holomorphicVolumeForm

    volumeFormIsHolomorphic :
      IsHolomorphicForm holomorphicVolumeForm

    volumeFormNowhereVanishes :
      (x : Point) →
      VanishesAt holomorphicVolumeForm x →
      ⊥

    volumeFormTrivializesCanonicalBundle :
      TrivializesCanonicalBundle holomorphicVolumeForm

open HolomorphicVolumeFormAuthority public

record CalabiYauAuthority
    (Point Coordinate RealScalar : Set)
    (Tangent : Point → Set)
    (IntegralCohomology2 TopForm : Set)
    : Set₁ where
  constructor mkCalabiYauAuthority
  field
    complexManifold :
      ComplexManifoldAuthority Point Coordinate

    kahler :
      KahlerAuthority complexManifold RealScalar Tangent

    firstChernClassCertificate :
      VanishingFirstChernClass IntegralCohomology2

    volumeFormAuthority :
      HolomorphicVolumeFormAuthority complexManifold TopForm

    CanonicalTrivialityCoherence :
      VanishingFirstChernClass IntegralCohomology2 →
      HolomorphicVolumeFormAuthority complexManifold TopForm →
      Set

    selectedDefinitionCoherence :
      CanonicalTrivialityCoherence
        firstChernClassCertificate
        volumeFormAuthority

open CalabiYauAuthority public

calabiYauFirstChernClassVanishes :
  ∀ {Point Coordinate RealScalar IntegralCohomology2 TopForm : Set}
    {Tangent : Point → Set} →
    (CY :
      CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm) →
    firstChernClass (firstChernClassCertificate CY)
      ≡ zeroClass (firstChernClassCertificate CY)
calabiYauFirstChernClassVanishes CY =
  firstChernClassIsZero (firstChernClassCertificate CY)

calabiYauVolumeFormIsHolomorphic :
  ∀ {Point Coordinate RealScalar IntegralCohomology2 TopForm : Set}
    {Tangent : Point → Set} →
    (CY :
      CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm) →
    IsHolomorphicForm
      (volumeFormAuthority CY)
      (holomorphicVolumeForm (volumeFormAuthority CY))
calabiYauVolumeFormIsHolomorphic CY =
  volumeFormIsHolomorphic (volumeFormAuthority CY)

calabiYauVolumeFormNowhereVanishes :
  ∀ {Point Coordinate RealScalar IntegralCohomology2 TopForm : Set}
    {Tangent : Point → Set} →
    (CY :
      CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm) →
    (x : Point) →
    VanishesAt
      (volumeFormAuthority CY)
      (holomorphicVolumeForm (volumeFormAuthority CY))
      x →
    ⊥
calabiYauVolumeFormNowhereVanishes CY =
  volumeFormNowhereVanishes (volumeFormAuthority CY)
