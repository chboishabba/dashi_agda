module DASHI.Physics.YangMills.BalabanRestrictedFluctuationCoordinateBijection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Empty)

------------------------------------------------------------------------
-- Restricted fluctuation coordinates.
--
-- A nonsingular Jacobian is only a local statement.  The RG coordinate map
-- must instead carry explicit admissible domains and two round-trip laws.
------------------------------------------------------------------------

record RestrictedChartData (Configuration Coordinate : Set) : Set₁ where
  field
    encode : Coordinate → Configuration
    decode : Configuration → Coordinate

    ConfigurationAdmissible : Configuration → Set
    CoordinateAdmissible : Coordinate → Set

    encodePreservesAdmissibility : ∀ coordinate →
      CoordinateAdmissible coordinate →
      ConfigurationAdmissible (encode coordinate)

    decodePreservesAdmissibility : ∀ configuration →
      ConfigurationAdmissible configuration →
      CoordinateAdmissible (decode configuration)

    configurationRoundTrip : ∀ configuration →
      ConfigurationAdmissible configuration →
      encode (decode configuration) ≡ configuration

    coordinateRoundTrip : ∀ coordinate →
      CoordinateAdmissible coordinate →
      decode (encode coordinate) ≡ coordinate

open RestrictedChartData public

RestrictedInjective :
  ∀ {Configuration Coordinate} →
  RestrictedChartData Configuration Coordinate → Set
RestrictedInjective dataSet =
  ∀ left right →
  CoordinateAdmissible dataSet left →
  CoordinateAdmissible dataSet right →
  encode dataSet left ≡ encode dataSet right →
  left ≡ right

RestrictedSurjective :
  ∀ {Configuration Coordinate} →
  RestrictedChartData Configuration Coordinate → Set
RestrictedSurjective dataSet =
  ∀ configuration →
  ConfigurationAdmissible dataSet configuration →
  encode dataSet (decode dataSet configuration) ≡ configuration

record RestrictedBijection
    {Configuration Coordinate : Set}
    (dataSet : RestrictedChartData Configuration Coordinate) : Set₁ where
  field
    injective : RestrictedInjective dataSet
    surjective : RestrictedSurjective dataSet

open RestrictedBijection public

restrictedChartInjective :
  ∀ {Configuration Coordinate}
    (dataSet : RestrictedChartData Configuration Coordinate) →
  RestrictedInjective dataSet
restrictedChartInjective dataSet left right leftAdmissible rightAdmissible equality
  rewrite coordinateRoundTrip dataSet left leftAdmissible
        | coordinateRoundTrip dataSet right rightAdmissible
        | equality = refl

restrictedChartSurjective :
  ∀ {Configuration Coordinate}
    (dataSet : RestrictedChartData Configuration Coordinate) →
  RestrictedSurjective dataSet
restrictedChartSurjective = configurationRoundTrip

restrictedRoundTripsGiveBijection :
  ∀ {Configuration Coordinate}
    (dataSet : RestrictedChartData Configuration Coordinate) →
  RestrictedBijection dataSet
restrictedRoundTripsGiveBijection dataSet = record
  { injective = restrictedChartInjective dataSet
  ; surjective = restrictedChartSurjective dataSet
  }

------------------------------------------------------------------------
-- Fail-closed adversarial statement: a constant/nonzero Jacobian witness does
-- not imply global injectivity when an explicit collision is present.
------------------------------------------------------------------------

record JacobianCollisionData (Domain Codomain Jacobian : Set) : Set₁ where
  field
    map : Domain → Codomain
    jacobianDeterminant : Domain → Jacobian
    selectedDeterminant : Jacobian
    determinantConstant : ∀ point →
      jacobianDeterminant point ≡ selectedDeterminant

    left right : Domain
    Distinct : Domain → Domain → Set
    leftDistinctRight : Distinct left right
    collision : map left ≡ map right

open JacobianCollisionData public

GloballyInjective :
  ∀ {Domain Codomain} → (Domain → Codomain) → Set
GloballyInjective map = ∀ left right → map left ≡ map right → left ≡ right

record EqualityExcludesDistinctness (Domain : Set)
    (Distinct : Domain → Domain → Set) : Set₁ where
  field
    equalityContradictsDistinct : ∀ {left right} →
      left ≡ right → Distinct left right → Empty

open EqualityExcludesDistinctness public

constantJacobianCollisionRefutesGlobalInjectivity :
  ∀ {Domain Codomain Jacobian}
    (collisionData : JacobianCollisionData Domain Codomain Jacobian) →
    EqualityExcludesDistinctness Domain (Distinct collisionData) →
    GloballyInjective (map collisionData) → Empty
constantJacobianCollisionRefutesGlobalInjectivity collisionData exclusion injective =
  equalityContradictsDistinct exclusion
    (injective (left collisionData) (right collisionData)
      (collision collisionData))
    (leftDistinctRight collisionData)

restrictedFluctuationCoordinateBijectionLevel : ProofLevel
restrictedFluctuationCoordinateBijectionLevel = machineChecked

jacobianAloneImpliesGlobalBijectionLevel : ProofLevel
jacobianAloneImpliesGlobalBijectionLevel = counterexample
