module DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact using
  (configuredGaugeFixedMatrix)
open import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact

------------------------------------------------------------------------
-- Generic Kronecker calculus for a duplicate-free decidable enumeration.
------------------------------------------------------------------------

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

kroneckerDelta :
  ∀ {A : Set} → DecidableEquality A → A → A → ℚ
kroneckerDelta decide left right with decide left right
... | yes equality = 1ℚ
... | no inequality = 0ℚ

kroneckerSelf :
  ∀ {A : Set} (decide : DecidableEquality A) value →
  kroneckerDelta decide value value ≡ 1ℚ
kroneckerSelf decide value with decide value value
... | yes equality = refl
... | no inequality = emptyElim (inequality refl)

kroneckerDifferent :
  ∀ {A : Set} (decide : DecidableEquality A) {left right} →
  left ≢ right → kroneckerDelta decide left right ≡ 0ℚ
kroneckerDifferent decide {left} {right} different with decide left right
... | yes equality = emptyElim (different equality)
... | no inequality = refl

zeroMulPlusZeroRaw : ∀ x → 0ℚ * x + 0ℚ ≡ 0ℚ
zeroMulPlusZeroRaw x =
  trans (cong (_+ 0ℚ) (ℚP.*-zeroˡ x)) (ℚP.+-identityʳ 0ℚ)

oneMulPlusZeroRaw : ∀ x → 1ℚ * x + 0ℚ ≡ x
oneMulPlusZeroRaw x =
  trans (cong (_+ 0ℚ) (ℚP.*-identityˡ x)) (ℚP.+-identityʳ x)

zeroMulPlusRightRaw : ∀ x y → 0ℚ * x + y ≡ y
zeroMulPlusRightRaw x y =
  trans (cong (_+ y) (ℚP.*-zeroˡ x)) (ℚP.+-identityˡ y)

deltaSumAbsent :
  ∀ {A : Set}
    (decide : DecidableEquality A)
    (values : List A) →
  ∀ row → row ∉ values →
  (vector : A → ℚ) →
  sumRational values
    (λ column → kroneckerDelta decide row column * vector column)
  ≡ 0ℚ
deltaSumAbsent decide [] row notMember vector = refl
deltaSumAbsent decide (value ∷ values) row notMember vector =
  trans
    (cong₂ _+_
      (cong (_* vector value)
        (kroneckerDifferent decide
          (λ equality →
            ⊥-elim
              (notMember
                (subst (λ candidate → candidate ∈ value ∷ values)
                  (sym equality) here)))))
      (deltaSumAbsent decide values row
        (λ membership → notMember (there membership)) vector))
    (zeroMulPlusZeroRaw (vector value))

deltaSumIdentity :
  ∀ {A : Set}
    (decide : DecidableEquality A)
    {values : List A} →
  ∀ row → row ∈ values →
  DuplicateFree values →
  (vector : A → ℚ) →
  sumRational values
    (λ column → kroneckerDelta decide row column * vector column)
  ≡ vector row
deltaSumIdentity decide {values = .row ∷ values}
    row here (notTail ∷-free tailFree) vector =
  trans
    (cong₂ _+_
      (cong (_* vector row) (kroneckerSelf decide row))
      (deltaSumAbsent decide values row notTail vector))
    (oneMulPlusZeroRaw (vector row))
deltaSumIdentity decide {values = value ∷ values}
    row (there membership) (notTail ∷-free tailFree) vector =
  trans
    (cong₂ _+_
      (cong (_* vector value)
        (kroneckerDifferent decide
          (λ equality →
            ⊥-elim
              (notTail (subst (λ candidate → candidate ∈ values) equality membership)))))
      (deltaSumIdentity decide row membership tailFree vector))
    (zeroMulPlusRightRaw (vector value) (vector row))

------------------------------------------------------------------------
-- Literal three-colour tangent component enumeration.
------------------------------------------------------------------------

componentDecidableEquality : DecidableEquality SU2Component
componentDecidableEquality component1 component1 = yes refl
componentDecidableEquality component1 component2 = no (λ ())
componentDecidableEquality component1 component3 = no (λ ())
componentDecidableEquality component2 component1 = no (λ ())
componentDecidableEquality component2 component2 = yes refl
componentDecidableEquality component2 component3 = no (λ ())
componentDecidableEquality component3 component1 = no (λ ())
componentDecidableEquality component3 component2 = no (λ ())
componentDecidableEquality component3 component3 = yes refl

componentElements : List SU2Component
componentElements = component1 ∷ component2 ∷ component3 ∷ []

componentFinite : FiniteEnumeration SU2Component
componentFinite = record
  { elements = componentElements
  ; complete = λ where
      component1 → here
      component2 → there here
      component3 → there (there here)
  }

component1NotTail : component1 ∉ (component2 ∷ component3 ∷ [])
component1NotTail (there (there ()))

component2NotTail : component2 ∉ (component3 ∷ [])
component2NotTail (there ())

component3NotEmpty : component3 ∉ []
component3NotEmpty ()

componentElementsDuplicateFree : DuplicateFree componentElements
componentElementsDuplicateFree =
  component1NotTail ∷-free
    (component2NotTail ∷-free
      (component3NotEmpty ∷-free []-free))

------------------------------------------------------------------------
-- The literal 3 × (4^4 × 4) physical coordinate carrier.
------------------------------------------------------------------------

PhysicalSU2Coordinate4 : Set
PhysicalSU2Coordinate4 = Product SU2Component (PositiveBond four)

productFiniteDuplicateFree :
  ∀ {A B : Set}
    (finiteA : FiniteEnumeration A)
    (finiteB : FiniteEnumeration B) →
  DuplicateFree (elements finiteA) →
  DuplicateFree (elements finiteB) →
  DuplicateFree (elements (productFinite finiteA finiteB))
productFiniteDuplicateFree finiteA finiteB freeA freeB =
  cartesianDuplicateFree
    {left = elements finiteA}
    {right = elements finiteB}
    freeA freeB

cyclicFourDuplicateFree :
  DuplicateFree (elements (cyclicIndexFinite four))
cyclicFourDuplicateFree = allCyclicIndicesDuplicateFree four

pair2FourFinite : FiniteEnumeration (Pair2 (CyclicIndex four))
pair2FourFinite = productFinite (cyclicIndexFinite four) (cyclicIndexFinite four)

positiveBondFinite : FiniteEnumeration (PositiveBond four)
positiveBondFinite =
  productFinite (periodicTorus4Finite four) (cyclicIndexFinite four)

physicalCoordinateFinite : FiniteEnumeration PhysicalSU2Coordinate4
physicalCoordinateFinite = productFinite componentFinite positiveBondFinite

abstract
  pair2FourDuplicateFree :
    DuplicateFree (elements pair2FourFinite)
  pair2FourDuplicateFree =
    productFiniteDuplicateFree
      (cyclicIndexFinite four)
      (cyclicIndexFinite four)
      cyclicFourDuplicateFree
      cyclicFourDuplicateFree

abstract
  siteElementsDuplicateFree :
    DuplicateFree (elements (periodicTorus4Finite four))
  siteElementsDuplicateFree =
    productFiniteDuplicateFree
      pair2FourFinite
      pair2FourFinite
      pair2FourDuplicateFree
      pair2FourDuplicateFree

abstract
  positiveBondElementsDuplicateFree :
    DuplicateFree (elements positiveBondFinite)
  positiveBondElementsDuplicateFree =
    productFiniteDuplicateFree
      (periodicTorus4Finite four)
      (cyclicIndexFinite four)
      siteElementsDuplicateFree
      cyclicFourDuplicateFree

abstract
  physicalCoordinateElementsDuplicateFree :
    DuplicateFree (elements physicalCoordinateFinite)
  physicalCoordinateElementsDuplicateFree =
    productFiniteDuplicateFree
      componentFinite
      positiveBondFinite
      componentElementsDuplicateFree
      positiveBondElementsDuplicateFree

physicalCoordinateDecidableEquality :
  DecidableEquality PhysicalSU2Coordinate4
physicalCoordinateDecidableEquality =
  productDecidableEquality
    componentDecidableEquality
    (productDecidableEquality
      (periodicTorus4DecidableEquality four)
      cyclicIndexDecidableEquality)

physicalCoordinateDelta :
  PhysicalSU2Coordinate4 → PhysicalSU2Coordinate4 → ℚ
physicalCoordinateDelta =
  kroneckerDelta physicalCoordinateDecidableEquality

abstract
  physicalCoordinateElements : List PhysicalSU2Coordinate4
  physicalCoordinateElements = elements physicalCoordinateFinite

  physicalCoordinateDeltaActsAsIdentity :
    ∀ (vector : PhysicalSU2Coordinate4 → ℚ) (row : PhysicalSU2Coordinate4) →
    sumRational physicalCoordinateElements
      (λ column → physicalCoordinateDelta row column * vector column)
    ≡ vector row
  physicalCoordinateDeltaActsAsIdentity vector row =
    deltaSumIdentity
      physicalCoordinateDecidableEquality
      {values = elements physicalCoordinateFinite}
      row
      (complete physicalCoordinateFinite row)
      physicalCoordinateElementsDuplicateFree
      vector

physicalFiniteRationalCoordinates :
  FiniteRationalCoordinates PhysicalSU2Coordinate4
physicalFiniteRationalCoordinates = record
  { coordinates = physicalCoordinateElements
  ; delta = physicalCoordinateDelta
  ; deltaActsAsIdentity = physicalCoordinateDeltaActsAsIdentity
  }

------------------------------------------------------------------------
-- Literal coordinate representation and configured operator matrix.
------------------------------------------------------------------------

tangentToCoordinateVector :
  PhysicalSU2Tangent4 → RationalVector PhysicalSU2Coordinate4
tangentToCoordinateVector tangent (pair component bond) =
  tangent component bond

coordinateVectorToTangent :
  RationalVector PhysicalSU2Coordinate4 → PhysicalSU2Tangent4
coordinateVectorToTangent vector component bond =
  vector (pair component bond)

tangentCoordinateRoundTripPointwise : ∀ tangent component bond →
  coordinateVectorToTangent (tangentToCoordinateVector tangent) component bond
  ≡ tangent component bond
tangentCoordinateRoundTripPointwise tangent component bond = refl

coordinateTangentRoundTripPointwise : ∀ vector coordinate →
  tangentToCoordinateVector (coordinateVectorToTangent vector) coordinate
  ≡ vector coordinate
coordinateTangentRoundTripPointwise vector (pair component bond) = refl

coordinateBasisTangent : PhysicalSU2Coordinate4 → PhysicalSU2Tangent4
coordinateBasisTangent column component bond =
  physicalCoordinateDelta (pair component bond) column

configuredGaugeFixedOperatorMatrix :
  RationalMatrix PhysicalSU2Coordinate4
configuredGaugeFixedOperatorMatrix row column =
  tangentToCoordinateVector
    (configuredGaugeFixedMatrix (coordinateBasisTangent column)) row

record ConfiguredMatrixActionCertificate : Set₁ where
  field
    configuredMatrixActsExactly : ∀ tangent row →
      applyMatrix
        physicalFiniteRationalCoordinates
        configuredGaugeFixedOperatorMatrix
        (tangentToCoordinateVector tangent)
        row
      ≡ tangentToCoordinateVector (configuredGaugeFixedMatrix tangent) row

open ConfiguredMatrixActionCertificate public

physicalCoordinateEnumerationLevel : ProofLevel
physicalCoordinateEnumerationLevel = machineChecked

physicalCoordinateDeltaActionLevel : ProofLevel
physicalCoordinateDeltaActionLevel = machineChecked

physicalCoordinateRoundTripLevel : ProofLevel
physicalCoordinateRoundTripLevel = machineChecked

configuredGaugeFixedOperatorMatrixDefinitionLevel : ProofLevel
configuredGaugeFixedOperatorMatrixDefinitionLevel = machineChecked

configuredMatrixActionLinearityProducerLevel : ProofLevel
configuredMatrixActionLinearityProducerLevel = conditional
