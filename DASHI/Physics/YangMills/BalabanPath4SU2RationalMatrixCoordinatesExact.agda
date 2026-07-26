module DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
kroneckerDifferent decide different with decide _ _
... | yes equality = emptyElim (different equality)
... | no inequality = refl

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
deltaSumAbsent decide (value ∷ values) row notMember vector
  rewrite kroneckerDifferent decide
    (λ equality →
      notMember
        (subst (λ candidate → candidate ∈ value ∷ values)
          (sym equality) here))
        | deltaSumAbsent decide values row
            (λ membership → notMember (there membership)) vector =
  ℚRing.solve-∀ (vector value)

deltaSumIdentity :
  ∀ {A : Set}
    (decide : DecidableEquality A)
    {values : List A} →
  DuplicateFree values →
  ∀ row → row ∈ values →
  (vector : A → ℚ) →
  sumRational values
    (λ column → kroneckerDelta decide row column * vector column)
  ≡ vector row
deltaSumIdentity decide []-free row () vector
deltaSumIdentity decide (notTail ∷-free tailFree) row here vector
  rewrite kroneckerSelf decide row
        | deltaSumAbsent decide _ row notTail vector =
  ℚRing.solve-∀ (vector row)
deltaSumIdentity decide {values = value ∷ values}
    (notTail ∷-free tailFree) row (there membership) vector
  rewrite kroneckerDifferent decide
    (λ equality →
      notTail (subst (λ candidate → candidate ∈ values) equality membership))
        | deltaSumIdentity decide tailFree row membership vector =
  ℚRing.solve-∀ (vector value) (vector row)

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

siteElementsDuplicateFree :
  DuplicateFree (elements (periodicTorus4Finite four))
siteElementsDuplicateFree =
  cartesianDuplicateFree
    (cartesianDuplicateFree
      (allCyclicIndicesDuplicateFree four)
      (allCyclicIndicesDuplicateFree four))
    (cartesianDuplicateFree
      (allCyclicIndicesDuplicateFree four)
      (allCyclicIndicesDuplicateFree four))

positiveBondFinite : FiniteEnumeration (PositiveBond four)
positiveBondFinite =
  productFinite (periodicTorus4Finite four) (cyclicIndexFinite four)

positiveBondElementsDuplicateFree :
  DuplicateFree (elements positiveBondFinite)
positiveBondElementsDuplicateFree =
  cartesianDuplicateFree
    siteElementsDuplicateFree
    (allCyclicIndicesDuplicateFree four)

physicalCoordinateFinite : FiniteEnumeration PhysicalSU2Coordinate4
physicalCoordinateFinite = productFinite componentFinite positiveBondFinite

physicalCoordinateElementsDuplicateFree :
  DuplicateFree (elements physicalCoordinateFinite)
physicalCoordinateElementsDuplicateFree =
  cartesianDuplicateFree
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

physicalFiniteRationalCoordinates :
  FiniteRationalCoordinates PhysicalSU2Coordinate4
physicalFiniteRationalCoordinates = record
  { coordinates = elements physicalCoordinateFinite
  ; delta = physicalCoordinateDelta
  ; deltaActsAsIdentity = λ vector row →
      deltaSumIdentity
        physicalCoordinateDecidableEquality
        physicalCoordinateElementsDuplicateFree
        row
        (complete physicalCoordinateFinite row)
        vector
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
