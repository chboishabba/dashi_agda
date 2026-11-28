module DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact finite rational matrix carrier for the arbitrary-side
-- physical su(2) coordinates introduced in BalabanPhysicalSU2FiniteCoordinatesExact.
-- This removes the last side-four dependency from the linear-algebra carrier:
-- for every L the coordinate enumeration is complete and duplicate-free, its
-- equality is decidable, and its Kronecker delta acts exactly as the identity.
-- In particular L=13 now has an honest FiniteRationalCoordinates object on the
-- same 3*4*13^4 tangent coordinates used by the source-faithful Gate-I lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

zeroPlusZero : 0ℚ + 0ℚ ≡ 0ℚ
zeroPlusZero = ℚRing.solve-∀

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

notMemberOfCons :
  ∀ {A : Set} {value row : A} {values : List A} →
  row ∉ (value ∷ values) → row ≡ value → ⊥
notMemberOfCons notMember equality with equality
... | refl = notMember here

notTailAtEqual :
  ∀ {A : Set} {value row : A} {values : List A} →
  value ∉ values → row ∈ values → row ≡ value → ⊥
notTailAtEqual notTail membership equality with equality
... | refl = notTail membership

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
deltaSumAbsent decide (value ∷ values) row notMember vector with decide row value
... | yes equality = ⊥-elim (notMemberOfCons notMember equality)
... | no inequality
  rewrite ℚP.*-zeroˡ (vector value)
        | deltaSumAbsent decide values row
            (λ membership → notMember (there membership)) vector
        | zeroPlusZero = refl

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
        | deltaSumAbsent decide _ row notTail vector
        | ℚP.*-identityˡ (vector row)
        | ℚP.+-identityʳ (vector row) = refl
deltaSumIdentity decide {values = value ∷ values}
    (notTail ∷-free tailFree) row (there membership) vector
  with decide row value
... | yes equality = ⊥-elim (notTailAtEqual notTail membership equality)
... | no inequality
  rewrite deltaSumIdentity decide tailFree row membership vector =
  trans (cong (λ z → z + vector row) (ℚP.*-zeroˡ (vector value)))
        (ℚP.+-identityˡ (vector row))

------------------------------------------------------------------------
-- Three Lie-coordinate factors.
------------------------------------------------------------------------

lieCoordinateDecidableEquality : DecidableEquality Physical.LieCoordinate3
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateX = yes refl
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateY = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateX = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateY = yes refl
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateX = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateY = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateZ = yes refl

coordinateXNotTail :
  Physical.coordinateX ∉ (Physical.coordinateY ∷ Physical.coordinateZ ∷ [])
coordinateXNotTail (there (there ()))

coordinateYNotTail : Physical.coordinateY ∉ (Physical.coordinateZ ∷ [])
coordinateYNotTail (there ())

coordinateZNotEmpty : Physical.coordinateZ ∉ []
coordinateZNotEmpty ()

lieCoordinatesDuplicateFree : DuplicateFree Physical.lieCoordinates3
lieCoordinatesDuplicateFree =
  coordinateXNotTail ∷-free
    (coordinateYNotTail ∷-free
      (coordinateZNotEmpty ∷-free []-free))

lieCoordinateFinite : FiniteEnumeration Physical.LieCoordinate3
lieCoordinateFinite = record
  { elements = Physical.lieCoordinates3
  ; complete = λ where
      Physical.coordinateX → here
      Physical.coordinateY → there here
      Physical.coordinateZ → there (there here)
  }

------------------------------------------------------------------------
-- Arbitrary-side site/bond/state enumeration.
------------------------------------------------------------------------

siteElementsDuplicateFree : ∀ L →
  DuplicateFree (elements (periodicTorus4Finite L))
siteElementsDuplicateFree L =
  cartesianDuplicateFree
    (cartesianDuplicateFree
      (allCyclicIndicesDuplicateFree L)
      (allCyclicIndicesDuplicateFree L))
    (cartesianDuplicateFree
      (allCyclicIndicesDuplicateFree L)
      (allCyclicIndicesDuplicateFree L))

positiveBondFinite : ∀ L → FiniteEnumeration (PositiveBond L)
positiveBondFinite L =
  productFinite (periodicTorus4Finite L) (cyclicIndexFinite four)

positiveBondElementsDuplicateFree : ∀ L →
  DuplicateFree (elements (positiveBondFinite L))
positiveBondElementsDuplicateFree L =
  cartesianDuplicateFree
    (siteElementsDuplicateFree L)
    (allCyclicIndicesDuplicateFree four)

physicalCoordinateFinite : ∀ L →
  FiniteEnumeration (Physical.PhysicalSU2Coordinate L)
physicalCoordinateFinite L =
  productFinite lieCoordinateFinite (positiveBondFiniteReoriented L)
  where
  positiveBondFiniteReoriented : ∀ side →
    FiniteEnumeration (Physical.PhysicalBondCell side)
  positiveBondFiniteReoriented side =
    productFinite (cyclicIndexFinite four) (periodicTorus4Finite side)

physicalBondCellElementsDuplicateFree : ∀ L →
  DuplicateFree (elements
    (productFinite (cyclicIndexFinite four) (periodicTorus4Finite L)))
physicalBondCellElementsDuplicateFree L =
  cartesianDuplicateFree
    (allCyclicIndicesDuplicateFree four)
    (siteElementsDuplicateFree L)

physicalCoordinateElementsDuplicateFree : ∀ L →
  DuplicateFree (elements (physicalCoordinateFinite L))
physicalCoordinateElementsDuplicateFree L =
  cartesianDuplicateFree
    lieCoordinatesDuplicateFree
    (physicalBondCellElementsDuplicateFree L)

physicalCoordinateDecidableEquality : ∀ L →
  DecidableEquality (Physical.PhysicalSU2Coordinate L)
physicalCoordinateDecidableEquality L =
  productDecidableEquality
    lieCoordinateDecidableEquality
    (productDecidableEquality
      cyclicIndexDecidableEquality
      (periodicTorus4DecidableEquality L))

physicalCoordinateDelta : ∀ L →
  Physical.PhysicalSU2Coordinate L → Physical.PhysicalSU2Coordinate L → ℚ
physicalCoordinateDelta L =
  kroneckerDelta (physicalCoordinateDecidableEquality L)

physicalFiniteRationalCoordinates : ∀ L →
  Matrix.FiniteRationalCoordinates (Physical.PhysicalSU2Coordinate L)
physicalFiniteRationalCoordinates L = record
  { coordinates =
      elements (physicalCoordinateFinite L)
  ; delta =
      physicalCoordinateDelta L
  ; deltaActsAsIdentity = λ vector row →
      deltaSumIdentity
        (physicalCoordinateDecidableEquality L)
        (physicalCoordinateElementsDuplicateFree L)
        row
        (complete (physicalCoordinateFinite L) row)
        vector
  }

physicalSU2ArbitrarySideEnumerationLevel : ProofLevel
physicalSU2ArbitrarySideEnumerationLevel = machineChecked

physicalSU2ArbitrarySideDeltaLevel : ProofLevel
physicalSU2ArbitrarySideDeltaLevel = machineChecked

physicalSU2ArbitrarySideFiniteRationalCarrierLevel : ProofLevel
physicalSU2ArbitrarySideFiniteRationalCarrierLevel = machineChecked
