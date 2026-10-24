module DASHI.Mathematics.Topology.AlexanderHornedC3SUNLieGroupReuseExact where

------------------------------------------------------------------------
-- MAX-CUT LIE PRIOR-ART REUSE: EXISTING YM SU(3) GROUP, NOT A NEW
-- INCOMPATIBLE SU3 SUBTYPE / MATRIX MULTIPLICATION / LIE BRACKET.
--
-- OWNERS: CompactLieGroupCore.Group, CompactLieGroupDerived,
-- SUNMatrixCarrier.CertifiedSUNMatrixTheory, SU3MatrixInstance,
-- AlexanderHornedC3CompactCommutatorRepresentationExact (horn owner).
--
-- Gotô (1949), DOI 10.2969/jmsj/00130270: every element of compact
-- connected semisimple SU3 is a SINGLE GROUP COMMUTATOR. The theorem
-- is EXTERNAL. The repository's imported compactness/connectedness
-- facts do not themselves provide a certified constructive section.
--
-- Exact new theorem: given the existing certified SU3 group carrier,
-- a selected root, Gotô's section and the order-three inner action,
-- derive horn-compatible commutator representations USING the
-- existing Yang–Mills group/adjoint calculus. All products/inverses
-- and conjugation identities are the canonical group ones.
--
-- This is about multiplicative [x,y]=xyx^-1y^-1, NOT the
-- Lie-algebra bracket [X,Y]=XY-YX. Neither exp/log, BCH nor Haar
-- are needed for the abstract commutator tower.
--
-- Note universe: this first bridge specializes the already generic
-- SU(N) carrier to concrete level-zero Matrix/Complex sets, matching
-- the Horn.CommutatorSectionGroup Set-level address interface.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; trans; sym)

import DASHI.Physics.YangMills.CompactLieGroupCore as GroupCore
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieInnerC3Exact as Inner
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.SU3MatrixInstance as SU3
import DASHI.Mathematics.Topology.AlexanderHornedC3CompactCommutatorRepresentationExact as Horn

groupCommutator :
  {A : Set} → (H : GroupCore.Group A) → A → A → A
groupCommutator H a b =
  GroupCore.multiply H
    (GroupCore.multiply H
      (GroupCore.multiply H a b)
      (GroupCore.inverse H a))
    (GroupCore.inverse H b)

-- The original Gotô theorem is a mathematical theorem, not a
-- field automatically implied by the basic group laws.
record GotôGroupSection (A : Set) (H : GroupCore.Group A) : Set₁ where
  field
    left right : A → A
    factorization :
      (x : A) → groupCommutator H (left x) (right x) ≡ x

open GotôGroupSection public

-- Canonical compact-group conjugation preserves inversion. This is
-- PROVED using existing GroupDerived.leftInverseUnique and
-- conjugateProduct, instead of making it a new authority field.
conjugatePreservesInverse :
  {A : Set} (H : GroupCore.Group A) →
  (t x : A) →
  Derived.conjugate H t (GroupCore.inverse H x)
    ≡ GroupCore.inverse H (Derived.conjugate H t x)
conjugatePreservesInverse H t x =
  Derived.leftInverseUnique H
    (Derived.conjugate H t (GroupCore.inverse H x))
    (trans
      (sym (Derived.conjugateProduct H t
        (GroupCore.inverse H x) x))
      (trans
        (cong (Derived.conjugate H t)
          (GroupCore.inverseLeft H x))
        (Derived.conjugateIdentity H t)))

-- Also derived, not assumed: the inner automorphism respects
-- the actual GROUP commutator used in Hatcher's horn substitutions.
conjugatePreservesGroupCommutator :
  {A : Set} (H : GroupCore.Group A) →
  (t x y : A) →
  Derived.conjugate H t (groupCommutator H x y) ≡
    groupCommutator H
      (Derived.conjugate H t x)
      (Derived.conjugate H t y)
conjugatePreservesGroupCommutator H t x y =
  trans
    (Derived.conjugateProduct H t
      (GroupCore.multiply H
        (GroupCore.multiply H x y)
        (GroupCore.inverse H x))
      (GroupCore.inverse H y))
    (cong₂ (GroupCore.multiply H)
      (trans
        (Derived.conjugateProduct H t
          (GroupCore.multiply H x y)
          (GroupCore.inverse H x))
        (cong₂ (GroupCore.multiply H)
          (Derived.conjugateProduct H t x y)
          (conjugatePreservesInverse H t x)))
      (conjugatePreservesInverse H t y))

-- The only finite-rotation input is now the actual group law
-- T*T*T=I, NOT a separately assumed conjugation-cube theorem.
-- Existing CompactLieInnerC3Exact derives Ad_T^3=id from this.
-- SU3's exact source-specific T^3=I in sibling #1247 still needs
-- a typed equality bridge to this certified matrix carrier.
record InnerThreefoldAction
    (A : Set) (H : GroupCore.Group A) : Set₁ where
  field
    generator : A
    generatorCubed :
      GroupCore.multiply H
        (GroupCore.multiply H generator generator)
        generator ≡ GroupCore.identity H
open InnerThreefoldAction public

-- Instantiate the existing horn commutator address operator from
-- the existing Group carrier, without duplicating its group axioms.
asHornSection :
  {A : Set} →
  (H : GroupCore.Group A) →
  (section : GotôGroupSection A H) →
  (twist : InnerThreefoldAction A H) →
  (root : A) →
  Horn.CommutatorSectionGroup
asHornSection {A = A} H section twist root = record
  { Horn.Carrier = A
  ; Horn.identity = GroupCore.identity H
  ; Horn.multiply = GroupCore.multiply H
  ; Horn.inverse = GroupCore.inverse H
  ; Horn.root = root
  ; Horn.chooseLeft = left section
  ; Horn.chooseRight = right section
  ; Horn.chosenCommutator = factorization section
  ; Horn.twist = Derived.conjugate H (generator twist)
  ; Horn.twistUnit = Derived.conjugateIdentity H (generator twist)
  ; Horn.twistProduct = Derived.conjugateProduct H (generator twist)
  ; Horn.twistInverse = conjugatePreservesInverse H (generator twist)
  ; Horn.twistCubed =
      Inner.innerC3FromElementCube H
        (generator twist) (generatorCubed twist)
  ; Horn.twistCommutator =
      conjugatePreservesGroupCommutator H (generator twist)
  }

-- Concrete specialization: this is the SAME SU3 carrier used by
-- the Yang–Mills theory, not an independent symbolic matrix type.
SU3Elements : (Matrix Complex : Set) →
  SUN.CertifiedSUNMatrixTheory 3 Matrix Complex → Set
SU3Elements Matrix Complex theory = SUN.SUNMatrixElement theory

-- A Gotô-section package over the current SU3 matrix subtype.
record SU3GotoInput (Matrix Complex : Set)
    (theory : SUN.CertifiedSUNMatrixTheory 3 Matrix Complex) : Set₂ where
  field
    commutatorSection :
      GotôGroupSection (SUN.SUNMatrixElement theory)
        (SU3.su3MatrixGroup theory)
    rotation :
      InnerThreefoldAction (SUN.SUNMatrixElement theory)
        (SU3.su3MatrixGroup theory)
    selectedRoot : SUN.SUNMatrixElement theory
open SU3GotoInput public

-- The requested EXISTING SU3 Lie-group instance is the literal
-- group passed to the horned word and commutator construction.
sun3HornAction :
  (Matrix Complex : Set) →
  (theory : SUN.CertifiedSUNMatrixTheory 3 Matrix Complex) →
  SU3GotoInput Matrix Complex theory →
  Horn.CommutatorSectionGroup
sun3HornAction Matrix Complex theory data =
  asHornSection
    (SU3.su3MatrixGroup theory)
    (commutatorSection data)
    (rotation data)
    (selectedRoot data)

-- Source-word expansion and cyclic-equivariance theorems are
-- inherited exactly from the existing horned owner:
--   Horn.everyHornExpansionPreservesValue (sun3HornAction ...)
--   Horn.wordRotationEquivariant (sun3HornAction ...)
-- Neither theorem is reproved or copied into a parallel carrier.
