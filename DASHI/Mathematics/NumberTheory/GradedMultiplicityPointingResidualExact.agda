module DASHI.Mathematics.NumberTheory.GradedMultiplicityPointingResidualExact where

------------------------------------------------------------------------
-- GRADED MULTIPLICITY POINTING / RESIDUAL SKELETON
--
-- DASHI CONTRIBUTION
--
-- Extract the combinatorial pattern underneath the Erdos partition identity.
-- A finite graded multiplicity state consists of generators g with
-- multiplicities m(g), positive/natural weights w(g), and exact grade
--
--   grade = sum_g w(g) * m(g).
--
-- A pointed cell chooses
--
--   g,
--   an occurrence j : Fin (m(g)),
--   a unit u : Fin (w(g)).
--
-- Hence the finite pointed-cell carrier has exactly `grade` elements.  A
-- domain-specific deletion/reinsertion theorem can then identify these cells
-- with a residual carrier.  This owner deliberately knows nothing about
-- integer partitions, Fock spaces, Euler products, or asymptotics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Finite

------------------------------------------------------------------------
-- Abstract finite graded multiplicity state.

record GradedMultiplicitySystem : Set₁ where
  field
    Generator : Set
    generators : List Generator
    multiplicity : Generator → Nat
    weight : Generator → Nat
    grade : Nat
    gradeExact :
      Reindex.foldNat (λ g → weight g * multiplicity g) generators
      ≡ grade

open GradedMultiplicitySystem public

------------------------------------------------------------------------
-- Literal pointed cells.

PointedCell : GradedMultiplicitySystem → Set
PointedCell system =
  Σ (Generator system)
    (λ g → Fin (multiplicity system g) × Fin (weight system g))

cellsForGenerator :
  (system : GradedMultiplicitySystem) →
  (g : Generator system) →
  List (PointedCell system)
cellsForGenerator system g =
  map
    (λ occurrenceUnit → g , occurrenceUnit)
    (Finite.markEnumeration {n = weight system g}
      (Finite.allFin (multiplicity system g)))

cellsForGeneratorLength :
  (system : GradedMultiplicitySystem) →
  (g : Generator system) →
  Reindex.listLength (cellsForGenerator system g)
  ≡ weight system g * multiplicity system g
cellsForGeneratorLength system g =
  trans
    (Finite.mapLength
      (λ occurrenceUnit → g , occurrenceUnit)
      (Finite.markEnumeration {n = weight system g}
        (Finite.allFin (multiplicity system g))))
    (trans
      (Finite.markEnumerationLength {n = weight system g}
        (Finite.allFin (multiplicity system g)))
      (cong (weight system g *_)
        (Finite.allFinLength (multiplicity system g))))

pointedCellsFrom :
  (system : GradedMultiplicitySystem) →
  List (Generator system) →
  List (PointedCell system)
pointedCellsFrom system [] = []
pointedCellsFrom system (g ∷ gs) =
  cellsForGenerator system g ++ pointedCellsFrom system gs

pointedCells :
  (system : GradedMultiplicitySystem) → List (PointedCell system)
pointedCells system = pointedCellsFrom system (generators system)

pointedCellsFromLength :
  (system : GradedMultiplicitySystem) →
  (gs : List (Generator system)) →
  Reindex.listLength (pointedCellsFrom system gs)
  ≡ Reindex.foldNat
      (λ g → weight system g * multiplicity system g)
      gs
pointedCellsFromLength system [] = refl
pointedCellsFromLength system (g ∷ gs) =
  trans
    (Finite.appendLength
      (cellsForGenerator system g)
      (pointedCellsFrom system gs))
    (cong₂ _+_
      (cellsForGeneratorLength system g)
      (pointedCellsFromLength system gs))
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

pointedCellsLengthEqualsGrade :
  (system : GradedMultiplicitySystem) →
  Reindex.listLength (pointedCells system) ≡ grade system
pointedCellsLengthEqualsGrade system =
  trans
    (pointedCellsFromLength system (generators system))
    (gradeExact system)

pointedUnitFoldEqualsGrade :
  (system : GradedMultiplicitySystem) →
  Reindex.foldNat (λ _ → 1) (pointedCells system) ≡ grade system
pointedUnitFoldEqualsGrade system =
  trans
    (Reindex.foldOneIsLength (pointedCells system))
    (pointedCellsLengthEqualsGrade system)

------------------------------------------------------------------------
-- Abstract residual equivalence.
--
-- Domains instantiate this only after constructing literal delete/insert maps
-- and proving the two round trips.  Once instantiated, any finite unique
-- enumeration of the residual carrier may be reindexed from `pointedCells`
-- using FiniteWeightedReindexExact.

record PointingResidualDecomposition
    (system : GradedMultiplicitySystem) : Set₁ where
  field
    Residual : Set
    delete : PointedCell system → Residual
    insert : Residual → PointedCell system
    deleteInsert : (residual : Residual) → delete (insert residual) ≡ residual
    insertDelete : (cell : PointedCell system) → insert (delete cell) ≡ cell

open PointingResidualDecomposition public

------------------------------------------------------------------------
-- No infinite series, differentiation, real analysis, or proof irrelevance
-- enters this theorem owner.
------------------------------------------------------------------------
