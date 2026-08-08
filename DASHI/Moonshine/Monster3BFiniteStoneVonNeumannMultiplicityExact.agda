module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact semisimple counting consequence of finite
-- Stone--von Neumann uniqueness.  Once each irreducible constituent carrying
-- the selected nontrivial central character has degree 729, a phase sector of
-- total degree 65610 contains exactly 90 such constituents.  The proof works
-- on a literal finite constituent list and derives the count by cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- A constituent certified by the finite Stone--von Neumann theorem.
------------------------------------------------------------------------

record ZetaHeisenbergIrreducible : Set₁ where
  constructor zeta-heisenberg-irreducible
  field
    Carrier : Set
    degree : Nat
    selectedCentralCharacter : Set
    irreducible : Set
    stoneVonNeumannDegree : degree ≡ 729

open ZetaHeisenbergIrreducible public

constituentCount : List ZetaHeisenbergIrreducible → Nat
constituentCount [] = 0
constituentCount (_ ∷ constituents) = suc (constituentCount constituents)

constituentDegreeSum : List ZetaHeisenbergIrreducible → Nat
constituentDegreeSum [] = 0
constituentDegreeSum (constituent ∷ constituents) =
  degree constituent + constituentDegreeSum constituents

constituentDegreeSumIsHeisenbergTimesCount :
  (constituents : List ZetaHeisenbergIrreducible) →
  constituentDegreeSum constituents
  ≡ 729 * constituentCount constituents
constituentDegreeSumIsHeisenbergTimesCount [] = refl
constituentDegreeSumIsHeisenbergTimesCount
  (constituent ∷ constituents)
  rewrite stoneVonNeumannDegree constituent
        | constituentDegreeSumIsHeisenbergTimesCount constituents = refl

------------------------------------------------------------------------
-- Exact multiplicity forcing.
------------------------------------------------------------------------

ninetyHeisenbergDegree : 729 * 90 ≡ 65610
ninetyHeisenbergDegree = refl

multiplicityForcedToNinety :
  (multiplicity : Nat) →
  729 * multiplicity ≡ 65610 →
  multiplicity ≡ 90
multiplicityForcedToNinety multiplicity degreeEquation =
  NatP.*-cancelʳ-≡ multiplicity 90 729
    (trans
      (NatP.*-comm multiplicity 729)
      (trans degreeEquation (sym (NatP.*-comm 90 729))))

actualZetaSectorHasNinetyConstituents :
  (constituents : List ZetaHeisenbergIrreducible) →
  constituentDegreeSum constituents ≡ 65610 →
  constituentCount constituents ≡ 90
actualZetaSectorHasNinetyConstituents constituents totalDegree =
  multiplicityForcedToNinety
    (constituentCount constituents)
    (trans
      (sym (constituentDegreeSumIsHeisenbergTimesCount constituents))
      totalDegree)

------------------------------------------------------------------------
-- This packages the actual representation-theoretic endpoint after the
-- external kernel action has supplied a semisimple constituent enumeration.
------------------------------------------------------------------------

record ActualZetaSectorStoneVonNeumannDecomposition : Set₁ where
  constructor actual-zeta-sector-stone-von-neumann-decomposition
  field
    constituents : List ZetaHeisenbergIrreducible
    actualSectorDegree : constituentDegreeSum constituents ≡ 65610

open ActualZetaSectorStoneVonNeumannDecomposition public

actualZetaSectorMultiplicityIsNinety :
  (decomposition : ActualZetaSectorStoneVonNeumannDecomposition) →
  constituentCount (constituents decomposition) ≡ 90
actualZetaSectorMultiplicityIsNinety decomposition =
  actualZetaSectorHasNinetyConstituents
    (constituents decomposition)
    (actualSectorDegree decomposition)
