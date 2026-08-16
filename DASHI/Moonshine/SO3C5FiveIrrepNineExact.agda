module DASHI.Moonshine.SO3C5FiveIrrepNineExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Give a literal representation-theoretic realization of the "five irreps of
-- nine" motif raised in the SSP reduction discussion.
--
-- For the integer-spin j=4 SO(3) irrep, dim V_4 = 9 and the weight lines are
-- m=-4,...,+4.  Restricting the axial rotations to C5 groups these weights by
-- residue modulo five.  Since every complex irrep of C5 is one-dimensional,
-- the restriction has five irreducible sectors with multiplicities
--
--   [1,2,2,2,2],
--
-- so 9 = 1+2+2+2+2 exactly.
--
-- The neighbouring j=5 carrier gives [3,2,2,2,2], so the C5 branching data
-- separates dimension 9 from dimension 11 even though their C2/C3 fixed-space
-- pair is identical.  This does not claim C5 is the final Ogg selector; it is
-- a concrete producer demonstrating how richer subgroup branching can recover
-- information lost by the minimal fixed-space quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact as Scan

------------------------------------------------------------------------
-- Five irreducible complex character sectors of C5.
------------------------------------------------------------------------

data C5Character : Set where
  chi0 chi1 chi2 chi3 chi4 : C5Character

record C5BranchingSpectrum : Set where
  constructor c5BranchingSpectrum
  field
    mult0 mult1 mult2 mult3 mult4 : Nat

open C5BranchingSpectrum public

c5Total : C5BranchingSpectrum → Nat
c5Total spectrum =
  mult0 spectrum
  + mult1 spectrum
  + mult2 spectrum
  + mult3 spectrum
  + mult4 spectrum

c5Multiplicity : C5BranchingSpectrum → C5Character → Nat
c5Multiplicity spectrum chi0 = mult0 spectrum
c5Multiplicity spectrum chi1 = mult1 spectrum
c5Multiplicity spectrum chi2 = mult2 spectrum
c5Multiplicity spectrum chi3 = mult3 spectrum
c5Multiplicity spectrum chi4 = mult4 spectrum

allC5Characters : List C5Character
allC5Characters = chi0 ∷ chi1 ∷ chi2 ∷ chi3 ∷ chi4 ∷ []

------------------------------------------------------------------------
-- j=4: the exact five-irrep decomposition of nine.
------------------------------------------------------------------------

j4C5Spectrum : C5BranchingSpectrum
j4C5Spectrum = c5BranchingSpectrum 1 2 2 2 2

j4C5TotalIsNine : c5Total j4C5Spectrum ≡ 9
j4C5TotalIsNine = refl

j4C5TotalMatchesAmbient : c5Total j4C5Spectrum ≡ Scan.oddDimension 4
j4C5TotalMatchesAmbient = refl

j4HasFiveIrrepSectors : allC5Characters ≡ chi0 ∷ chi1 ∷ chi2 ∷ chi3 ∷ chi4 ∷ []
j4HasFiveIrrepSectors = refl

j4TrivialC5MultiplicityIsOne : c5Multiplicity j4C5Spectrum chi0 ≡ 1
j4TrivialC5MultiplicityIsOne = refl

j4NontrivialC5MultiplicitiesAreTwo :
  c5Multiplicity j4C5Spectrum chi1 ≡ 2
  × (c5Multiplicity j4C5Spectrum chi2 ≡ 2
  × (c5Multiplicity j4C5Spectrum chi3 ≡ 2
  × c5Multiplicity j4C5Spectrum chi4 ≡ 2))
j4NontrivialC5MultiplicitiesAreTwo = refl , (refl , (refl , refl))

------------------------------------------------------------------------
-- j=5: the neighbouring dimension eleven control.
------------------------------------------------------------------------

j5C5Spectrum : C5BranchingSpectrum
j5C5Spectrum = c5BranchingSpectrum 3 2 2 2 2

j5C5TotalIsEleven : c5Total j5C5Spectrum ≡ 11
j5C5TotalIsEleven = refl

j5C5TotalMatchesAmbient : c5Total j5C5Spectrum ≡ Scan.oddDimension 5
j5C5TotalMatchesAmbient = refl

j5TrivialC5MultiplicityIsThree : c5Multiplicity j5C5Spectrum chi0 ≡ 3
j5TrivialC5MultiplicityIsThree = refl

j4J5C5BranchingDiffer : j4C5Spectrum ≡ j5C5Spectrum → ⊥
j4J5C5BranchingDiffer ()

------------------------------------------------------------------------
-- The C5 invariant line is exactly the trivial-character multiplicity.
------------------------------------------------------------------------

j4C5FixedSpaceDimension : Nat
j4C5FixedSpaceDimension = c5Multiplicity j4C5Spectrum chi0

j5C5FixedSpaceDimension : Nat
j5C5FixedSpaceDimension = c5Multiplicity j5C5Spectrum chi0

j4C5FixedIsOne : j4C5FixedSpaceDimension ≡ 1
j4C5FixedIsOne = refl

j5C5FixedIsThree : j5C5FixedSpaceDimension ≡ 3
j5C5FixedIsThree = refl
