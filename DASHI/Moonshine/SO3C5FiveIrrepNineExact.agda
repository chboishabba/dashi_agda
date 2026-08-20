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
-- nine" motif inside the repository's canonical representation-restriction
-- lane.
--
-- For the integer-spin j=4 SO(3) irrep, dim V_4 = 9 and the weights are
-- m=-4,...,+4.  Restricting axial rotations to C5 groups these weights by
-- residue modulo five.  Since every complex irrep of C5 is one-dimensional,
--
--   V_4 | C5 = chi0 + 2 chi1 + 2 chi2 + 2 chi3 + 2 chi4,
--
-- hence 9 = 1+2+2+2+2 with all five irrep species present.
--
-- The neighbouring j=5 carrier gives
--
--   V_5 | C5 = 3 chi0 + 2 chi1 + 2 chi2 + 2 chi3 + 2 chi4,
--
-- so the C5 branch separates dimension 9 from 11 even though their C2/C3
-- fixed-space pair coincides.  C5 is an information-producing restriction
-- here, not an asserted final Ogg subgroup.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact as Scan

------------------------------------------------------------------------
-- Five irreducible complex character sectors of C5.
------------------------------------------------------------------------

data C5Character : Set where
  chi0 chi1 chi2 chi3 chi4 : C5Character

allC5Characters : List C5Character
allC5Characters = chi0 ∷ chi1 ∷ chi2 ∷ chi3 ∷ chi4 ∷ []

c5IrrepDimension : C5Character → Nat
c5IrrepDimension chi0 = 1
c5IrrepDimension chi1 = 1
c5IrrepDimension chi2 = 1
c5IrrepDimension chi3 = 1
c5IrrepDimension chi4 = 1

c5Family : Core.FiniteIrrepFamily
c5Family =
  Core.finite-irrep-family
    C5Character
    allC5Characters
    c5IrrepDimension
    "five one-dimensional complex characters of C5"

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

------------------------------------------------------------------------
-- j=4: exact five-irrep decomposition of nine.
------------------------------------------------------------------------

j4C5Spectrum : C5BranchingSpectrum
j4C5Spectrum = c5BranchingSpectrum 1 2 2 2 2

j4C5TotalIsNine : c5Total j4C5Spectrum ≡ 9
j4C5TotalIsNine = refl

j4C5TotalMatchesAmbient : c5Total j4C5Spectrum ≡ Spin.jDimension Spin.j4
j4C5TotalMatchesAmbient = refl

j4TrivialC5MultiplicityIsOne : c5Multiplicity j4C5Spectrum chi0 ≡ 1
j4TrivialC5MultiplicityIsOne = refl

j4NontrivialC5MultiplicitiesAreTwo :
  c5Multiplicity j4C5Spectrum chi1 ≡ 2
  × (c5Multiplicity j4C5Spectrum chi2 ≡ 2
  × (c5Multiplicity j4C5Spectrum chi3 ≡ 2
  × c5Multiplicity j4C5Spectrum chi4 ≡ 2))
j4NontrivialC5MultiplicitiesAreTwo = refl , (refl , (refl , refl))

j4CoreMultiplicity : C5Character → Nat
j4CoreMultiplicity = c5Multiplicity j4C5Spectrum

j4CoreBranching :
  Core.BranchingSpectrum (Spin.continuousSO3Irrep Spin.j4) c5Family
j4CoreBranching =
  Core.branching-spectrum
    j4CoreMultiplicity
    refl
    "V_4 restricted to C5: multiplicities [1,2,2,2,2]"

------------------------------------------------------------------------
-- j=5: neighbouring dimension-eleven control.
------------------------------------------------------------------------

j5C5Spectrum : C5BranchingSpectrum
j5C5Spectrum = c5BranchingSpectrum 3 2 2 2 2

j5C5TotalIsEleven : c5Total j5C5Spectrum ≡ 11
j5C5TotalIsEleven = refl

j5C5TotalMatchesAmbient : c5Total j5C5Spectrum ≡ Spin.jDimension Spin.j5
j5C5TotalMatchesAmbient = refl

j5TrivialC5MultiplicityIsThree : c5Multiplicity j5C5Spectrum chi0 ≡ 3
j5TrivialC5MultiplicityIsThree = refl

j4J5C5BranchingDiffer : j4C5Spectrum ≡ j5C5Spectrum → ⊥
j4J5C5BranchingDiffer ()

j5CoreMultiplicity : C5Character → Nat
j5CoreMultiplicity = c5Multiplicity j5C5Spectrum

j5CoreBranching :
  Core.BranchingSpectrum (Spin.continuousSO3Irrep Spin.j5) c5Family
j5CoreBranching =
  Core.branching-spectrum
    j5CoreMultiplicity
    refl
    "V_5 restricted to C5: multiplicities [3,2,2,2,2]"

------------------------------------------------------------------------
-- Fixed-space probes and complete canonical FiniteRestriction witnesses.
------------------------------------------------------------------------

data C5FixedProbe : Set where
  c5WholeGroup : C5FixedProbe

c5ProbeLabel : C5FixedProbe → String
c5ProbeLabel c5WholeGroup = "C5 whole-group invariant subspace"

j4C5FixedSpaces : Core.FixedSpaceSpectrum
j4C5FixedSpaces =
  Core.fixed-space-spectrum
    C5FixedProbe
    (λ _ → 1)
    c5ProbeLabel
    "trivial-character multiplicity in V_4|C5 is one"

j5C5FixedSpaces : Core.FixedSpaceSpectrum
j5C5FixedSpaces =
  Core.fixed-space-spectrum
    C5FixedProbe
    (λ _ → 3)
    c5ProbeLabel
    "trivial-character multiplicity in V_5|C5 is three"

j4C5Restriction : Core.FiniteRestriction
j4C5Restriction =
  Core.finite-restriction
    (Spin.continuousSO3Irrep Spin.j4)
    c5Family
    j4CoreBranching
    j4C5FixedSpaces
    "exact C5 restriction of the nine-dimensional SO(3) j=4 carrier"

j5C5Restriction : Core.FiniteRestriction
j5C5Restriction =
  Core.finite-restriction
    (Spin.continuousSO3Irrep Spin.j5)
    c5Family
    j5CoreBranching
    j5C5FixedSpaces
    "exact C5 restriction of the eleven-dimensional SO(3) j=5 carrier"

j4C5FixedSpaceDimension : Nat
j4C5FixedSpaceDimension = Core.fixedDimension j4C5FixedSpaces c5WholeGroup

j5C5FixedSpaceDimension : Nat
j5C5FixedSpaceDimension = Core.fixedDimension j5C5FixedSpaces c5WholeGroup

j4C5FixedIsOne : j4C5FixedSpaceDimension ≡ 1
j4C5FixedIsOne = refl

j5C5FixedIsThree : j5C5FixedSpaceDimension ≡ 3
j5C5FixedIsThree = refl

------------------------------------------------------------------------
-- Cross-check against the minimal C2/C3 scan.
------------------------------------------------------------------------

j4AndJ5StillCollideOnC2C3 : Scan.fixedPair 4 ≡ Scan.fixedPair 5
j4AndJ5StillCollideOnC2C3 = Scan.j4AndJ5FixedPairsCoincide
