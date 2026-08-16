module DASHI.Moonshine.SO3CyclicBranchingControlExact where

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
-- Strengthen the first SO(3) fixed-space scan with literal branching data at
-- the earliest informative control pair.  The C2/C3 invariant dimensions of
-- j=4 and j=5 coincide, but their complete cyclic multiplicity spectra do not.
-- This is the first concrete demonstration that the Ogg selector, if it is a
-- reduced-symmetry invariant, must retain branching information rather than
-- only fixed-space dimension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact as Scan

------------------------------------------------------------------------
-- C2 restriction: trivial and sign characters.
------------------------------------------------------------------------

record C2Branching : Set where
  constructor c2Branching
  field
    trivialMultiplicity : Nat
    signMultiplicity : Nat

open C2Branching public

c2Total : C2Branching → Nat
c2Total spectrum = trivialMultiplicity spectrum + signMultiplicity spectrum

j4C2Branching : C2Branching
j4C2Branching = c2Branching 5 4

j5C2Branching : C2Branching
j5C2Branching = c2Branching 5 6

j4C2BranchingConservesDimension : c2Total j4C2Branching ≡ Scan.oddDimension 4
j4C2BranchingConservesDimension = refl

j5C2BranchingConservesDimension : c2Total j5C2Branching ≡ Scan.oddDimension 5
j5C2BranchingConservesDimension = refl

j4C2FixedMultiplicityMatchesScan :
  trivialMultiplicity j4C2Branching ≡ Scan.fixedC2 4
j4C2FixedMultiplicityMatchesScan = refl

j5C2FixedMultiplicityMatchesScan :
  trivialMultiplicity j5C2Branching ≡ Scan.fixedC2 5
j5C2FixedMultiplicityMatchesScan = refl

c2BranchingControlDiffers : j4C2Branching ≡ j5C2Branching → ⊥
c2BranchingControlDiffers ()

------------------------------------------------------------------------
-- C3 restriction.  Over the real weight-counting carrier the two nontrivial
-- residue classes occur with equal multiplicity because m and -m are paired.
------------------------------------------------------------------------

record C3Branching : Set where
  constructor c3Branching
  field
    residue0Multiplicity : Nat
    residue1Multiplicity : Nat
    residue2Multiplicity : Nat

open C3Branching public

c3Total : C3Branching → Nat
c3Total spectrum =
  residue0Multiplicity spectrum
  + residue1Multiplicity spectrum
  + residue2Multiplicity spectrum

j4C3Branching : C3Branching
j4C3Branching = c3Branching 3 3 3

j5C3Branching : C3Branching
j5C3Branching = c3Branching 3 4 4

j4C3BranchingConservesDimension : c3Total j4C3Branching ≡ Scan.oddDimension 4
j4C3BranchingConservesDimension = refl

j5C3BranchingConservesDimension : c3Total j5C3Branching ≡ Scan.oddDimension 5
j5C3BranchingConservesDimension = refl

j4C3FixedMultiplicityMatchesScan :
  residue0Multiplicity j4C3Branching ≡ Scan.fixedC3 4
j4C3FixedMultiplicityMatchesScan = refl

j5C3FixedMultiplicityMatchesScan :
  residue0Multiplicity j5C3Branching ≡ Scan.fixedC3 5
j5C3FixedMultiplicityMatchesScan = refl

c3BranchingControlDiffers : j4C3Branching ≡ j5C3Branching → ⊥
c3BranchingControlDiffers ()

------------------------------------------------------------------------
-- Combined result: the fixed-space quotient loses information that is present
-- in the full cyclic branching spectrum.
------------------------------------------------------------------------

FixedPair : Set
FixedPair = Nat × Nat

BranchingControlPair : Set
BranchingControlPair = C2Branching × C3Branching

j4FixedPairEqualsJ5 : Scan.fixedPair 4 ≡ Scan.fixedPair 5
j4FixedPairEqualsJ5 = refl

j4BranchingControl : BranchingControlPair
j4BranchingControl = j4C2Branching , j4C3Branching

j5BranchingControl : BranchingControlPair
j5BranchingControl = j5C2Branching , j5C3Branching

fullBranchingSeparatesJ4J5 : j4BranchingControl ≡ j5BranchingControl → ⊥
fullBranchingSeparatesJ4J5 ()
