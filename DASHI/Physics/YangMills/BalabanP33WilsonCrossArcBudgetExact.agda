module DASHI.Physics.YangMills.BalabanP33WilsonCrossArcBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The six already factorised right-inserted cross operators each contain the
-- four plaquette background links, distributed between prefix, middle and
-- suffix.  This module records that literal geometry rather than assigning a
-- worst-case anonymous support constant:
--
--   pair 01 : 1 + 1 + 2 = 4,
--   pair 02 : 1 + 2 + 1 = 4,
--   pair 03 : 1 + 3 + 0 = 4,
--   pair 12 : 2 + 1 + 1 = 4,
--   pair 13 : 2 + 2 + 0 = 4,
--   pair 23 : 3 + 1 + 0 = 4.
--
-- Each unordered pair occurs in both derivative orders.  Hence the complete
-- twelve-cross-atom product telescope has exactly
--
--   2 * 6 * 4 = 48
--
-- local link-defect occurrences.  At the local allocation rho/96 the complete
-- cross contribution is rho/2.  These are exact natural and rational
-- calculations, and are the finite multiplicity calculation consumed by the
-- physical Wilson-background estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

data WilsonCrossPair6 : Set where
  pair01 pair02 pair03 pair12 pair13 pair23 : WilsonCrossPair6

wilsonCrossPairs6 : List WilsonCrossPair6
wilsonCrossPairs6 =
  pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷ []

prefixLength middleLength suffixLength : WilsonCrossPair6 → Nat
prefixLength pair01 = 1
prefixLength pair02 = 1
prefixLength pair03 = 1
prefixLength pair12 = 2
prefixLength pair13 = 2
prefixLength pair23 = 3

middleLength pair01 = 1
middleLength pair02 = 2
middleLength pair03 = 3
middleLength pair12 = 1
middleLength pair13 = 2
middleLength pair23 = 1

suffixLength pair01 = 2
suffixLength pair02 = 1
suffixLength pair03 = 0
suffixLength pair12 = 1
suffixLength pair13 = 0
suffixLength pair23 = 0

crossArcLength : WilsonCrossPair6 → Nat
crossArcLength pair =
  prefixLength pair + middleLength pair + suffixLength pair

crossArcLengthIsFour : ∀ pair → crossArcLength pair ≡ 4
crossArcLengthIsFour pair01 = refl
crossArcLengthIsFour pair02 = refl
crossArcLengthIsFour pair03 = refl
crossArcLengthIsFour pair12 = refl
crossArcLengthIsFour pair13 = refl
crossArcLengthIsFour pair23 = refl

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (value ∷ values) = value + sumNat values

mapCrossArcLength : List WilsonCrossPair6 → List Nat
mapCrossArcLength [] = []
mapCrossArcLength (pair ∷ pairs) =
  crossArcLength pair ∷ mapCrossArcLength pairs

unorderedCrossPairCountExact : length wilsonCrossPairs6 ≡ 6
unorderedCrossPairCountExact = refl

unorderedCrossArcOccurrenceCountExact :
  sumNat (mapCrossArcLength wilsonCrossPairs6) ≡ 24
unorderedCrossArcOccurrenceCountExact = refl

orderedDerivativeMultiplicity : Nat
orderedDerivativeMultiplicity = 2

orderedCrossArcOccurrenceCount : Nat
orderedCrossArcOccurrenceCount =
  orderedDerivativeMultiplicity
    * sumNat (mapCrossArcLength wilsonCrossPairs6)

orderedCrossArcOccurrenceCountExact :
  orderedCrossArcOccurrenceCount ≡ 48
orderedCrossArcOccurrenceCountExact = refl

p33Radius : ℚ
p33Radius = + 1 / 8192

localCrossLinkAllocation : ℚ
localCrossLinkAllocation = p33Radius * (+ 1 / 96)

completeCrossBudget : ℚ
completeCrossBudget = (+ 48 / 1) * localCrossLinkAllocation

completeCrossBudgetIsHalfRadius :
  completeCrossBudget ≡ p33Radius * (+ 1 / 2)
completeCrossBudgetIsHalfRadius = ℚRing.solve []

wilsonCrossPairGeometryLevel : ProofLevel
wilsonCrossPairGeometryLevel = machineChecked

wilsonCrossArcMultiplicityLevel : ProofLevel
wilsonCrossArcMultiplicityLevel = machineChecked

wilsonCrossHalfRadiusArithmeticLevel : ProofLevel
wilsonCrossHalfRadiusArithmeticLevel = machineChecked
