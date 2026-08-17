module DASHI.Physics.YangMills.BalabanP33SelectedGreenSubsetOrbitReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Before attempting Walsh diagonalization of the selected Green atom matrix,
-- exploit the weaker symmetry that is much more likely to survive physically:
-- simultaneous S4 relabelling of the four plaquette-factor slots.
--
-- A nonempty raw atom has four possible degree classes 1,2,3,4 with exact
-- multiplicities 4,6,4,1.  An ORDERED pair of nonempty subsets has only 26 S4
-- orbit signatures, classified by
--
--      (|S|, |T|, |S cap T|),
--
-- instead of 15*15 = 225 independent entries.  This module computes those 26
-- classes and their exact multiplicities, then proves the resulting weighted
-- finite-sum formulas.  A physical S4-equivariance theorem can therefore reduce
-- G2 Green interval production from 225 boxes to at most 26 representative
-- boxes without assuming the much stronger XOR-convolution/Walsh hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as O

infixl 7 _and_
_and_ : Bool → Bool → Bool
false and right = false
true and right = right

bitNat : Bool → Nat
bitNat false = 0
bitNat true = 1

intersectionCardinality : Cube.Subset4 → Cube.Subset4 → Nat
intersectionCardinality left right =
  bitNat (Cube.contains Cube.slot0 left and Cube.contains Cube.slot0 right)
  + bitNat (Cube.contains Cube.slot1 left and Cube.contains Cube.slot1 right)
  + bitNat (Cube.contains Cube.slot2 left and Cube.contains Cube.slot2 right)
  + bitNat (Cube.contains Cube.slot3 left and Cube.contains Cube.slot3 right)

data PairOrbitCode : Set where
  emptyCode : PairOrbitCode
  c110 c111 c120 c121 c130 c131 c141 : PairOrbitCode
  c210 c211 c220 c221 c222 c231 c232 c242 : PairOrbitCode
  c310 c311 c321 c322 c332 c333 c343 : PairOrbitCode
  c411 c422 c433 c444 : PairOrbitCode

pairOrbitCode : Cube.Subset4 → Cube.Subset4 → PairOrbitCode
pairOrbitCode left right
  with Cube.subsetCardinality left | Cube.subsetCardinality right | intersectionCardinality left right
... | 1 | 1 | 0 = c110
... | 1 | 1 | 1 = c111
... | 1 | 2 | 0 = c120
... | 1 | 2 | 1 = c121
... | 1 | 3 | 0 = c130
... | 1 | 3 | 1 = c131
... | 1 | 4 | 1 = c141
... | 2 | 1 | 0 = c210
... | 2 | 1 | 1 = c211
... | 2 | 2 | 0 = c220
... | 2 | 2 | 1 = c221
... | 2 | 2 | 2 = c222
... | 2 | 3 | 1 = c231
... | 2 | 3 | 2 = c232
... | 2 | 4 | 2 = c242
... | 3 | 1 | 0 = c310
... | 3 | 1 | 1 = c311
... | 3 | 2 | 1 = c321
... | 3 | 2 | 2 = c322
... | 3 | 3 | 2 = c332
... | 3 | 3 | 3 = c333
... | 3 | 4 | 3 = c343
... | 4 | 1 | 1 = c411
... | 4 | 2 | 2 = c422
... | 4 | 3 | 3 = c433
... | 4 | 4 | 4 = c444
... | _ | _ | _ = emptyCode

record RawDegreeValues : Set where
  constructor rawDegreeValues
  field d1 d2 d3 d4 : ℚ
open RawDegreeValues public

rawDegreeValueAt : RawDegreeValues → Cube.Subset4 → ℚ
rawDegreeValueAt values subset with Cube.subsetCardinality subset
... | 1 = d1 values
... | 2 = d2 values
... | 3 = d3 values
... | 4 = d4 values
... | _ = 0ℚ

rawDegreeWeightedSum : RawDegreeValues → ℚ
rawDegreeWeightedSum values =
  (+ 4 / 1) * d1 values + (+ 6 / 1) * d2 values
  + (+ 4 / 1) * d3 values + d4 values

rawDegreeSumExact : ∀ values →
  Sums.sumRational Cube.nonemptySubsets4 (rawDegreeValueAt values)
  ≡ rawDegreeWeightedSum values
rawDegreeSumExact (rawDegreeValues a b c d) = ℚRing.solve-∀ a b c d

record PairOrbitValues : Set where
  constructor pairOrbitValues
  field
    v110 v111 v120 v121 v130 v131 v141 : ℚ
    v210 v211 v220 v221 v222 v231 v232 v242 : ℚ
    v310 v311 v321 v322 v332 v333 v343 : ℚ
    v411 v422 v433 v444 : ℚ
open PairOrbitValues public

pairOrbitValue : PairOrbitValues → PairOrbitCode → ℚ
pairOrbitValue values emptyCode = 0ℚ
pairOrbitValue values c110 = v110 values
pairOrbitValue values c111 = v111 values
pairOrbitValue values c120 = v120 values
pairOrbitValue values c121 = v121 values
pairOrbitValue values c130 = v130 values
pairOrbitValue values c131 = v131 values
pairOrbitValue values c141 = v141 values
pairOrbitValue values c210 = v210 values
pairOrbitValue values c211 = v211 values
pairOrbitValue values c220 = v220 values
pairOrbitValue values c221 = v221 values
pairOrbitValue values c222 = v222 values
pairOrbitValue values c231 = v231 values
pairOrbitValue values c232 = v232 values
pairOrbitValue values c242 = v242 values
pairOrbitValue values c310 = v310 values
pairOrbitValue values c311 = v311 values
pairOrbitValue values c321 = v321 values
pairOrbitValue values c322 = v322 values
pairOrbitValue values c332 = v332 values
pairOrbitValue values c333 = v333 values
pairOrbitValue values c343 = v343 values
pairOrbitValue values c411 = v411 values
pairOrbitValue values c422 = v422 values
pairOrbitValue values c433 = v433 values
pairOrbitValue values c444 = v444 values

pairValueAt : PairOrbitValues → Cube.Subset4 → Cube.Subset4 → ℚ
pairValueAt values left right = pairOrbitValue values (pairOrbitCode left right)

pairOrbitWeightedSum : PairOrbitValues → ℚ
pairOrbitWeightedSum v =
  (+ 12 / 1) * v110 v + (+ 4 / 1) * v111 v
  + (+ 12 / 1) * v120 v + (+ 12 / 1) * v121 v
  + (+ 4 / 1) * v130 v + (+ 12 / 1) * v131 v + (+ 4 / 1) * v141 v
  + (+ 12 / 1) * v210 v + (+ 12 / 1) * v211 v
  + (+ 6 / 1) * v220 v + (+ 24 / 1) * v221 v + (+ 6 / 1) * v222 v
  + (+ 12 / 1) * v231 v + (+ 12 / 1) * v232 v + (+ 6 / 1) * v242 v
  + (+ 4 / 1) * v310 v + (+ 12 / 1) * v311 v
  + (+ 12 / 1) * v321 v + (+ 12 / 1) * v322 v
  + (+ 12 / 1) * v332 v + (+ 4 / 1) * v333 v + (+ 4 / 1) * v343 v
  + (+ 4 / 1) * v411 v + (+ 6 / 1) * v422 v + (+ 4 / 1) * v433 v
  + v444 v

pairOrbitFiniteSum : PairOrbitValues → ℚ
pairOrbitFiniteSum values =
  Sums.sumRational Cube.nonemptySubsets4
    (λ left → Sums.sumRational Cube.nonemptySubsets4 (pairValueAt values left))

pairOrbitSumExact : ∀ values → pairOrbitFiniteSum values ≡ pairOrbitWeightedSum values
pairOrbitSumExact
  (pairOrbitValues a110 a111 a120 a121 a130 a131 a141
    a210 a211 a220 a221 a222 a231 a232 a242
    a310 a311 a321 a322 a332 a333 a343
    a411 a422 a433 a444) =
  ℚRing.solve-∀
    a110 a111 a120 a121 a130 a131 a141
    a210 a211 a220 a221 a222 a231 a232 a242
    a310 a311 a321 a322 a332 a333 a343
    a411 a422 a433 a444

record RawDegreeInvariantData (family : O.CorrelatedResidualFamily) : Set₁ where
  field
    values : RawDegreeValues
    rawExact : ∀ subset → O.rawLocalizationAtom family subset ≡ rawDegreeValueAt values subset
open RawDegreeInvariantData public

rawTotalFromFourDegreeRepresentatives :
  ∀ {family} (data : RawDegreeInvariantData family) →
  O.rawLocalizationTotal family ≡ rawDegreeWeightedSum (values data)
rawTotalFromFourDegreeRepresentatives {family} data =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (O.rawLocalizationAtom family)
      (rawDegreeValueAt (values data))
      (rawExact data))
    (rawDegreeSumExact (values data))

record GreenPairOrbitInvariantData (family : O.CorrelatedResidualFamily) : Set₁ where
  field
    values : PairOrbitValues
    greenExact : ∀ left right →
      O.multiplierGreenAtom family left right ≡ pairValueAt values left right
open GreenPairOrbitInvariantData public

greenRowFromOrbitRepresentatives :
  ∀ {family} (data : GreenPairOrbitInvariantData family) left →
  Sums.sumRational Cube.nonemptySubsets4 (O.multiplierGreenAtom family left)
  ≡ Sums.sumRational Cube.nonemptySubsets4 (pairValueAt (values data) left)
greenRowFromOrbitRepresentatives {family} data left =
  Sums.sumRationalCong
    Cube.nonemptySubsets4
    (O.multiplierGreenAtom family left)
    (pairValueAt (values data) left)
    (greenExact data left)

greenTotalFromTwentySixOrbitRepresentatives :
  ∀ {family} (data : GreenPairOrbitInvariantData family) →
  O.greenPairTotal family ≡ pairOrbitWeightedSum (values data)
greenTotalFromTwentySixOrbitRepresentatives {family} data =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (λ left → Sums.sumRational Cube.nonemptySubsets4 (O.multiplierGreenAtom family left))
      (λ left → Sums.sumRational Cube.nonemptySubsets4 (pairValueAt (values data) left))
      (greenRowFromOrbitRepresentatives data))
    (pairOrbitSumExact (values data))

rawFourDegreeReductionLevel : ProofLevel
rawFourDegreeReductionLevel = machineChecked

greenTwentySixPairOrbitFiniteArithmeticLevel : ProofLevel
greenTwentySixPairOrbitFiniteArithmeticLevel = machineChecked

selectedRawSubsetS4EquivarianceLevel : ProofLevel
selectedRawSubsetS4EquivarianceLevel = conditional

selectedGreenSubsetS4EquivarianceLevel : ProofLevel
selectedGreenSubsetS4EquivarianceLevel = conditional
