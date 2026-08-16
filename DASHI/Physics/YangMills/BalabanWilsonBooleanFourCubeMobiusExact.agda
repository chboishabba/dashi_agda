module DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Give the literal Boolean four-cube its canonical Möbius transform. For a
-- function F on the sixteen plaquette-factor subsets, define
--
--   a(S) = sum_{T subseteq S} (-1)^(|S|-|T|) F(T).
--
-- Since the carrier is fixed and finite, the transform is written out
-- definitionally rather than hiding subset enumeration behind another
-- certificate. Exact rational normalization proves
--
--   sum_{S nonempty} a(S) = F({0,1,2,3}) - F(empty).
--
-- Hence whenever the background/empty evaluation vanishes, the fifteen Wilson
-- atoms reconstruct the full plaquette value automatically. This removes the
-- old need to supply arbitrary atoms together with a reconstruction equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

mobiusAtom : (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
mobiusAtom value Cube.empty = value Cube.empty

mobiusAtom value Cube.s0 =
  value Cube.s0 - value Cube.empty
mobiusAtom value Cube.s1 =
  value Cube.s1 - value Cube.empty
mobiusAtom value Cube.s2 =
  value Cube.s2 - value Cube.empty
mobiusAtom value Cube.s3 =
  value Cube.s3 - value Cube.empty

mobiusAtom value Cube.s01 =
  value Cube.s01 - value Cube.s0 - value Cube.s1 + value Cube.empty
mobiusAtom value Cube.s02 =
  value Cube.s02 - value Cube.s0 - value Cube.s2 + value Cube.empty
mobiusAtom value Cube.s03 =
  value Cube.s03 - value Cube.s0 - value Cube.s3 + value Cube.empty
mobiusAtom value Cube.s12 =
  value Cube.s12 - value Cube.s1 - value Cube.s2 + value Cube.empty
mobiusAtom value Cube.s13 =
  value Cube.s13 - value Cube.s1 - value Cube.s3 + value Cube.empty
mobiusAtom value Cube.s23 =
  value Cube.s23 - value Cube.s2 - value Cube.s3 + value Cube.empty

mobiusAtom value Cube.s012 =
  value Cube.s012
  - value Cube.s01 - value Cube.s02 - value Cube.s12
  + value Cube.s0 + value Cube.s1 + value Cube.s2
  - value Cube.empty
mobiusAtom value Cube.s013 =
  value Cube.s013
  - value Cube.s01 - value Cube.s03 - value Cube.s13
  + value Cube.s0 + value Cube.s1 + value Cube.s3
  - value Cube.empty
mobiusAtom value Cube.s023 =
  value Cube.s023
  - value Cube.s02 - value Cube.s03 - value Cube.s23
  + value Cube.s0 + value Cube.s2 + value Cube.s3
  - value Cube.empty
mobiusAtom value Cube.s123 =
  value Cube.s123
  - value Cube.s12 - value Cube.s13 - value Cube.s23
  + value Cube.s1 + value Cube.s2 + value Cube.s3
  - value Cube.empty

mobiusAtom value Cube.s0123 =
  value Cube.s0123
  - value Cube.s012 - value Cube.s013 - value Cube.s023 - value Cube.s123
  + value Cube.s01 + value Cube.s02 + value Cube.s03
  + value Cube.s12 + value Cube.s13 + value Cube.s23
  - value Cube.s0 - value Cube.s1 - value Cube.s2 - value Cube.s3
  + value Cube.empty

nonemptyMobiusSumExact :
  ∀ value →
  Sums.sumRational Cube.nonemptySubsets4 (mobiusAtom value)
  ≡ value Cube.s0123 - value Cube.empty
nonemptyMobiusSumExact value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)

nonemptyMobiusSumWithZeroBackground :
  ∀ value → value Cube.empty ≡ 0ℚ →
  Sums.sumRational Cube.nonemptySubsets4 (mobiusAtom value)
  ≡ value Cube.s0123
nonemptyMobiusSumWithZeroBackground value emptyZero =
  trans
    (nonemptyMobiusSumExact value)
    (subst
      (λ background → value Cube.s0123 - background ≡ value Cube.s0123)
      (sym emptyZero)
      (ℚRing.solve-∀ (value Cube.s0123)))

booleanFourCubeMobiusDefinitionLevel : ProofLevel
booleanFourCubeMobiusDefinitionLevel = machineChecked

booleanFourCubeMobiusReconstructionLevel : ProofLevel
booleanFourCubeMobiusReconstructionLevel = machineChecked
