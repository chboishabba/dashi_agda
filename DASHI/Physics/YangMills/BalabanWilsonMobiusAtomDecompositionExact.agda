module DASHI.Physics.YangMills.BalabanWilsonMobiusAtomDecompositionExact where

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
-- Construct the zeta/Möbius transform of the literal four-bond Boolean cube
-- and prove both inversions by exact rational ring normalization.  The same
-- subset order is then connected definitionally to the repository's ordered
-- noncommutative four-factor Wilson expansion.  The degree-one projection is
-- exactly the four-singleton term already consumed by the selected-background
-- reducer; degrees two, three and four are the pair, triple and quartic atoms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition

record CubeSignal : Set where
  constructor cubeSignal
  field
    atEmpty : ℚ
    at0 at1 at2 at3 : ℚ
    at01 at02 at03 at12 at13 at23 : ℚ
    at012 at013 at023 at123 : ℚ
    at0123 : ℚ

open CubeSignal public

cubeSignalAt : CubeSignal → Cube.Subset4 → ℚ
cubeSignalAt signal Cube.empty = atEmpty signal
cubeSignalAt signal Cube.s0 = at0 signal
cubeSignalAt signal Cube.s1 = at1 signal
cubeSignalAt signal Cube.s2 = at2 signal
cubeSignalAt signal Cube.s3 = at3 signal
cubeSignalAt signal Cube.s01 = at01 signal
cubeSignalAt signal Cube.s02 = at02 signal
cubeSignalAt signal Cube.s03 = at03 signal
cubeSignalAt signal Cube.s12 = at12 signal
cubeSignalAt signal Cube.s13 = at13 signal
cubeSignalAt signal Cube.s23 = at23 signal
cubeSignalAt signal Cube.s012 = at012 signal
cubeSignalAt signal Cube.s013 = at013 signal
cubeSignalAt signal Cube.s023 = at023 signal
cubeSignalAt signal Cube.s123 = at123 signal
cubeSignalAt signal Cube.s0123 = at0123 signal

cubeSignalExt :
  ∀ {left right} →
  atEmpty left ≡ atEmpty right →
  at0 left ≡ at0 right → at1 left ≡ at1 right →
  at2 left ≡ at2 right → at3 left ≡ at3 right →
  at01 left ≡ at01 right → at02 left ≡ at02 right →
  at03 left ≡ at03 right → at12 left ≡ at12 right →
  at13 left ≡ at13 right → at23 left ≡ at23 right →
  at012 left ≡ at012 right → at013 left ≡ at013 right →
  at023 left ≡ at023 right → at123 left ≡ at123 right →
  at0123 left ≡ at0123 right →
  left ≡ right
cubeSignalExt
  {cubeSignal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}
  {cubeSignal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl = refl

mobiusTransform : CubeSignal → CubeSignal
mobiusTransform f = cubeSignal
  (atEmpty f)
  (at0 f - atEmpty f)
  (at1 f - atEmpty f)
  (at2 f - atEmpty f)
  (at3 f - atEmpty f)
  (at01 f - at0 f - at1 f + atEmpty f)
  (at02 f - at0 f - at2 f + atEmpty f)
  (at03 f - at0 f - at3 f + atEmpty f)
  (at12 f - at1 f - at2 f + atEmpty f)
  (at13 f - at1 f - at3 f + atEmpty f)
  (at23 f - at2 f - at3 f + atEmpty f)
  (at012 f - at01 f - at02 f - at12 f
    + at0 f + at1 f + at2 f - atEmpty f)
  (at013 f - at01 f - at03 f - at13 f
    + at0 f + at1 f + at3 f - atEmpty f)
  (at023 f - at02 f - at03 f - at23 f
    + at0 f + at2 f + at3 f - atEmpty f)
  (at123 f - at12 f - at13 f - at23 f
    + at1 f + at2 f + at3 f - atEmpty f)
  (at0123 f
    - at012 f - at013 f - at023 f - at123 f
    + at01 f + at02 f + at03 f + at12 f + at13 f + at23 f
    - at0 f - at1 f - at2 f - at3 f
    + atEmpty f)

zetaTransform : CubeSignal → CubeSignal
zetaTransform a = cubeSignal
  (atEmpty a)
  (atEmpty a + at0 a)
  (atEmpty a + at1 a)
  (atEmpty a + at2 a)
  (atEmpty a + at3 a)
  (atEmpty a + at0 a + at1 a + at01 a)
  (atEmpty a + at0 a + at2 a + at02 a)
  (atEmpty a + at0 a + at3 a + at03 a)
  (atEmpty a + at1 a + at2 a + at12 a)
  (atEmpty a + at1 a + at3 a + at13 a)
  (atEmpty a + at2 a + at3 a + at23 a)
  (atEmpty a + at0 a + at1 a + at2 a
    + at01 a + at02 a + at12 a + at012 a)
  (atEmpty a + at0 a + at1 a + at3 a
    + at01 a + at03 a + at13 a + at013 a)
  (atEmpty a + at0 a + at2 a + at3 a
    + at02 a + at03 a + at23 a + at023 a)
  (atEmpty a + at1 a + at2 a + at3 a
    + at12 a + at13 a + at23 a + at123 a)
  (atEmpty a
    + at0 a + at1 a + at2 a + at3 a
    + at01 a + at02 a + at03 a + at12 a + at13 a + at23 a
    + at012 a + at013 a + at023 a + at123 a
    + at0123 a)

zetaAfterMobiusExact : ∀ signal →
  zetaTransform (mobiusTransform signal) ≡ signal
zetaAfterMobiusExact
    (cubeSignal e a0 a1 a2 a3
      a01 a02 a03 a12 a13 a23
      a012 a013 a023 a123 a0123) =
  cubeSignalExt
    (ℚRing.solve-∀ e)
    (ℚRing.solve-∀ e a0)
    (ℚRing.solve-∀ e a1)
    (ℚRing.solve-∀ e a2)
    (ℚRing.solve-∀ e a3)
    (ℚRing.solve-∀ e a0 a1 a01)
    (ℚRing.solve-∀ e a0 a2 a02)
    (ℚRing.solve-∀ e a0 a3 a03)
    (ℚRing.solve-∀ e a1 a2 a12)
    (ℚRing.solve-∀ e a1 a3 a13)
    (ℚRing.solve-∀ e a2 a3 a23)
    (ℚRing.solve-∀ e a0 a1 a2 a01 a02 a12 a012)
    (ℚRing.solve-∀ e a0 a1 a3 a01 a03 a13 a013)
    (ℚRing.solve-∀ e a0 a2 a3 a02 a03 a23 a023)
    (ℚRing.solve-∀ e a1 a2 a3 a12 a13 a23 a123)
    (ℚRing.solve-∀
      e a0 a1 a2 a3 a01 a02 a03 a12 a13 a23
      a012 a013 a023 a123 a0123)

mobiusAfterZetaExact : ∀ atoms →
  mobiusTransform (zetaTransform atoms) ≡ atoms
mobiusAfterZetaExact
    (cubeSignal e a0 a1 a2 a3
      a01 a02 a03 a12 a13 a23
      a012 a013 a023 a123 a0123) =
  cubeSignalExt
    (ℚRing.solve-∀ e)
    (ℚRing.solve-∀ e a0)
    (ℚRing.solve-∀ e a1)
    (ℚRing.solve-∀ e a2)
    (ℚRing.solve-∀ e a3)
    (ℚRing.solve-∀ e a0 a1 a01)
    (ℚRing.solve-∀ e a0 a2 a02)
    (ℚRing.solve-∀ e a0 a3 a03)
    (ℚRing.solve-∀ e a1 a2 a12)
    (ℚRing.solve-∀ e a1 a3 a13)
    (ℚRing.solve-∀ e a2 a3 a23)
    (ℚRing.solve-∀ e a0 a1 a2 a01 a02 a12 a012)
    (ℚRing.solve-∀ e a0 a1 a3 a01 a03 a13 a013)
    (ℚRing.solve-∀ e a0 a2 a3 a02 a03 a23 a023)
    (ℚRing.solve-∀ e a1 a2 a3 a12 a13 a23 a123)
    (ℚRing.solve-∀
      e a0 a1 a2 a3 a01 a02 a03 a12 a13 a23
      a012 a013 a023 a123 a0123)

degreeZeroPart degreeOnePart degreeTwoPart
degreeThreePart degreeFourPart : CubeSignal → ℚ
degreeZeroPart atoms = atEmpty atoms
degreeOnePart atoms = at0 atoms + at1 atoms + at2 atoms + at3 atoms
degreeTwoPart atoms =
  at01 atoms + at02 atoms + at03 atoms
  + at12 atoms + at13 atoms + at23 atoms
degreeThreePart atoms =
  at012 atoms + at013 atoms + at023 atoms + at123 atoms
degreeFourPart atoms = at0123 atoms

fullAtomMass : CubeSignal → ℚ
fullAtomMass atoms =
  degreeZeroPart atoms
  + degreeOnePart atoms
  + degreeTwoPart atoms
  + degreeThreePart atoms
  + degreeFourPart atoms

fullSignalIsAllMobiusAtoms : ∀ signal →
  at0123 signal ≡ fullAtomMass (mobiusTransform signal)
fullSignalIsAllMobiusAtoms
    (cubeSignal e a0 a1 a2 a3
      a01 a02 a03 a12 a13 a23
      a012 a013 a023 a123 a0123) =
  ℚRing.solve-∀
    e a0 a1 a2 a3 a01 a02 a03 a12 a13 a23
    a012 a013 a023 a123 a0123

subsetQuaternionAtom :
  Cube.Subset4 →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
subsetQuaternionAtom subset a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    d0 = Partition.factorDefect a0 b0
    d1 = Partition.factorDefect a1 b1
    d2 = Partition.factorDefect a2 b2
    d3 = Partition.factorDefect a3 b3
  in
  case subset of λ where
    Cube.empty → Telescope.orderedProduct4 b0 b1 b2 b3
    Cube.s0 → Telescope.orderedProduct4 d0 b1 b2 b3
    Cube.s1 → Telescope.orderedProduct4 b0 d1 b2 b3
    Cube.s2 → Telescope.orderedProduct4 b0 b1 d2 b3
    Cube.s3 → Telescope.orderedProduct4 b0 b1 b2 d3
    Cube.s01 → Telescope.orderedProduct4 d0 d1 b2 b3
    Cube.s02 → Telescope.orderedProduct4 d0 b1 d2 b3
    Cube.s03 → Telescope.orderedProduct4 d0 b1 b2 d3
    Cube.s12 → Telescope.orderedProduct4 b0 d1 d2 b3
    Cube.s13 → Telescope.orderedProduct4 b0 d1 b2 d3
    Cube.s23 → Telescope.orderedProduct4 b0 b1 d2 d3
    Cube.s012 → Telescope.orderedProduct4 d0 d1 d2 b3
    Cube.s013 → Telescope.orderedProduct4 d0 d1 b2 d3
    Cube.s023 → Telescope.orderedProduct4 d0 b1 d2 d3
    Cube.s123 → Telescope.orderedProduct4 b0 d1 d2 d3
    Cube.s0123 → Telescope.orderedProduct4 d0 d1 d2 d3

fourFactorDegreeOneAtoms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorDegreeOneAtoms a0 a1 a2 a3 b0 b1 b2 b3 =
  subsetQuaternionAtom Cube.s0 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s1 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s2 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s3 a0 a1 a2 a3 b0 b1 b2 b3 ∷ []

fourFactorDegreesTwoToFourAtoms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorDegreesTwoToFourAtoms a0 a1 a2 a3 b0 b1 b2 b3 =
  subsetQuaternionAtom Cube.s01 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s02 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s03 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s12 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s13 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s23 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s012 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s013 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s023 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s123 a0 a1 a2 a3 b0 b1 b2 b3 ∷
  subsetQuaternionAtom Cube.s0123 a0 a1 a2 a3 b0 b1 b2 b3 ∷ []

degreeOneAtomsAreLiteralSingletons :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  fourFactorDegreeOneAtoms a0 a1 a2 a3 b0 b1 b2 b3
  ≡ Partition.fourFactorSingletonTerms
      a0 a1 a2 a3 b0 b1 b2 b3
degreeOneAtomsAreLiteralSingletons
  a0 a1 a2 a3 b0 b1 b2 b3 = refl

degreesTwoToFourAreLiteralHigherTerms :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  fourFactorDegreesTwoToFourAtoms a0 a1 a2 a3 b0 b1 b2 b3
  ≡ Partition.fourFactorHigherTerms
      a0 a1 a2 a3 b0 b1 b2 b3
degreesTwoToFourAreLiteralHigherTerms
  a0 a1 a2 a3 b0 b1 b2 b3 = refl

degreeOneQuaternionProjection :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
degreeOneQuaternionProjection a0 a1 a2 a3 b0 b1 b2 b3 =
  Q.sumQuaternion
    (fourFactorDegreeOneAtoms a0 a1 a2 a3 b0 b1 b2 b3)

degreeOneProjectionIsLiteralLinearPart :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  degreeOneQuaternionProjection a0 a1 a2 a3 b0 b1 b2 b3
  ≡ Partition.fourFactorLinearPart
      a0 a1 a2 a3 b0 b1 b2 b3
degreeOneProjectionIsLiteralLinearPart
    a0 a1 a2 a3 b0 b1 b2 b3 =
  cong Q.sumQuaternion
    (degreeOneAtomsAreLiteralSingletons
      a0 a1 a2 a3 b0 b1 b2 b3)

allNonemptyQuaternionAtoms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
allNonemptyQuaternionAtoms a0 a1 a2 a3 b0 b1 b2 b3 =
  fourFactorDegreeOneAtoms a0 a1 a2 a3 b0 b1 b2 b3
  ++ fourFactorDegreesTwoToFourAtoms a0 a1 a2 a3 b0 b1 b2 b3

allNonemptyAtomsSumToProductDefect :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Q.sumQuaternion
    (allNonemptyQuaternionAtoms a0 a1 a2 a3 b0 b1 b2 b3)
  ≡ Telescope._-q_
      (Telescope.orderedProduct4 a0 a1 a2 a3)
      (Telescope.orderedProduct4 b0 b1 b2 b3)
allNonemptyAtomsSumToProductDefect
    a0 a1 a2 a3 b0 b1 b2 b3 =
  trans
    (Q.sumQuaternionAppend
      (fourFactorDegreeOneAtoms a0 a1 a2 a3 b0 b1 b2 b3)
      (fourFactorDegreesTwoToFourAtoms a0 a1 a2 a3 b0 b1 b2 b3))
    (trans
      (cong₂ Q._+q_
        (degreeOneProjectionIsLiteralLinearPart
          a0 a1 a2 a3 b0 b1 b2 b3)
        (cong Q.sumQuaternion
          (degreesTwoToFourAreLiteralHigherTerms
            a0 a1 a2 a3 b0 b1 b2 b3)))
      (sym
        (Partition.fourFactorLinearNonlinearExpansionExact
          a0 a1 a2 a3 b0 b1 b2 b3)))

booleanMobiusInversionLevel : ProofLevel
booleanMobiusInversionLevel = machineChecked

wilsonDegreeOneIdentificationLevel : ProofLevel
wilsonDegreeOneIdentificationLevel = machineChecked

wilsonNonemptySubsetExpansionLevel : ProofLevel
wilsonNonemptySubsetExpansionLevel = machineChecked
