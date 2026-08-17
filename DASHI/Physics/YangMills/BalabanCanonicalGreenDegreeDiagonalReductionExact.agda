module DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Apply the Round60 K+ positivity/polarization theorem to the SAME canonical
-- four source-degree and four defect-degree vectors already generating the
-- Round58 4x4 Green table.  Thus each signed Green block is controlled by two
-- diagonal energies without changing the physical carrier or re-enumerating
-- the Boolean-cube subsets.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact as Polarization
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sourceDegreeEnergy :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor) →
  Degree.MobiusDegree → ℚ
sourceDegreeEnergy {pseudoData = pseudoData} atoms degree =
  Positive.pseudoinverseEnergy pseudoData
    (GreenDegree.sourceDegreeVector atoms degree)

defectDegreeEnergy :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor) →
  Degree.MobiusDegree → ℚ
defectDegreeEnergy {pseudoData = pseudoData} atoms degree =
  Positive.pseudoinverseEnergy pseudoData
    (GreenDegree.defectDegreeVector atoms degree)

greenDegreeDoubleLower :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    leftDegree rightDegree →
  - (sourceDegreeEnergy atoms leftDegree
      + defectDegreeEnergy atoms rightDegree)
  ≤ GreenDegree.greenDegreePairing atoms leftDegree rightDegree
      + GreenDegree.greenDegreePairing atoms leftDegree rightDegree
greenDegreeDoubleLower {pseudoData = pseudoData}
    atoms leftDegree rightDegree =
  Polarization.polarizationGreenLowerBound pseudoData
    (GreenDegree.sourceDegreeVector atoms leftDegree)
    (GreenDegree.defectDegreeVector atoms rightDegree)

-- Divide the denominator-cleared polarization inequality by two using the
-- exact nonnegative rational scale 1/2.
greenDegreeHalfEnergyLower :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    leftDegree rightDegree →
  - ((+ 1 / 2)
      * (sourceDegreeEnergy atoms leftDegree
        + defectDegreeEnergy atoms rightDegree))
  ≤ GreenDegree.greenDegreePairing atoms leftDegree rightDegree
greenDegreeHalfEnergyLower atoms leftDegree rightDegree =
  let
    sourceEnergy = sourceDegreeEnergy atoms leftDegree
    defectEnergy = defectDegreeEnergy atoms rightDegree
    green = GreenDegree.greenDegreePairing atoms leftDegree rightDegree

    scaled =
      Norm.scaleNonnegative
        (+ 1 / 2)
        (ℚP.nonNegative⁻¹ (+ 1 / 2))
        (greenDegreeDoubleLower atoms leftDegree rightDegree)
  in
  subst
    (λ lower → lower ≤ green)
    (ℚRing.solve-∀ sourceEnergy defectEnergy)
    (subst
      (λ upper →
        (+ 1 / 2) * (- (sourceEnergy + defectEnergy)) ≤ upper)
      (ℚRing.solve-∀ green)
      scaled)

canonicalGreenDegreeDiagonalReductionLevel : ProofLevel
canonicalGreenDegreeDiagonalReductionLevel = machineChecked

-- Physical frontier after this theorem: upper-bound four source diagonal
-- energies and four defect diagonal energies uniformly on the selected region.
selectedRegionEightDiagonalEnergyBoundsLevel : ProofLevel
selectedRegionEightDiagonalEnergyBoundsLevel = conditional
