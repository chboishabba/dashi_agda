module DASHI.Physics.YangMills.BalabanSelectedGreenDiagonalEndpointAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Convert the Round60 polarization theorem into the exact endpoint shape
-- consumed by BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact.
-- A caller supplies only EIGHT uniform upper bounds:
--
--   U^S_d >= <S_d,K+S_d>,   d=1..4
--   U^D_e >= <D_e,K+D_e>,   e=1..4.
--
-- The sixteen signed Green lower endpoints are then generated mechanically:
--
--   L_de = -(U^S_d + U^D_e)/2
--        <= <S_d,K+D_e>.
--
-- Thus G2 no longer needs sixteen independently certified signed Green boxes.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as DegreeGreen
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact as Polar

half : ℚ
half = + 1 / 2

record DiagonalDegreeEnergyUpperEnvelope
    {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor) : Set where
  field
    sourceEnergyUpper : Degree.MobiusDegree → ℚ
    defectEnergyUpper : Degree.MobiusDegree → ℚ
    sourceEnergyUpperSound : ∀ degree →
      Polar.sourceDegreeEnergy atoms degree ≤ sourceEnergyUpper degree
    defectEnergyUpperSound : ∀ degree →
      Polar.defectDegreeEnergy atoms degree ≤ defectEnergyUpper degree
open DiagonalDegreeEnergyUpperEnvelope public

generatedGreenLower :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    {atoms : Atoms.SelectedConstraintAtomData
      {Multiplier} pseudoData firstVariationCovector rawExtractor} →
  DiagonalDegreeEnergyUpperEnvelope atoms →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
generatedGreenLower envelope sourceDegree defectDegree =
  half *
    (- (sourceEnergyUpper envelope sourceDegree
      + defectEnergyUpper envelope defectDegree))

generatedGreenLowerSound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    {atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor}
    (envelope : DiagonalDegreeEnergyUpperEnvelope atoms)
    sourceDegree defectDegree →
  generatedGreenLower envelope sourceDegree defectDegree
  ≤ DegreeGreen.greenDegreePairing atoms sourceDegree defectDegree
generatedGreenLowerSound
    {pseudoData = pseudoData} {atoms = atoms}
    envelope sourceDegree defectDegree =
  let
    sourceEnergy = Polar.sourceDegreeEnergy atoms sourceDegree
    defectEnergy = Polar.defectDegreeEnergy atoms defectDegree
    sourceUpper = sourceEnergyUpper envelope sourceDegree
    defectUpper = defectEnergyUpper envelope defectDegree
    green = DegreeGreen.greenDegreePairing atoms sourceDegree defectDegree

    energySumUpper :
      sourceEnergy + defectEnergy ≤ sourceUpper + defectUpper
    energySumUpper = ℚP.+-mono-≤
      (sourceEnergyUpperSound envelope sourceDegree)
      (defectEnergyUpperSound envelope defectDegree)

    negativeUpperBelowNegativeEnergy :
      - (sourceUpper + defectUpper)
      ≤ - (sourceEnergy + defectEnergy)
    negativeUpperBelowNegativeEnergy = ℚP.neg-antimono-≤ energySumUpper

    denominatorCleared :
      - (sourceUpper + defectUpper) ≤ green + green
    denominatorCleared = ℚP.≤-trans
      negativeUpperBelowNegativeEnergy
      (Polar.degreeGreenLowerFromDiagonalEnergies
        atoms sourceDegree defectDegree)

    scaled :
      half * (- (sourceUpper + defectUpper))
      ≤ half * (green + green)
    scaled = Norm.scaleNonnegative half
      (ℚP.nonNegative⁻¹ half) denominatorCleared
  in
  subst
    (λ upper →
      half * (- (sourceUpper + defectUpper)) ≤ upper)
    (ℚRing.solve-∀ green)
    scaled

diagonalEightGenerateSixteenGreenEndpointsLevel : ProofLevel
diagonalEightGenerateSixteenGreenEndpointsLevel = machineChecked

-- Physical A2 leaf after this adapter: certify only the eight diagonal energy
-- upper bounds uniformly on the selected region.
selectedRegionEightDiagonalEndpointBoundsLevel : ProofLevel
selectedRegionEightDiagonalEndpointBoundsLevel = conditional
