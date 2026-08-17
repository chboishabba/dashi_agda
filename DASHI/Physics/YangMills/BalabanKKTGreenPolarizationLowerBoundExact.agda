module DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Round58 needs SIGN-SENSITIVE lower bounds on sixteen quantities
--
--   <S_d,K+ D_e>.
--
-- A norm upper bound on K+ cannot supply those signs.  The previous module
-- proves K+ is positive semidefinite from the existing Moore--Penrose laws.
-- This module now uses exact polarization:
--
--   0 <= <s+d,K+(s+d)>
--      = <s,K+s> + 2<s,K+d> + <d,K+d>,
--
-- hence, without absolute values,
--
--   -(<s,K+s> + <d,K+d>) <= 2<s,K+d>.
--
-- Therefore the sixteen cross-term LOWER bounds can be generated from only
-- the four source and four defect diagonal pseudoinverse energies.  This is a
-- genuine reduction of the A2 physical numerical/locality workload.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as DegreeGreen
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

------------------------------------------------------------------------
-- Local finite bilinearity.  The rectangular module exports matrix-action
-- additivity but not dot-additivity names, so prove the two needed identities
-- directly from the same finite-sum/Fubini primitives rather than relying on
-- nonexistent API aliases.
------------------------------------------------------------------------

finiteDotAddLeftExact :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left right target →
  Rect.finiteDot carrier (Rect.vectorAdd left right) target
  ≡ Rect.finiteDot carrier left target
    + Rect.finiteDot carrier right target
finiteDotAddLeftExact carrier left right target =
  trans
    (Sums.sumRationalCong (Matrix.coordinates carrier) _ _
      (λ index →
        ℚP.*-distribʳ-+ (left index) (right index) (target index)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ index → left index * target index)
      (λ index → right index * target index))

finiteDotAddRightExact :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left rightFirst rightSecond →
  Rect.finiteDot carrier left (Rect.vectorAdd rightFirst rightSecond)
  ≡ Rect.finiteDot carrier left rightFirst
    + Rect.finiteDot carrier left rightSecond
finiteDotAddRightExact carrier left rightFirst rightSecond =
  trans
    (Sums.sumRationalCong (Matrix.coordinates carrier) _ _
      (λ index →
        ℚP.*-distribˡ-+
          (left index) (rightFirst index) (rightSecond index)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ index → left index * rightFirst index)
      (λ index → left index * rightSecond index))

pseudoPairing :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Pseudo.MultiplierVector Multiplier →
  Pseudo.MultiplierVector Multiplier → ℚ
pseudoPairing pseudoData left right =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    left (Pseudo.pseudoApply pseudoData right)

pseudoPairingSymmetric :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  pseudoPairing pseudoData left right
  ≡ pseudoPairing pseudoData right left
pseudoPairingSymmetric pseudoData left right =
  let carrier = Pseudo.multiplierCarrier pseudoData in
  trans
    (Rect.finiteDotSymmetric carrier left
      (Pseudo.pseudoApply pseudoData right))
    (trans
      (Rect.rectangularAdjointExact
        carrier carrier
        (Pseudo.gramPseudoinverse pseudoData)
        right left)
      (Green.finiteDotRightPointwiseCong carrier
        (Positive.pseudoTransposeApplyExact pseudoData left)))

pseudoQuadraticAddExpansion :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  Positive.pseudoQuadratic pseudoData (Rect.vectorAdd left right)
  ≡ Positive.pseudoQuadratic pseudoData left
    + pseudoPairing pseudoData left right
    + pseudoPairing pseudoData left right
    + Positive.pseudoQuadratic pseudoData right
pseudoQuadraticAddExpansion pseudoData left right =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    pseudoLeft = Pseudo.pseudoApply pseudoData left
    pseudoRight = Pseudo.pseudoApply pseudoData right

    distributePseudo : ∀ row →
      Pseudo.pseudoApply pseudoData (Rect.vectorAdd left right) row
      ≡ Rect.vectorAdd pseudoLeft pseudoRight row
    distributePseudo =
      Rect.applyRectangularAddExact
        carrier (Pseudo.gramPseudoinverse pseudoData) left right

    expandLeft :
      Rect.finiteDot carrier
        (Rect.vectorAdd left right) (Rect.vectorAdd pseudoLeft pseudoRight)
      ≡ Rect.finiteDot carrier left (Rect.vectorAdd pseudoLeft pseudoRight)
        + Rect.finiteDot carrier right (Rect.vectorAdd pseudoLeft pseudoRight)
    expandLeft = finiteDotAddLeftExact carrier left right
      (Rect.vectorAdd pseudoLeft pseudoRight)

    expandBoth :
      Rect.finiteDot carrier left (Rect.vectorAdd pseudoLeft pseudoRight)
        + Rect.finiteDot carrier right (Rect.vectorAdd pseudoLeft pseudoRight)
      ≡ (Rect.finiteDot carrier left pseudoLeft
          + Rect.finiteDot carrier left pseudoRight)
        + (Rect.finiteDot carrier right pseudoLeft
          + Rect.finiteDot carrier right pseudoRight)
    expandBoth = cong₂ _+_
      (finiteDotAddRightExact carrier left pseudoLeft pseudoRight)
      (finiteDotAddRightExact carrier right pseudoLeft pseudoRight)

    crossSym = pseudoPairingSymmetric pseudoData right left
  in
  trans
    (Green.finiteDotRightPointwiseCong carrier distributePseudo)
    (trans expandLeft
      (trans expandBoth
        (subst
          (λ selected →
            (Positive.pseudoQuadratic pseudoData left
              + pseudoPairing pseudoData left right)
            + (selected + Positive.pseudoQuadratic pseudoData right)
            ≡ Positive.pseudoQuadratic pseudoData left
              + pseudoPairing pseudoData left right
              + pseudoPairing pseudoData left right
              + Positive.pseudoQuadratic pseudoData right)
          crossSym
          (ℚRing.solve-∀
            (Positive.pseudoQuadratic pseudoData left)
            (pseudoPairing pseudoData left right)
            (Positive.pseudoQuadratic pseudoData right)))))

pseudoPairingLowerDenominatorCleared :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  - (Positive.pseudoQuadratic pseudoData left
      + Positive.pseudoQuadratic pseudoData right)
  ≤ pseudoPairing pseudoData left right
      + pseudoPairing pseudoData left right
pseudoPairingLowerDenominatorCleared pseudoData left right =
  let
    qLeft = Positive.pseudoQuadratic pseudoData left
    qRight = Positive.pseudoQuadratic pseudoData right
    cross = pseudoPairing pseudoData left right

    sumNonnegative :
      0ℚ ≤ qLeft + cross + cross + qRight
    sumNonnegative = subst
      (λ selected → 0ℚ ≤ selected)
      (pseudoQuadraticAddExpansion pseudoData left right)
      (Positive.pseudoQuadraticNonnegative pseudoData
        (Rect.vectorAdd left right))

    differenceNonnegative :
      0ℚ ≤ (cross + cross) - (- (qLeft + qRight))
    differenceNonnegative = subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ qLeft qRight cross)
      sumNonnegative
  in
  Norm.nonnegativeDifferenceImpliesBelow
    (- (qLeft + qRight)) (cross + cross) differenceNonnegative

------------------------------------------------------------------------
-- Direct Round58 degree-table specialization.
------------------------------------------------------------------------

sourceDegreeEnergy :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor) →
  Degree.MobiusDegree → ℚ
sourceDegreeEnergy {pseudoData = pseudoData} atoms degree =
  Positive.pseudoQuadratic pseudoData
    (DegreeGreen.sourceDegreeVector atoms degree)

defectDegreeEnergy :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor) →
  Degree.MobiusDegree → ℚ
defectDegreeEnergy {pseudoData = pseudoData} atoms degree =
  Positive.pseudoQuadratic pseudoData
    (DegreeGreen.defectDegreeVector atoms degree)

degreeGreenLowerFromDiagonalEnergies :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    sourceDegree defectDegree →
  - (sourceDegreeEnergy atoms sourceDegree
      + defectDegreeEnergy atoms defectDegree)
  ≤ DegreeGreen.greenDegreePairing atoms sourceDegree defectDegree
      + DegreeGreen.greenDegreePairing atoms sourceDegree defectDegree
degreeGreenLowerFromDiagonalEnergies
    {pseudoData = pseudoData} atoms sourceDegree defectDegree =
  pseudoPairingLowerDenominatorCleared pseudoData
    (DegreeGreen.sourceDegreeVector atoms sourceDegree)
    (DegreeGreen.defectDegreeVector atoms defectDegree)

sourceDegreeEnergyNonnegative :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    degree →
  0ℚ ≤ sourceDegreeEnergy atoms degree
sourceDegreeEnergyNonnegative {pseudoData = pseudoData} atoms degree =
  Positive.pseudoQuadraticNonnegative pseudoData
    (DegreeGreen.sourceDegreeVector atoms degree)

defectDegreeEnergyNonnegative :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor}
    (atoms : Atoms.SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    degree →
  0ℚ ≤ defectDegreeEnergy atoms degree
defectDegreeEnergyNonnegative {pseudoData = pseudoData} atoms degree =
  Positive.pseudoQuadraticNonnegative pseudoData
    (DegreeGreen.defectDegreeVector atoms degree)

kktGreenPolarizationLowerBoundLevel : ProofLevel
kktGreenPolarizationLowerBoundLevel = machineChecked

degreeGreenSixteenToEightDiagonalReductionLevel : ProofLevel
degreeGreenSixteenToEightDiagonalReductionLevel = machineChecked

-- The remaining A2 physical leaf is now diagonal: uniformly upper-bound the
-- eight energies <S_d,K+S_d> and <D_e,K+D_e> on the selected region tightly
-- enough for the endpoint.  No sixteen independent signed cross enclosures are
-- required.
selectedRegionEightDiagonalGreenEnergyBoundsLevel : ProofLevel
selectedRegionEightDiagonalGreenEnergyBoundsLevel = conditional
