module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Complete the l1/l-infinity estimate for the literal selected Gram
-- perturbation E_A.  The row bound 6153/65536 was proved previously.  The
-- transpose-product column lemma gives the same bound columnwise:
--
--   columnMass(L_0 D_A^T) <= (3/128)*2       = 3/64,
--   columnMass(D_A L_0^T) <= 8*(3/512)       = 3/64,
--   columnMass(D_A D_A^T) <= (3/128)(3/512) = 9/65536.
--
-- Hence both induced l1 and l-infinity absolute matrix norms of E_A are
-- bounded by 6153/65536 on the actual selected carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as RowMass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact as FlatMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact as DefectMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass

firstColumnTermBound secondColumnTermBound thirdColumnTermBound : ℚ
firstColumnTermBound = + 3 / 64
secondColumnTermBound = + 3 / 64
thirdColumnTermBound = + 9 / 65536

gaugeRows = DefectMass.gaugeRows
physicalColumns = DefectMass.physicalColumns
flatMatrix = FlatMass.Flat.identityGaugeConstraintMatrix

defectMatrix background = DefectMass.Defect.gaugeDefectMatrix background

firstPerturbationTermColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (RowMass.transposeProduct physicalColumns flatMatrix (defectMatrix background))
    column
  ≤ firstColumnTermBound
firstPerturbationTermColumnMassBound background radius column =
  let
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows physicalColumns flatMatrix (defectMatrix background)
      FlatMass.flatColumnMassBound column
      (ℚP.nonNegative⁻¹ FlatMass.flatColumnMassBound)
      FlatMass.selectedFlatGaugeAbsoluteColumnMassBound

    scaled = PerturbationMass.rightScaleMonotone FlatMass.flatColumnMassBound
      (RowMass.absoluteRectRowMass physicalColumns (defectMatrix background) column)
      DefectMass.defectRowMassBound
      (ℚP.nonNegative⁻¹ FlatMass.flatColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteRowMassBound background radius column)

    coefficientExact :
      DefectMass.defectRowMassBound * FlatMass.flatColumnMassBound
      ≡ firstColumnTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        RowMass.absoluteRectRowMass physicalColumns (defectMatrix background) column
          * FlatMass.flatColumnMassBound ≤ upper)
      coefficientExact scaled)

secondPerturbationTermColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (RowMass.transposeProduct physicalColumns (defectMatrix background) flatMatrix)
    column
  ≤ secondColumnTermBound
secondPerturbationTermColumnMassBound background radius column =
  let
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows physicalColumns (defectMatrix background) flatMatrix
      DefectMass.defectColumnMassBound column
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteColumnMassBound background radius)

    scaled = PerturbationMass.rightScaleMonotone DefectMass.defectColumnMassBound
      (RowMass.absoluteRectRowMass physicalColumns flatMatrix column)
      FlatMass.flatRowMassBound
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (FlatMass.selectedFlatGaugeAbsoluteRowMassBound column)

    coefficientExact :
      FlatMass.flatRowMassBound * DefectMass.defectColumnMassBound
      ≡ secondColumnTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        RowMass.absoluteRectRowMass physicalColumns flatMatrix column
          * DefectMass.defectColumnMassBound ≤ upper)
      coefficientExact scaled)

thirdPerturbationTermColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (RowMass.transposeProduct physicalColumns
      (defectMatrix background) (defectMatrix background))
    column
  ≤ thirdColumnTermBound
thirdPerturbationTermColumnMassBound background radius column =
  let
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows physicalColumns
      (defectMatrix background) (defectMatrix background)
      DefectMass.defectColumnMassBound column
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteColumnMassBound background radius)

    scaled = PerturbationMass.rightScaleMonotone DefectMass.defectColumnMassBound
      (RowMass.absoluteRectRowMass physicalColumns (defectMatrix background) column)
      DefectMass.defectRowMassBound
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteRowMassBound background radius column)

    coefficientExact :
      DefectMass.defectRowMassBound * DefectMass.defectColumnMassBound
      ≡ thirdColumnTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        RowMass.absoluteRectRowMass physicalColumns (defectMatrix background) column
          * DefectMass.defectColumnMassBound ≤ upper)
      coefficientExact scaled)

explicitThreeTermPerturbationColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (PerturbationMass.explicitThreeTermPerturbation background) column
  ≤ PerturbationMass.perturbationRowMassBound
explicitThreeTermPerturbationColumnMassBound background radius column =
  let
    triangle = ColumnMass.squareColumnMassAdd3 gaugeRows
      (RowMass.transposeProduct physicalColumns flatMatrix (defectMatrix background))
      (RowMass.transposeProduct physicalColumns (defectMatrix background) flatMatrix)
      (RowMass.transposeProduct physicalColumns
        (defectMatrix background) (defectMatrix background)) column

    bounded = ℚP.+-mono-≤
      (firstPerturbationTermColumnMassBound background radius column)
      (ℚP.+-mono-≤
        (secondPerturbationTermColumnMassBound background radius column)
        (thirdPerturbationTermColumnMassBound background radius column))

    coefficientExact :
      firstColumnTermBound + (secondColumnTermBound + thirdColumnTermBound)
      ≡ PerturbationMass.perturbationRowMassBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        firstColumnTermBound + (secondColumnTermBound + thirdColumnTermBound)
        ≤ upper)
      coefficientExact bounded)

selectedGaugeGramPerturbationAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (Perturbation.gaugeGramPerturbationMatrix background) column
  ≤ PerturbationMass.perturbationRowMassBound
selectedGaugeGramPerturbationAbsoluteColumnMassBound background radius column =
  let
    identify :
      ColumnMass.squareColumnMass gaugeRows
        (Perturbation.gaugeGramPerturbationMatrix background) column
      ≡ ColumnMass.squareColumnMass gaugeRows
        (PerturbationMass.explicitThreeTermPerturbation background) column
    identify =
      DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalCong
        gaugeRows _ _
        (λ row → cong ∣_∣
          (PerturbationMass.gaugeGramPerturbationThreeTermExact
            background row column))
  in
  subst
    (λ left → left ≤ PerturbationMass.perturbationRowMassBound)
    (sym identify)
    (explicitThreeTermPerturbationColumnMassBound background radius column)

selectedGaugeGramPerturbationTwoSidedMassLevel : ProofLevel
selectedGaugeGramPerturbationTwoSidedMassLevel = machineChecked
