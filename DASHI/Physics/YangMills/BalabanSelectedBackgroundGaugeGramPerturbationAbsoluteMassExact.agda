module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact where

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
-- Turn the literal selected defect matrix D_A = L_A-L_0 and the sharp flat
-- l1 masses into a quantitative kernel bound for
--
--   E_A = K_A-K_0
--       = L_0 D_A^T + D_A L_0^T + D_A D_A^T.
--
-- The already-proved constants are
--
--   rowMass(L_0) <= 8,       columnMass(L_0) <= 2,
--   rowMass(D_A) <= 3/128,   columnMass(D_A) <= 3/512.
--
-- Hence, on every multiplier row,
--
--   rowMass(E_A)
--     <= 8(3/512) + (3/128)2 + (3/128)(3/512)
--      = 6153/65536.
--
-- This is the first direct absolute-kernel smallness theorem for the actual
-- selected-background Gram perturbation.  It is substantially stronger than
-- the earlier relative-form estimate for the purpose of an l-infinity
-- Neumann/Combes--Thomas construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as Gram
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Previous
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact as FlatMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact as DefectMass

flatMatrix = Flat.identityGaugeConstraintMatrix

defectMatrix background = Defect.gaugeDefectMatrix background

gaugeRows = Defect.gaugeRows
physicalColumns = Coordinates.physicalSU2Coordinates4

firstTermBound secondTermBound thirdTermBound perturbationRowMassBound : ℚ
firstTermBound = + 3 / 64
secondTermBound = + 3 / 64
thirdTermBound = + 9 / 65536
perturbationRowMassBound = + 6153 / 65536

explicitThreeTermPerturbation :
  Physical.RationalSU2Background4 → Defect.GaugeRow → Defect.GaugeRow → ℚ
explicitThreeTermPerturbation background left right =
  Mass.transposeProduct physicalColumns flatMatrix (defectMatrix background) left right
  + Mass.transposeProduct physicalColumns (defectMatrix background) flatMatrix left right
  + Mass.transposeProduct physicalColumns
      (defectMatrix background) (defectMatrix background) left right

gaugeGramPerturbationThreeTermExact : ∀ background left right →
  Perturbation.gaugeGramPerturbationMatrix background left right
  ≡ explicitThreeTermPerturbation background left right
gaugeGramPerturbationThreeTermExact background left right =
  let
    LA = GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background
    L0 = flatMatrix
    D = defectMatrix background

    differenceInside :
      Perturbation.gaugeGramPerturbationMatrix background left right
      ≡ Sums.sumRational physicalColumns
          (λ column →
            LA left column * LA right column
            - L0 left column * L0 right column)
    differenceInside =
      sym
        (Previous.sumSubtract physicalColumns
          (λ column → LA left column * LA right column)
          (λ column → L0 left column * L0 right column))

    pointwise : ∀ column →
      LA left column * LA right column
        - L0 left column * L0 right column
      ≡ L0 left column * D right column
        + D left column * L0 right column
        + D left column * D right column
    pointwise column =
      ℚRing.solve-∀
        (LA left column) (LA right column)
        (L0 left column) (L0 right column)

    expanded = Sums.sumRationalCong physicalColumns _ _ pointwise

    splitFirst :
      Sums.sumRational physicalColumns
        (λ column →
          L0 left column * D right column
          + D left column * L0 right column
          + D left column * D right column)
      ≡ Sums.sumRational physicalColumns
          (λ column → L0 left column * D right column)
        + Sums.sumRational physicalColumns
          (λ column →
            D left column * L0 right column
            + D left column * D right column)
    splitFirst = Mass.sumAddExact physicalColumns
      (λ column → L0 left column * D right column)
      (λ column →
        D left column * L0 right column
        + D left column * D right column)

    splitSecond :
      Sums.sumRational physicalColumns
          (λ column → L0 left column * D right column)
        + Sums.sumRational physicalColumns
          (λ column →
            D left column * L0 right column
            + D left column * D right column)
      ≡ explicitThreeTermPerturbation background left right
    splitSecond =
      cong
        (Sums.sumRational physicalColumns
          (λ column → L0 left column * D right column) +_)
        (Mass.sumAddExact physicalColumns
          (λ column → D left column * L0 right column)
          (λ column → D left column * D right column))
  in
  trans differenceInside
    (trans expanded (trans splitFirst splitSecond))

rightScaleMonotone : ∀ scale left right →
  0ℚ ≤ scale → left ≤ right → left * scale ≤ right * scale
rightScaleMonotone scale left right scaleNonnegative leftBelow =
  subst
    (λ lower → lower ≤ right * scale)
    (ℚP.*-comm scale left)
    (subst
      (λ upper → scale * left ≤ upper)
      (ℚP.*-comm scale right)
      (Norm.scaleNonnegative scale scaleNonnegative leftBelow))

firstPerturbationTermRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (Mass.transposeProduct physicalColumns flatMatrix (defectMatrix background)) row
  ≤ firstTermBound
firstPerturbationTermRowMassBound background radius row =
  let
    raw = Mass.transposeProductRowMassBound
      gaugeRows physicalColumns flatMatrix (defectMatrix background)
      DefectMass.defectColumnMassBound row
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteColumnMassBound background radius)

    scaled = rightScaleMonotone DefectMass.defectColumnMassBound
      (Mass.absoluteRectRowMass physicalColumns flatMatrix row)
      FlatMass.flatRowMassBound
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (FlatMass.selectedFlatGaugeAbsoluteRowMassBound row)

    coefficientExact :
      FlatMass.flatRowMassBound * DefectMass.defectColumnMassBound
      ≡ firstTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Mass.absoluteRectRowMass physicalColumns flatMatrix row
          * DefectMass.defectColumnMassBound ≤ upper)
      coefficientExact scaled)

secondPerturbationTermRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (Mass.transposeProduct physicalColumns (defectMatrix background) flatMatrix) row
  ≤ secondTermBound
secondPerturbationTermRowMassBound background radius row =
  let
    raw = Mass.transposeProductRowMassBound
      gaugeRows physicalColumns (defectMatrix background) flatMatrix
      FlatMass.flatColumnMassBound row
      (ℚP.nonNegative⁻¹ FlatMass.flatColumnMassBound)
      FlatMass.selectedFlatGaugeAbsoluteColumnMassBound

    scaled = rightScaleMonotone FlatMass.flatColumnMassBound
      (Mass.absoluteRectRowMass physicalColumns (defectMatrix background) row)
      DefectMass.defectRowMassBound
      (ℚP.nonNegative⁻¹ FlatMass.flatColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteRowMassBound background radius row)

    coefficientExact :
      DefectMass.defectRowMassBound * FlatMass.flatColumnMassBound
      ≡ secondTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Mass.absoluteRectRowMass physicalColumns (defectMatrix background) row
          * FlatMass.flatColumnMassBound ≤ upper)
      coefficientExact scaled)

thirdPerturbationTermRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (Mass.transposeProduct physicalColumns
      (defectMatrix background) (defectMatrix background)) row
  ≤ thirdTermBound
thirdPerturbationTermRowMassBound background radius row =
  let
    raw = Mass.transposeProductRowMassBound
      gaugeRows physicalColumns
      (defectMatrix background) (defectMatrix background)
      DefectMass.defectColumnMassBound row
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteColumnMassBound background radius)

    scaled = rightScaleMonotone DefectMass.defectColumnMassBound
      (Mass.absoluteRectRowMass physicalColumns (defectMatrix background) row)
      DefectMass.defectRowMassBound
      (ℚP.nonNegative⁻¹ DefectMass.defectColumnMassBound)
      (DefectMass.selectedGaugeDefectAbsoluteRowMassBound background radius row)

    coefficientExact :
      DefectMass.defectRowMassBound * DefectMass.defectColumnMassBound
      ≡ thirdTermBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Mass.absoluteRectRowMass physicalColumns (defectMatrix background) row
          * DefectMass.defectColumnMassBound ≤ upper)
      coefficientExact scaled)

explicitThreeTermPerturbationRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows (explicitThreeTermPerturbation background) row
  ≤ perturbationRowMassBound
explicitThreeTermPerturbationRowMassBound background radius row =
  let
    triangle = Mass.squareRowMassAdd3 gaugeRows
      (Mass.transposeProduct physicalColumns flatMatrix (defectMatrix background))
      (Mass.transposeProduct physicalColumns (defectMatrix background) flatMatrix)
      (Mass.transposeProduct physicalColumns
        (defectMatrix background) (defectMatrix background)) row

    bounded = ℚP.+-mono-≤
      (firstPerturbationTermRowMassBound background radius row)
      (ℚP.+-mono-≤
        (secondPerturbationTermRowMassBound background radius row)
        (thirdPerturbationTermRowMassBound background radius row))

    coefficientExact :
      firstTermBound + (secondTermBound + thirdTermBound)
      ≡ perturbationRowMassBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        firstTermBound + (secondTermBound + thirdTermBound) ≤ upper)
      coefficientExact bounded)

selectedGaugeGramPerturbationAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (Perturbation.gaugeGramPerturbationMatrix background) row
  ≤ perturbationRowMassBound
selectedGaugeGramPerturbationAbsoluteRowMassBound background radius row =
  let
    identify :
      Mass.squareRowMass gaugeRows
        (Perturbation.gaugeGramPerturbationMatrix background) row
      ≡ Mass.squareRowMass gaugeRows
        (explicitThreeTermPerturbation background) row
    identify =
      Sums.sumRationalCong gaugeRows _ _
        (λ right → cong ∣_∣
          (gaugeGramPerturbationThreeTermExact background row right))
  in
  subst
    (λ left → left ≤ perturbationRowMassBound)
    (sym identify)
    (explicitThreeTermPerturbationRowMassBound background radius row)

selectedGaugeGramPerturbationAbsoluteMassLevel : ProofLevel
selectedGaugeGramPerturbationAbsoluteMassLevel = machineChecked
