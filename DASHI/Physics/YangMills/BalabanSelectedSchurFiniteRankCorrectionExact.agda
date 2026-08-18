module DASHI.Physics.YangMills.BalabanSelectedSchurFiniteRankCorrectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Complete the quantitative finite-rank part of the selected KKT Schur
-- elimination.  The average block is exactly 256 I, hence its inverse is
-- exactly 1/256 I.  With the physical defect-only cross matrix C_A,
--
--   F_A = (1/256) C_A C_A^T.
--
-- The preceding exact bounds are deliberately conservative:
--
--   rowMass(C_A)    <= 9/32,
--   columnMass(C_A) <= 18.
--
-- Finite Schur/Fubini algebra therefore gives
--
--   rowMass(C_A C_A^T) <= (9/32) 18 = 81/16,
--
-- and hence
--
--   rowMass(F_A) <= 81/4096.
--
-- This is already far below one.  No cancellation or optimized average-sector
-- estimate is needed for the locality contraction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as Scale
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross

rawSchurCorrection :
  Physical.RationalSU2Background4 → Cross.GaugeRow → Cross.GaugeRow → ℚ
rawSchurCorrection background =
  Mass.transposeProduct Cross.averageRows
    (Cross.selectedSchurCrossMatrix background)
    (Cross.selectedSchurCrossMatrix background)

schurScale rawCorrectionRowMassBound schurCorrectionRowMassBound : ℚ
schurScale = + 1 / 256
rawCorrectionRowMassBound = + 81 / 16
schurCorrectionRowMassBound = + 81 / 4096

selectedRawSchurCorrectionRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass Cross.gaugeRows (rawSchurCorrection background) row
  ≤ rawCorrectionRowMassBound
selectedRawSchurCorrectionRowMassBound background radius row =
  let
    C = Cross.selectedSchurCrossMatrix background

    productBound :
      Mass.squareRowMass Cross.gaugeRows (rawSchurCorrection background) row
      ≤ Mass.absoluteRectRowMass Cross.averageRows C row
          * Cross.crossColumnMassBound
    productBound =
      Mass.transposeProductRowMassBound
        Cross.gaugeRows Cross.averageRows C C
        Cross.crossColumnMassBound row
        (ℚP.nonNegative⁻¹ Cross.crossColumnMassBound)
        (Cross.selectedSchurCrossAbsoluteColumnMassBound background radius)

    crossRowScaled :
      Mass.absoluteRectRowMass Cross.averageRows C row
          * Cross.crossColumnMassBound
      ≤ Cross.crossRowMassBound * Cross.crossColumnMassBound
    crossRowScaled =
      Scale.rightScaleMonotone
        Cross.crossColumnMassBound
        (Mass.absoluteRectRowMass Cross.averageRows C row)
        Cross.crossRowMassBound
        (ℚP.nonNegative⁻¹ Cross.crossColumnMassBound)
        (Cross.selectedSchurCrossAbsoluteRowMassBound background radius row)
  in
  ℚP.≤-trans productBound
    (subst
      (λ upper →
        Cross.crossRowMassBound * Cross.crossColumnMassBound ≤ upper)
      (ℚRing.solve []) crossRowScaled)

selectedSchurFiniteRankCorrection :
  Physical.RationalSU2Background4 → Cross.GaugeRow → Cross.GaugeRow → ℚ
selectedSchurFiniteRankCorrection background left right =
  schurScale * rawSchurCorrection background left right

schurScaleAbsoluteExact : ∣ schurScale ∣ ≡ schurScale
schurScaleAbsoluteExact =
  ℚP.0≤p⇒∣p∣≡p (ℚP.nonNegative⁻¹ schurScale)

selectedSchurCorrectionRowMassScaleExact :
  ∀ background row →
  Mass.squareRowMass Cross.gaugeRows
    (selectedSchurFiniteRankCorrection background) row
  ≡ schurScale
      * Mass.squareRowMass Cross.gaugeRows (rawSchurCorrection background) row
selectedSchurCorrectionRowMassScaleExact background row =
  trans
    (Sums.sumRationalCong Cross.gaugeRows _ _
      (λ outputRow →
        trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ schurScale
            (rawSchurCorrection background row outputRow))
          (cong
            (_* ∣ rawSchurCorrection background row outputRow ∣)
            schurScaleAbsoluteExact)))
    (Sums.sumRationalScale schurScale Cross.gaugeRows
      (λ outputRow → ∣ rawSchurCorrection background row outputRow ∣))

selectedSchurFiniteRankCorrectionRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass Cross.gaugeRows
    (selectedSchurFiniteRankCorrection background) row
  ≤ schurCorrectionRowMassBound
selectedSchurFiniteRankCorrectionRowMassBound background radius row =
  let
    rawBound = selectedRawSchurCorrectionRowMassBound background radius row
    scaled = Norm.scaleNonnegative schurScale
      (ℚP.nonNegative⁻¹ schurScale) rawBound
    coefficientExact :
      schurScale * rawCorrectionRowMassBound ≡ schurCorrectionRowMassBound
    coefficientExact = ℚRing.solve []
  in
  subst
    (λ lower → lower ≤ schurCorrectionRowMassBound)
    (sym (selectedSchurCorrectionRowMassScaleExact background row))
    (subst
      (λ upper →
        schurScale
          * Mass.squareRowMass Cross.gaugeRows
              (rawSchurCorrection background) row
        ≤ upper)
      coefficientExact scaled)

selectedSchurFiniteRankCorrectionLevel : ProofLevel
selectedSchurFiniteRankCorrectionLevel = machineChecked

selectedSchurFiniteRankCorrectionMassLevel : ProofLevel
selectedSchurFiniteRankCorrectionMassLevel = machineChecked
