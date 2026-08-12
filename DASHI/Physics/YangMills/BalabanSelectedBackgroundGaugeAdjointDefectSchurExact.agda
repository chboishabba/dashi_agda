module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectSchurExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Issai Schur, classical matrix norm test (1911). No DOI applies to the
-- original result.
--
-- DASHI CONTRIBUTION
--
-- The earlier selected gauge-adjoint defect theorem used a Frobenius estimate
-- and therefore paid the total state dimension 3072.  The local stencil proof
-- subsequently established the much sharper absolute masses
--
--       rowMass(D_A)    <= 3/128,
--       columnMass(D_A) <= 3/512.
--
-- Apply the repository's square-root-free rectangular Schur theorem to the
-- literal transpose D_A^T.  The row and column masses swap, giving
--
--       ||D_A^T lambda||^2
--          <= (3/512)(3/128) ||lambda||^2
--          = 9/65536 ||lambda||^2.
--
-- This removes the volume-count artefact from the adjoint perturbation bound.
-- The same proof architecture is therefore the correct route for L=13: only
-- the local entry/stencil identification must be migrated; the coefficient
-- itself is independent of the number of lattice sites.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

transposeGaugeDefectMatrix :
  Physical.RationalSU2Background4 →
  KKT.State → Defect.GaugeRow → ℚ
transposeGaugeDefectMatrix background column row =
  Defect.gaugeDefectMatrix background row column

transposeRowMassBound transposeColumnMassBound : ℚ
transposeRowMassBound = Mass.defectColumnMassBound
transposeColumnMassBound = Mass.defectRowMassBound

selectedSchurAdjointDefectCoefficient : ℚ
selectedSchurAdjointDefectCoefficient = + 9 / 65536

selectedSchurAdjointDefectCoefficientExact :
  transposeRowMassBound * transposeColumnMassBound
  ≡ selectedSchurAdjointDefectCoefficient
selectedSchurAdjointDefectCoefficientExact = ℚRing.solve []

transposeRowsBounded :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  RectSchur.rectAbsoluteRowMass Defect.gaugeRows
    (transposeGaugeDefectMatrix background) column
  ≤ transposeRowMassBound
transposeRowsBounded background radius column =
  Mass.selectedGaugeDefectAbsoluteColumnMassBound
    background radius column

transposeColumnsBounded :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  RectSchur.rectAbsoluteColumnMass Coordinates.physicalSU2Coordinates4
    (transposeGaugeDefectMatrix background) row
  ≤ transposeColumnMassBound
transposeColumnsBounded background radius row =
  Mass.selectedGaugeDefectAbsoluteRowMassBound
    background radius row

selectedGaugeAdjointDefectSchurBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  Defect.gaugeAdjointDefectNormSq background multiplier
  ≤ selectedSchurAdjointDefectCoefficient
      * Defect.gaugeMultiplierRowNormSq multiplier
selectedGaugeAdjointDefectSchurBound background radius multiplier =
  let
    raw = RectSchur.finiteRectangularSchurSquared
      Coordinates.physicalSU2Coordinates4
      Defect.gaugeRows
      (transposeGaugeDefectMatrix background)
      multiplier
      transposeRowMassBound
      transposeColumnMassBound
      (ℚP.nonNegative⁻¹ transposeRowMassBound)
      (ℚP.nonNegative⁻¹ transposeColumnMassBound)
      (transposeRowsBounded background radius)
      (transposeColumnsBounded background radius)
  in
  subst
    (λ coefficient →
      Defect.gaugeAdjointDefectNormSq background multiplier
      ≤ coefficient * Defect.gaugeMultiplierRowNormSq multiplier)
    selectedSchurAdjointDefectCoefficientExact
    raw

selectedGaugeAdjointDefectSchurLevel : ProofLevel
selectedGaugeAdjointDefectSchurLevel = machineChecked
