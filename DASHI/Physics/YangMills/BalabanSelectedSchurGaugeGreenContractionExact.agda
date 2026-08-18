module DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- The exact average-sector Schur elimination replaces the selected gauge Gram
-- perturbation E_A by
--
--   Q_A = E_A - F_A,
--   F_A = (1/256) C_A C_A^T.
--
-- We already have
--
--   rowMass(E_A) <= 6153/65536,
--   rowMass(F_A) <=   81/4096 = 1296/65536.
--
-- Hence
--
--   rowMass(Q_A) <= 7449/65536.
--
-- The exact flat Fourier Green G_0 has row mass <=17/16.  Finite matrix
-- multiplication therefore gives
--
--   rowMass(G_0 Q_A)
--     <= (17/16)(7449/65536)
--      = 126633/1048576
--      < 1/8 < 1.
--
-- Thus the gauge Schur operator is already in a strict unweighted Neumann ball
-- around the explicit flat Green.  This removes the need to obtain mere
-- invertibility from a separate 780-row black-box Combes--Thomas theorem.
-- Exponential weighted locality still requires transporting this margin through
-- the selected finite weight, which is a smaller remaining step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as FlatContraction
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurFiniteRankCorrectionExact as Correction

schurPerturbation :
  Physical.RationalSU2Background4 → Cross.GaugeRow → Cross.GaugeRow → ℚ
schurPerturbation background left right =
  Perturbation.gaugeGramPerturbationMatrix background left right
  - Correction.selectedSchurFiniteRankCorrection background left right

schurPerturbationRowMassBound : ℚ
schurPerturbationRowMassBound = + 7449 / 65536

selectedSchurPerturbationRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass Cross.gaugeRows (schurPerturbation background) row
  ≤ schurPerturbationRowMassBound
selectedSchurPerturbationRowMassBound background radius row =
  let
    E = Perturbation.gaugeGramPerturbationMatrix background
    F = Correction.selectedSchurFiniteRankCorrection background

    triangle :
      Sums.sumRational Cross.gaugeRows
        (λ output → ∣ E row output - F row output ∣)
      ≤ Sums.sumRational Cross.gaugeRows
        (λ output → ∣ E row output ∣ + ∣ F row output ∣)
    triangle = Schur.sumPointwiseBelow Cross.gaugeRows _ _
      (λ output → ℚP.∣p-q∣≤∣p∣+∣q∣ (E row output) (F row output))

    split :
      Sums.sumRational Cross.gaugeRows
        (λ output → ∣ E row output ∣ + ∣ F row output ∣)
      ≡ Mass.squareRowMass Cross.gaugeRows E row
        + Mass.squareRowMass Cross.gaugeRows F row
    split = Mass.sumAddExact Cross.gaugeRows
      (λ output → ∣ E row output ∣)
      (λ output → ∣ F row output ∣)

    bounded :
      Mass.squareRowMass Cross.gaugeRows E row
        + Mass.squareRowMass Cross.gaugeRows F row
      ≤ PerturbationMass.perturbationRowMassBound
        + Correction.schurCorrectionRowMassBound
    bounded = ℚP.+-mono-≤
      (PerturbationMass.selectedGaugeGramPerturbationAbsoluteRowMassBound
        background radius row)
      (Correction.selectedSchurFiniteRankCorrectionRowMassBound
        background radius row)

    coefficientExact :
      PerturbationMass.perturbationRowMassBound
        + Correction.schurCorrectionRowMassBound
      ≡ schurPerturbationRowMassBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        Sums.sumRational Cross.gaugeRows
          (λ output → ∣ E row output ∣ + ∣ F row output ∣)
        ≤ upper)
      (trans split coefficientExact)
      (subst
        (λ lower → lower
          ≤ PerturbationMass.perturbationRowMassBound
            + Correction.schurCorrectionRowMassBound)
        (sym split) bounded))

flatGreenTimesSchurPerturbation :
  Physical.RationalSU2Background4 → Cross.GaugeRow → Cross.GaugeRow → ℚ
flatGreenTimesSchurPerturbation background =
  Matrix.matrixProduct Cross.gaugeRows
    FlatContraction.flatGreenKernelMatrix
    (schurPerturbation background)

schurGreenContractionBound : ℚ
schurGreenContractionBound = + 126633 / 1048576

schurGreenContractionProductExact :
  GreenMass.seventeenSixteenths * schurPerturbationRowMassBound
  ≡ schurGreenContractionBound
schurGreenContractionProductExact = ℚRing.solve []

selectedFlatGreenSchurPerturbationRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass Cross.gaugeRows
    (flatGreenTimesSchurPerturbation background) row
  ≤ schurGreenContractionBound
selectedFlatGreenSchurPerturbationRowMassBound background radius row =
  let
    raw = Neumann.productRowMassBound
      Cross.gaugeRows
      FlatContraction.flatGreenKernelMatrix
      (schurPerturbation background)
      GreenMass.seventeenSixteenths
      schurPerturbationRowMassBound
      (ℚP.nonNegative⁻¹ schurPerturbationRowMassBound)
      FlatContraction.selectedFlatGaugeGreenAbsoluteRowMassBound
      (selectedSchurPerturbationRowMassBound background radius)
      row
  in
  subst
    (λ upper →
      Neumann.rowMass Cross.gaugeRows
        (flatGreenTimesSchurPerturbation background) row ≤ upper)
    schurGreenContractionProductExact raw

oneEighth : ℚ
oneEighth = + 1 / 8

schurGreenContractionBelowOneEighth :
  schurGreenContractionBound ≤ oneEighth
schurGreenContractionBelowOneEighth =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (oneEighth - schurGreenContractionBound))

oneEighthBelowOne : oneEighth < 1ℚ
oneEighthBelowOne = ℚP.positive⁻¹ (+ 7 / 8)

selectedFlatGreenSchurStrictContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass Cross.gaugeRows
    (flatGreenTimesSchurPerturbation background) row
  < 1ℚ
selectedFlatGreenSchurStrictContraction background radius row =
  ℚP.≤-<-trans
    (ℚP.≤-trans
      (selectedFlatGreenSchurPerturbationRowMassBound background radius row)
      schurGreenContractionBelowOneEighth)
    oneEighthBelowOne

selectedSchurPerturbationMassLevel : ProofLevel
selectedSchurPerturbationMassLevel = machineChecked

selectedSchurFlatGreenStrictContractionLevel : ProofLevel
selectedSchurFlatGreenStrictContractionLevel = machineChecked
