module DASHI.Physics.YangMills.BalabanP33UniformSchurFeedbackFromDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Volker Bach, Thomas Chen, Jurg Frohlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Compose the two exact finite results that Stage II actually needs:
--
--   entrywise decay/stencil majorant -> row and column mass,
--   row and column mass -> ||B C^-1 B^T v||^2 bound.
--
-- If B has amplitude b and weight masses BR,BC, while C^-1 has amplitude c
-- and weight masses CR,CC, the feedback coefficient is exactly
--
--   [b^2 BR BC]^2 [c^2 CR CC]
--
-- in the square-root-free squared norm.  This module does not supply the
-- scale-uniform physical amplitudes or shell masses; it proves that those are
-- now the only quantitative inputs between RG3/RG4 and the Feshbach loss.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33KernelDecayToSchurExact as Decay
import DASHI.Physics.YangMills.BalabanP33CoarseFineSchurCouplingExact as Coupling

feedbackDecayCoefficient :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
feedbackDecayCoefficient
    couplingAmplitude inverseAmplitude
    couplingRowWeight couplingColumnWeight
    inverseRowWeight inverseColumnWeight =
  ((couplingAmplitude * couplingRowWeight)
    * (couplingAmplitude * couplingColumnWeight))
  * ((inverseAmplitude * inverseRowWeight)
    * (inverseAmplitude * inverseColumnWeight))
  * ((couplingAmplitude * couplingRowWeight)
    * (couplingAmplitude * couplingColumnWeight))

feedbackDecayCoefficientExpanded :
  ∀ couplingAmplitude inverseAmplitude
    couplingRowWeight couplingColumnWeight
    inverseRowWeight inverseColumnWeight →
  feedbackDecayCoefficient
    couplingAmplitude inverseAmplitude
    couplingRowWeight couplingColumnWeight
    inverseRowWeight inverseColumnWeight
  ≡ (couplingAmplitude * couplingAmplitude
      * couplingRowWeight * couplingColumnWeight)
    * (couplingAmplitude * couplingAmplitude
      * couplingRowWeight * couplingColumnWeight)
    * (inverseAmplitude * inverseAmplitude
      * inverseRowWeight * inverseColumnWeight)
feedbackDecayCoefficientExpanded = ℚRing.solve-∀

uniformSchurFeedbackFromDecay :
  ∀ {Index : Set}
    (indices : List Index)
    (coupling couplingWeight : Schur.Matrix Index)
    (fluctuationInverse inverseWeight : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (couplingAmplitude inverseAmplitude : ℚ)
    (couplingRowWeight couplingColumnWeight : ℚ)
    (inverseRowWeight inverseColumnWeight : ℚ) →
  0ℚ ≤ couplingAmplitude →
  0ℚ ≤ inverseAmplitude →
  0ℚ ≤ couplingRowWeight →
  0ℚ ≤ couplingColumnWeight →
  0ℚ ≤ inverseRowWeight →
  0ℚ ≤ inverseColumnWeight →
  (∀ row column →
    ∣ coupling row column ∣
    ≤ couplingAmplitude * couplingWeight row column) →
  (∀ row →
    Sums.sumRational indices (couplingWeight row)
    ≤ couplingRowWeight) →
  (∀ column →
    Sums.sumRational indices (λ row → couplingWeight row column)
    ≤ couplingColumnWeight) →
  (∀ row column →
    ∣ fluctuationInverse row column ∣
    ≤ inverseAmplitude * inverseWeight row column) →
  (∀ row →
    Sums.sumRational indices (inverseWeight row)
    ≤ inverseRowWeight) →
  (∀ column →
    Sums.sumRational indices (λ row → inverseWeight row column)
    ≤ inverseColumnWeight) →
  Schur.vectorNormSq indices
    (Coupling.schurFeedbackApply
      indices coupling fluctuationInverse vector)
  ≤ feedbackDecayCoefficient
      couplingAmplitude inverseAmplitude
      couplingRowWeight couplingColumnWeight
      inverseRowWeight inverseColumnWeight
      * Schur.vectorNormSq indices vector
uniformSchurFeedbackFromDecay
    indices coupling couplingWeight
    fluctuationInverse inverseWeight vector
    couplingAmplitude inverseAmplitude
    couplingRowWeight couplingColumnWeight
    inverseRowWeight inverseColumnWeight
    couplingAmplitudeNonnegative inverseAmplitudeNonnegative
    couplingRowWeightNonnegative couplingColumnWeightNonnegative
    inverseRowWeightNonnegative inverseColumnWeightNonnegative
    couplingEntry couplingRows couplingColumns
    inverseEntry inverseRows inverseColumns =
  let
    couplingRow = couplingAmplitude * couplingRowWeight
    couplingColumn = couplingAmplitude * couplingColumnWeight
    inverseRow = inverseAmplitude * inverseRowWeight
    inverseColumn = inverseAmplitude * inverseColumnWeight

    couplingRowNonnegative : 0ℚ ≤ couplingRow
    couplingRowNonnegative =
      Schur.productNonnegative
        couplingAmplitude couplingRowWeight
        couplingAmplitudeNonnegative couplingRowWeightNonnegative

    couplingColumnNonnegative : 0ℚ ≤ couplingColumn
    couplingColumnNonnegative =
      Schur.productNonnegative
        couplingAmplitude couplingColumnWeight
        couplingAmplitudeNonnegative couplingColumnWeightNonnegative

    inverseRowNonnegative : 0ℚ ≤ inverseRow
    inverseRowNonnegative =
      Schur.productNonnegative
        inverseAmplitude inverseRowWeight
        inverseAmplitudeNonnegative inverseRowWeightNonnegative

    inverseColumnNonnegative : 0ℚ ≤ inverseColumn
    inverseColumnNonnegative =
      Schur.productNonnegative
        inverseAmplitude inverseColumnWeight
        inverseAmplitudeNonnegative inverseColumnWeightNonnegative

    raw =
      Coupling.coarseFineSchurFeedbackSquared
        indices coupling fluctuationInverse vector
        couplingRow couplingColumn inverseRow inverseColumn
        couplingRowNonnegative couplingColumnNonnegative
        inverseRowNonnegative inverseColumnNonnegative
        (Decay.kernelMajorantRowMass
          indices coupling couplingWeight
          couplingAmplitude couplingRowWeight
          couplingAmplitudeNonnegative couplingEntry couplingRows)
        (Decay.kernelMajorantColumnMass
          indices coupling couplingWeight
          couplingAmplitude couplingColumnWeight
          couplingAmplitudeNonnegative couplingEntry couplingColumns)
        (Decay.kernelMajorantRowMass
          indices fluctuationInverse inverseWeight
          inverseAmplitude inverseRowWeight
          inverseAmplitudeNonnegative inverseEntry inverseRows)
        (Decay.kernelMajorantColumnMass
          indices fluctuationInverse inverseWeight
          inverseAmplitude inverseColumnWeight
          inverseAmplitudeNonnegative inverseEntry inverseColumns)
  in
  raw

uniformSchurFeedbackFromDecayLevel : ProofLevel
uniformSchurFeedbackFromDecayLevel = machineChecked

physicalUniformCouplingDecayInputLevel : ProofLevel
physicalUniformCouplingDecayInputLevel = conditional

physicalUniformFluctuationInverseDecayInputLevel : ProofLevel
physicalUniformFluctuationInverseDecayInputLevel = conditional
