module DASHI.Physics.YangMills.BalabanClayGate4QuantitativeNewtonImplicitFunctionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative

------------------------------------------------------------------------
-- Newton-map realization of the common quantitative implicit function.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- The contraction map used for both physical applications is a Newton map
--
--   T_x(y) = y - B F(x,y),
--
-- with B a selected inverse or parametrix for the centre differential.  This
-- module proves algebraically that fixed points of T_x are exactly zeros of the
-- residual, provided the correction map reflects zero.  The common IFT carrier
-- can then be constructed without separately assuming the two implications
-- "fixed point implies residual zero" and "residual zero implies fixed point".
------------------------------------------------------------------------

record NewtonCorrectionAlgebra
    (Output Correction Residual : Set) : Set₁ where
  field
    zeroCorrection : Correction
    zeroResidual : Residual

    applyCorrection : Output → Correction → Output
    correctionOfResidual : Residual → Correction

    applyZeroCorrection : ∀ output →
      applyCorrection output zeroCorrection ≡ output

    correctionOfZeroResidual :
      correctionOfResidual zeroResidual ≡ zeroCorrection

    correctionReflectsResidualZero : ∀ residual →
      correctionOfResidual residual ≡ zeroCorrection →
      residual ≡ zeroResidual

    fixedUpdateReflectsZeroCorrection : ∀ output correction →
      applyCorrection output correction ≡ output →
      correction ≡ zeroCorrection

open NewtonCorrectionAlgebra public

record NewtonResidualData
    (Input Output Correction Residual : Set) : Set₁ where
  field
    correctionAlgebra : NewtonCorrectionAlgebra Output Correction Residual
    residual : Input → Output → Residual

open NewtonResidualData public

newtonMap :
  ∀ {Input Output Correction Residual} →
  NewtonResidualData Input Output Correction Residual →
  Input → Output → Output
newtonMap dataSet input output =
  applyCorrection (correctionAlgebra dataSet) output
    (correctionOfResidual (correctionAlgebra dataSet)
      (residual dataSet input output))

ResidualZero :
  ∀ {Input Output Correction Residual} →
  NewtonResidualData Input Output Correction Residual →
  Input → Output → Set
ResidualZero dataSet input output =
  residual dataSet input output
  ≡ zeroResidual (correctionAlgebra dataSet)

residualZeroImpliesNewtonFixed :
  ∀ {Input Output Correction Residual}
    (dataSet : NewtonResidualData Input Output Correction Residual)
    input output →
  ResidualZero dataSet input output →
  newtonMap dataSet input output ≡ output
residualZeroImpliesNewtonFixed dataSet input output residualZero =
  trans
    (cong
      (applyCorrection (correctionAlgebra dataSet) output)
      (trans
        (cong
          (correctionOfResidual (correctionAlgebra dataSet))
          residualZero)
        (correctionOfZeroResidual (correctionAlgebra dataSet))))
    (applyZeroCorrection (correctionAlgebra dataSet) output)

newtonFixedImpliesResidualZero :
  ∀ {Input Output Correction Residual}
    (dataSet : NewtonResidualData Input Output Correction Residual)
    input output →
  newtonMap dataSet input output ≡ output →
  ResidualZero dataSet input output
newtonFixedImpliesResidualZero dataSet input output fixed =
  correctionReflectsResidualZero (correctionAlgebra dataSet)
    (residual dataSet input output)
    (fixedUpdateReflectsZeroCorrection (correctionAlgebra dataSet)
      output
      (correctionOfResidual (correctionAlgebra dataSet)
        (residual dataSet input output))
      fixed)

record QuantitativeNewtonIFTInputs
    (Input Output Correction Residual Bound : Set) : Set₁ where
  field
    metric : Quantitative.QuantitativeMetricAlgebra Output Bound
    newton : NewtonResidualData Input Output Correction Residual

    AdmissibleInput : Input → Set
    contractionBall : Input → Quantitative.InvariantContractionBall metric

    ballMapMeaning : ∀ input output →
      Quantitative.map (contractionBall input) output
      ≡ newtonMap newton input output

    fixedPointExists : ∀ input → AdmissibleInput input →
      Quantitative.FixedPointWitness (contractionBall input)

open QuantitativeNewtonIFTInputs public

asQuantitativeImplicitFunctionData :
  ∀ {Input Output Correction Residual Bound} →
  QuantitativeNewtonIFTInputs Input Output Correction Residual Bound →
  Quantitative.QuantitativeImplicitFunctionData Input Output Bound
asQuantitativeImplicitFunctionData inputs = record
  { Quantitative.QuantitativeImplicitFunctionData.metric = metric inputs
  ; Quantitative.QuantitativeImplicitFunctionData.AdmissibleInput =
      AdmissibleInput inputs
  ; Quantitative.QuantitativeImplicitFunctionData.contractionBall =
      contractionBall inputs
  ; Quantitative.QuantitativeImplicitFunctionData.ResidualZero =
      ResidualZero (newton inputs)
  ; Quantitative.QuantitativeImplicitFunctionData.fixedPointImpliesResidualZero =
      λ input output inBall fixed →
        newtonFixedImpliesResidualZero (newton inputs) input output
          (trans
            (sym (ballMapMeaning inputs input output))
            fixed)
  ; Quantitative.QuantitativeImplicitFunctionData.residualZeroImpliesFixedPoint =
      λ input output inBall residualZero →
        trans
          (ballMapMeaning inputs input output)
          (residualZeroImpliesNewtonFixed
            (newton inputs) input output residualZero)
  ; Quantitative.QuantitativeImplicitFunctionData.fixedPointExists =
      fixedPointExists inputs
  }

newtonResidualFixedPointEquivalenceLevel : ProofLevel
newtonResidualFixedPointEquivalenceLevel = machineChecked

quantitativeNewtonIFTAssemblyLevel : ProofLevel
quantitativeNewtonIFTAssemblyLevel = machineChecked

physicalFederbushNewtonCorrectionInputsLevel : ProofLevel
physicalFederbushNewtonCorrectionInputsLevel = conditional

physicalFaddeevPopovNewtonCorrectionInputsLevel : ProofLevel
physicalFaddeevPopovNewtonCorrectionInputsLevel = conditional
