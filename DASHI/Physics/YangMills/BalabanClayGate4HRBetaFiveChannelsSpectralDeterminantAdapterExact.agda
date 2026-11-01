module DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveChannelsSpectralDeterminantAdapterExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaDeterminantSpectralChannelExact as Determinant

------------------------------------------------------------------------
-- Five H-R_beta channels with determinant estimate derived spectrally.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- The five-channel carrier previously accepted the determinant estimate as an
-- independent field.  This adapter derives it from localized relative-spectrum
-- mode estimates.  The remaining H-R_beta frontier is interaction, chart,
-- gauge, localization, and the physical identification of each cell spectrum.
------------------------------------------------------------------------

record FiveChannelsWithSpectralDeterminantInputs
    (Cell Mode Scalar : Set) : Set₁ where
  field
    determinant : Determinant.LocalDeterminantSpectralData Cell Mode Scalar
    cells : List Cell

    interactionRemainder chartRemainder gaugeRemainder
      localizationRemainder : Cell → Scalar

    interactionBudget chartBudget gaugeBudget
      localizationBudget : Cell → Scalar

    interactionEstimate : ∀ cell →
      HRBase.LessEqual (Determinant.algebra determinant)
        (HRBase.absolute (Determinant.algebra determinant)
          (interactionRemainder cell))
        (interactionBudget cell)

    chartEstimate : ∀ cell →
      HRBase.LessEqual (Determinant.algebra determinant)
        (HRBase.absolute (Determinant.algebra determinant)
          (chartRemainder cell))
        (chartBudget cell)

    gaugeEstimate : ∀ cell →
      HRBase.LessEqual (Determinant.algebra determinant)
        (HRBase.absolute (Determinant.algebra determinant)
          (gaugeRemainder cell))
        (gaugeBudget cell)

    localizationEstimate : ∀ cell →
      HRBase.LessEqual (Determinant.algebra determinant)
        (HRBase.absolute (Determinant.algebra determinant)
          (localizationRemainder cell))
        (localizationBudget cell)

    localHalfIncrement : Cell → Scalar
    localHalfIncrementMeaning : ∀ cell →
      localHalfIncrement cell
      ≡ HRBase.finiteSum (Determinant.algebra determinant)
          ( Determinant.determinantBudget determinant cell
          ∷ interactionBudget cell
          ∷ chartBudget cell
          ∷ gaugeBudget cell
          ∷ localizationBudget cell
          ∷ [] )

    totalRemainder totalHalfIncrement : Scalar

    totalRemainderMeaning :
      totalRemainder
      ≡ HRBase.finiteSum (Determinant.algebra determinant)
          (HRBase.mapList
            (λ cell →
              HRBase.finiteSum (Determinant.algebra determinant)
                ( Determinant.determinantRemainder determinant cell
                ∷ interactionRemainder cell
                ∷ chartRemainder cell
                ∷ gaugeRemainder cell
                ∷ localizationRemainder cell
                ∷ [] ))
            cells)

    totalHalfIncrementMeaning :
      totalHalfIncrement
      ≡ HRBase.finiteSum (Determinant.algebra determinant)
          (HRBase.mapList localHalfIncrement cells)

open FiveChannelsWithSpectralDeterminantInputs public

asFiveLocalHRBetaChannels :
  ∀ {Cell Mode Scalar} →
  FiveChannelsWithSpectralDeterminantInputs Cell Mode Scalar →
  Five.FiveLocalHRBetaChannels Cell Scalar
asFiveLocalHRBetaChannels inputs = record
  { algebra =
      Determinant.algebra (determinant inputs)
  ; cells = cells inputs
  ; determinantRemainder =
      Determinant.determinantRemainder (determinant inputs)
  ; interactionRemainder =
      interactionRemainder inputs
  ; chartRemainder = chartRemainder inputs
  ; gaugeRemainder = gaugeRemainder inputs
  ; localizationRemainder =
      localizationRemainder inputs
  ; determinantBudget =
      Determinant.determinantBudget (determinant inputs)
  ; interactionBudget = interactionBudget inputs
  ; chartBudget = chartBudget inputs
  ; gaugeBudget = gaugeBudget inputs
  ; localizationBudget = localizationBudget inputs
  ; determinantEstimate =
      Determinant.localDeterminantRemainderEstimate (determinant inputs)
  ; interactionEstimate =
      interactionEstimate inputs
  ; chartEstimate = chartEstimate inputs
  ; gaugeEstimate = gaugeEstimate inputs
  ; localizationEstimate =
      localizationEstimate inputs
  ; localHalfIncrement =
      localHalfIncrement inputs
  ; localHalfIncrementMeaning =
      localHalfIncrementMeaning inputs
  ; totalRemainder = totalRemainder inputs
  ; totalHalfIncrement =
      totalHalfIncrement inputs
  ; totalRemainderMeaning =
      totalRemainderMeaning inputs
  ; totalHalfIncrementMeaning =
      totalHalfIncrementMeaning inputs
  }

uniformHalfRemainderWithSpectralDeterminant :
  ∀ {Cell Mode Scalar}
    (inputs : FiveChannelsWithSpectralDeterminantInputs Cell Mode Scalar) →
  HRBase.LessEqual (Determinant.algebra (determinant inputs))
    (HRBase.absolute (Determinant.algebra (determinant inputs))
      (totalRemainder inputs))
    (totalHalfIncrement inputs)
uniformHalfRemainderWithSpectralDeterminant inputs =
  Five.fiveChannelUniformHalfRemainder
    (asFiveLocalHRBetaChannels inputs)

hrBetaSpectralDeterminantAdapterLevel : ProofLevel
hrBetaSpectralDeterminantAdapterLevel = machineChecked

hrBetaSpectralDeterminantUniformAssemblyLevel : ProofLevel
hrBetaSpectralDeterminantUniformAssemblyLevel = machineChecked

physicalHRBetaLocalizedRelativeSpectrumInputsLevel : ProofLevel
physicalHRBetaLocalizedRelativeSpectrumInputsLevel = conditional

physicalHRBetaFourRemainingChannelInputsLevel : ProofLevel
physicalHRBetaFourRemainingChannelInputsLevel = conditional
