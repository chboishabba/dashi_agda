module DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HR

------------------------------------------------------------------------
-- Five local channels for the physical H-R_beta remainder.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239021.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. III.
-- Convergence of Polymer Expansions", Communications in Mathematical
-- Physics 116 (1988), 1--22. Bibliographic identification remains to be
-- checked against the primary series before this secondary title is promoted.
--
-- The local remainder is decomposed into determinant, interaction, chart,
-- gauge and localization channels.  Channelwise absolute estimates imply the
-- local absorption inequality by the finite triangle theorem, and the existing
-- local-to-uniform module then gives |r_k| <= Delta_k/2.  This removes one
-- monolithic local estimate from the frontier; the five physical channel bounds
-- and their polymer localization are the remaining analytic inputs.
------------------------------------------------------------------------

data HRBetaChannel : Set where
  determinant interaction chart gauge localization : HRBetaChannel

allChannels : List HRBetaChannel
allChannels =
  determinant ∷ interaction ∷ chart ∷ gauge ∷ localization ∷ []

record FiveLocalHRBetaChannels
    (Cell Scalar : Set) : Set₁ where
  field
    algebra : HR.OrderedAbsoluteAdditiveAlgebra Scalar
    cells : List Cell

    determinantRemainder interactionRemainder chartRemainder
      gaugeRemainder localizationRemainder : Cell → Scalar

    determinantBudget interactionBudget chartBudget
      gaugeBudget localizationBudget : Cell → Scalar

    determinantEstimate : ∀ cell →
      HR.LessEqual algebra
        (HR.absolute algebra (determinantRemainder cell))
        (determinantBudget cell)

    interactionEstimate : ∀ cell →
      HR.LessEqual algebra
        (HR.absolute algebra (interactionRemainder cell))
        (interactionBudget cell)

    chartEstimate : ∀ cell →
      HR.LessEqual algebra
        (HR.absolute algebra (chartRemainder cell))
        (chartBudget cell)

    gaugeEstimate : ∀ cell →
      HR.LessEqual algebra
        (HR.absolute algebra (gaugeRemainder cell))
        (gaugeBudget cell)

    localizationEstimate : ∀ cell →
      HR.LessEqual algebra
        (HR.absolute algebra (localizationRemainder cell))
        (localizationBudget cell)

    localHalfIncrement : Cell → Scalar
    localHalfIncrementMeaning : ∀ cell →
      localHalfIncrement cell
      ≡ HR.finiteSum algebra
          (HR.mapList (channelBudgetAt cell) allChannels)

    totalRemainder totalHalfIncrement : Scalar

    totalRemainderMeaning :
      totalRemainder
      ≡ HR.finiteSum algebra
          (HR.mapList localRemainder cells)

    totalHalfIncrementMeaning :
      totalHalfIncrement
      ≡ HR.finiteSum algebra
          (HR.mapList localHalfIncrement cells)

  channelRemainderAt : Cell → HRBetaChannel → Scalar
  channelRemainderAt cell determinant = determinantRemainder cell
  channelRemainderAt cell interaction = interactionRemainder cell
  channelRemainderAt cell chart = chartRemainder cell
  channelRemainderAt cell gauge = gaugeRemainder cell
  channelRemainderAt cell localization = localizationRemainder cell

  channelBudgetAt : Cell → HRBetaChannel → Scalar
  channelBudgetAt cell determinant = determinantBudget cell
  channelBudgetAt cell interaction = interactionBudget cell
  channelBudgetAt cell chart = chartBudget cell
  channelBudgetAt cell gauge = gaugeBudget cell
  channelBudgetAt cell localization = localizationBudget cell

  localRemainder : Cell → Scalar
  localRemainder cell =
    HR.finiteSum algebra
      (HR.mapList (channelRemainderAt cell) allChannels)

open FiveLocalHRBetaChannels public

channelEstimate :
  ∀ {Cell Scalar}
    (dataSet : FiveLocalHRBetaChannels Cell Scalar)
    cell channel →
  HR.LessEqual (algebra dataSet)
    (HR.absolute (algebra dataSet)
      (channelRemainderAt dataSet cell channel))
    (channelBudgetAt dataSet cell channel)
channelEstimate dataSet cell determinant = determinantEstimate dataSet cell
channelEstimate dataSet cell interaction = interactionEstimate dataSet cell
channelEstimate dataSet cell chart = chartEstimate dataSet cell
channelEstimate dataSet cell gauge = gaugeEstimate dataSet cell
channelEstimate dataSet cell localization = localizationEstimate dataSet cell

localFiveChannelAbsorption :
  ∀ {Cell Scalar}
    (dataSet : FiveLocalHRBetaChannels Cell Scalar)
    cell →
  HR.LessEqual (algebra dataSet)
    (HR.absolute (algebra dataSet)
      (localRemainder dataSet cell))
    (localHalfIncrement dataSet cell)
localFiveChannelAbsorption dataSet cell =
  subst
    (λ upper →
      HR.LessEqual (algebra dataSet)
        (HR.absolute (algebra dataSet)
          (localRemainder dataSet cell)) upper)
    (sym (localHalfIncrementMeaning dataSet cell))
    (HR.transitive (algebra dataSet)
      (HR.absoluteFiniteSumBelowSumAbsolute
        (algebra dataSet)
        (HR.mapList
          (channelRemainderAt dataSet cell) allChannels))
      (HR.finiteSumPointwiseMonotone
        (algebra dataSet)
        (λ channel →
          HR.absolute (algebra dataSet)
            (channelRemainderAt dataSet cell channel))
        (channelBudgetAt dataSet cell)
        allChannels
        (channelEstimate dataSet cell)))

asLocalHRBetaAbsorption :
  ∀ {Cell Scalar} →
  FiveLocalHRBetaChannels Cell Scalar →
  HR.LocalHRBetaAbsorption Cell Scalar
asLocalHRBetaAbsorption dataSet = record
  { HR.LocalHRBetaAbsorption.algebra = algebra dataSet
  ; HR.LocalHRBetaAbsorption.cells = cells dataSet
  ; HR.LocalHRBetaAbsorption.localRemainder = localRemainder dataSet
  ; HR.LocalHRBetaAbsorption.localHalfIncrement = localHalfIncrement dataSet
  ; HR.LocalHRBetaAbsorption.totalRemainder = totalRemainder dataSet
  ; HR.LocalHRBetaAbsorption.totalHalfIncrement = totalHalfIncrement dataSet
  ; HR.LocalHRBetaAbsorption.totalRemainderMeaning =
      totalRemainderMeaning dataSet
  ; HR.LocalHRBetaAbsorption.totalHalfIncrementMeaning =
      totalHalfIncrementMeaning dataSet
  ; HR.LocalHRBetaAbsorption.localAbsorption =
      localFiveChannelAbsorption dataSet
  }

fiveChannelUniformHalfRemainder :
  ∀ {Cell Scalar}
    (dataSet : FiveLocalHRBetaChannels Cell Scalar) →
  HR.LessEqual (algebra dataSet)
    (HR.absolute (algebra dataSet) (totalRemainder dataSet))
    (totalHalfIncrement dataSet)
fiveChannelUniformHalfRemainder dataSet =
  HR.uniformHalfRemainderFromLocalAbsorption
    (asLocalHRBetaAbsorption dataSet)

record PhysicalFiveChannelHRBetaNormalization
    (Cell Scalar : Set) : Set₁ where
  field
    channels : FiveLocalHRBetaChannels Cell Scalar
    Delta halfDelta : Scalar
    PhysicalHalf : Scalar → Scalar

    halfDeltaMeaning :
      halfDelta ≡ totalHalfIncrement channels
    physicalHalfMeaning : PhysicalHalf Delta ≡ halfDelta

open PhysicalFiveChannelHRBetaNormalization public

asPhysicalHRBetaNormalization :
  ∀ {Cell Scalar} →
  PhysicalFiveChannelHRBetaNormalization Cell Scalar →
  HR.PhysicalHRBetaNormalization Cell Scalar
asPhysicalHRBetaNormalization dataSet = record
  { HR.PhysicalHRBetaNormalization.local =
      asLocalHRBetaAbsorption (channels dataSet)
  ; HR.PhysicalHRBetaNormalization.Delta = Delta dataSet
  ; HR.PhysicalHRBetaNormalization.halfDelta = halfDelta dataSet
  ; HR.PhysicalHRBetaNormalization.halfDeltaMeaning =
      halfDeltaMeaning dataSet
  ; HR.PhysicalHRBetaNormalization.PhysicalHalf = PhysicalHalf dataSet
  ; HR.PhysicalHRBetaNormalization.physicalHalfMeaning =
      physicalHalfMeaning dataSet
  }

physicalFiveChannelUniformHRBeta :
  ∀ {Cell Scalar}
    (dataSet : PhysicalFiveChannelHRBetaNormalization Cell Scalar) →
  HR.LessEqual (algebra (channels dataSet))
    (HR.absolute (algebra (channels dataSet))
      (totalRemainder (channels dataSet)))
    (PhysicalHalf dataSet (Delta dataSet))
physicalFiveChannelUniformHRBeta dataSet =
  HR.physicalUniformHRBetaRemainder
    (asPhysicalHRBetaNormalization dataSet)

hrBetaFiveChannelLocalTriangleLevel : ProofLevel
hrBetaFiveChannelLocalTriangleLevel = machineChecked

hrBetaFiveChannelLocalToUniformLevel : ProofLevel
hrBetaFiveChannelLocalToUniformLevel = machineChecked

hrBetaFiveChannelPhysicalHalfAssemblyLevel : ProofLevel
hrBetaFiveChannelPhysicalHalfAssemblyLevel = machineChecked

physicalHRBetaDeterminantChannelInputsLevel : ProofLevel
physicalHRBetaDeterminantChannelInputsLevel = conditional

physicalHRBetaInteractionChartGaugeLocalizationInputsLevel : ProofLevel
physicalHRBetaInteractionChartGaugeLocalizationInputsLevel = conditional

physicalHRBetaPolymerLocalizationInputsLevel : ProofLevel
physicalHRBetaPolymerLocalizationInputsLevel = conditional
