module DASHI.Physics.YangMills.BalabanClayGate4GaugeHRBetaFiveActivityAllocationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DimockConnectedActivityStabilityExact as Dimock
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaDimockLocalizationAdapterExact as Adapter

------------------------------------------------------------------------
-- Five physical activity amplitudes allocate the H-R_beta half budget.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (11) (2014), 2133--2175.
-- arXiv:1304.0705v1. DOI: 10.1007/s00023-013-0303-3.
--
-- The total connected-activity amplitude is not an unnamed g.  It is the sum
-- of determinant, interaction, chart, gauge and localization amplitudes.  Each
-- channel spends a named allowance, and distributivity proves that the total
-- coupling-times-volume estimate spends exactly the sum of those allowances.
------------------------------------------------------------------------

record GaugeFiveActivityAllocation
    {Polymer Scalar : Set}
    (connected : Dimock.ConnectedActivityStabilityData Polymer Scalar) : Set₁ where
  field
    determinantCoupling interactionCoupling chartCoupling
      gaugeCoupling localizationCoupling totalCoupling : Scalar

    determinantAllowance interactionAllowance chartAllowance
      gaugeAllowance localizationAllowance totalAllowance : Scalar

    totalCouplingMeaning :
      totalCoupling
      ≡ Dimock.add (Dimock.algebra connected) determinantCoupling
          (Dimock.add (Dimock.algebra connected) interactionCoupling
            (Dimock.add (Dimock.algebra connected) chartCoupling
              (Dimock.add (Dimock.algebra connected)
                gaugeCoupling localizationCoupling)))

    totalAllowanceMeaning :
      totalAllowance
      ≡ Dimock.add (Dimock.algebra connected) determinantAllowance
          (Dimock.add (Dimock.algebra connected) interactionAllowance
            (Dimock.add (Dimock.algebra connected) chartAllowance
              (Dimock.add (Dimock.algebra connected)
                gaugeAllowance localizationAllowance)))

    connectedCouplingMeaning :
      Dimock.coupling connected ≡ totalCoupling

    rightDistributive : ∀ left right factor →
      Dimock.multiply (Dimock.algebra connected)
        (Dimock.add (Dimock.algebra connected) left right) factor
      ≡ Dimock.add (Dimock.algebra connected)
          (Dimock.multiply (Dimock.algebra connected) left factor)
          (Dimock.multiply (Dimock.algebra connected) right factor)

    determinantAllocation :
      Dimock.LessEqual (Dimock.algebra connected)
        (Dimock.multiply (Dimock.algebra connected)
          determinantCoupling (Dimock.volume connected))
        determinantAllowance

    interactionAllocation :
      Dimock.LessEqual (Dimock.algebra connected)
        (Dimock.multiply (Dimock.algebra connected)
          interactionCoupling (Dimock.volume connected))
        interactionAllowance

    chartAllocation :
      Dimock.LessEqual (Dimock.algebra connected)
        (Dimock.multiply (Dimock.algebra connected)
          chartCoupling (Dimock.volume connected))
        chartAllowance

    gaugeAllocation :
      Dimock.LessEqual (Dimock.algebra connected)
        (Dimock.multiply (Dimock.algebra connected)
          gaugeCoupling (Dimock.volume connected))
        gaugeAllowance

    localizationAllocation :
      Dimock.LessEqual (Dimock.algebra connected)
        (Dimock.multiply (Dimock.algebra connected)
          localizationCoupling (Dimock.volume connected))
        localizationAllowance

open GaugeFiveActivityAllocation public

totalActivityCouplingVolumeBelowAllowance :
  ∀ {Polymer Scalar}
    {connected : Dimock.ConnectedActivityStabilityData Polymer Scalar} →
  (allocation : GaugeFiveActivityAllocation connected) →
  Dimock.LessEqual (Dimock.algebra connected)
    (Dimock.multiply (Dimock.algebra connected)
      (Dimock.coupling connected) (Dimock.volume connected))
    (totalAllowance allocation)
totalActivityCouplingVolumeBelowAllowance {connected = connected} allocation =
  subst
    (λ upper → Dimock.LessEqual (Dimock.algebra connected)
      (Dimock.multiply (Dimock.algebra connected)
        (Dimock.coupling connected) (Dimock.volume connected)) upper)
    (sym (totalAllowanceMeaning allocation))
    (subst
      (λ selectedCoupling →
        Dimock.LessEqual (Dimock.algebra connected)
          (Dimock.multiply (Dimock.algebra connected)
            selectedCoupling (Dimock.volume connected))
          (Dimock.add (Dimock.algebra connected)
            (determinantAllowance allocation)
            (Dimock.add (Dimock.algebra connected)
              (interactionAllowance allocation)
              (Dimock.add (Dimock.algebra connected)
                (chartAllowance allocation)
                (Dimock.add (Dimock.algebra connected)
                  (gaugeAllowance allocation)
                  (localizationAllowance allocation))))))
      (sym (connectedCouplingMeaning allocation))
      (subst
        (λ selectedCoupling →
          Dimock.LessEqual (Dimock.algebra connected)
            (Dimock.multiply (Dimock.algebra connected)
              selectedCoupling (Dimock.volume connected))
            (Dimock.add (Dimock.algebra connected)
              (determinantAllowance allocation)
              (Dimock.add (Dimock.algebra connected)
                (interactionAllowance allocation)
                (Dimock.add (Dimock.algebra connected)
                  (chartAllowance allocation)
                  (Dimock.add (Dimock.algebra connected)
                    (gaugeAllowance allocation)
                    (localizationAllowance allocation))))))
        (sym (totalCouplingMeaning allocation))
        (subst
          (λ lower → Dimock.LessEqual (Dimock.algebra connected) lower
            (Dimock.add (Dimock.algebra connected)
              (determinantAllowance allocation)
              (Dimock.add (Dimock.algebra connected)
                (interactionAllowance allocation)
                (Dimock.add (Dimock.algebra connected)
                  (chartAllowance allocation)
                  (Dimock.add (Dimock.algebra connected)
                    (gaugeAllowance allocation)
                    (localizationAllowance allocation))))))
          (sym
            (trans
              (rightDistributive allocation
                (determinantCoupling allocation)
                (Dimock.add (Dimock.algebra connected)
                  (interactionCoupling allocation)
                  (Dimock.add (Dimock.algebra connected)
                    (chartCoupling allocation)
                    (Dimock.add (Dimock.algebra connected)
                      (gaugeCoupling allocation)
                      (localizationCoupling allocation))))
                (Dimock.volume connected))
              (cong
                (Dimock.add (Dimock.algebra connected)
                  (Dimock.multiply (Dimock.algebra connected)
                    (determinantCoupling allocation)
                    (Dimock.volume connected)))
                (trans
                  (rightDistributive allocation
                    (interactionCoupling allocation)
                    (Dimock.add (Dimock.algebra connected)
                      (chartCoupling allocation)
                      (Dimock.add (Dimock.algebra connected)
                        (gaugeCoupling allocation)
                        (localizationCoupling allocation)))
                    (Dimock.volume connected))
                  (cong
                    (Dimock.add (Dimock.algebra connected)
                      (Dimock.multiply (Dimock.algebra connected)
                        (interactionCoupling allocation)
                        (Dimock.volume connected)))
                    (trans
                      (rightDistributive allocation
                        (chartCoupling allocation)
                        (Dimock.add (Dimock.algebra connected)
                          (gaugeCoupling allocation)
                          (localizationCoupling allocation))
                        (Dimock.volume connected))
                      (cong
                        (Dimock.add (Dimock.algebra connected)
                          (Dimock.multiply (Dimock.algebra connected)
                            (chartCoupling allocation)
                            (Dimock.volume connected)))
                        (rightDistributive allocation
                          (gaugeCoupling allocation)
                          (localizationCoupling allocation)
                          (Dimock.volume connected)))))))))
          (Dimock.addMonotone (Dimock.algebra connected)
            (determinantAllocation allocation)
            (Dimock.addMonotone (Dimock.algebra connected)
              (interactionAllocation allocation)
              (Dimock.addMonotone (Dimock.algebra connected)
                (chartAllocation allocation)
                (Dimock.addMonotone (Dimock.algebra connected)
                  (gaugeAllocation allocation)
                  (localizationAllocation allocation))))))))

record GaugeFiveActivityPhysicalHalfInputs
    {Cell Polymer Scalar : Set}
    (normalization : Five.PhysicalFiveChannelHRBetaNormalization Cell Scalar)
    (connected : Dimock.ConnectedActivityStabilityData Polymer Scalar) : Set₁ where
  field
    allocation : GaugeFiveActivityAllocation connected

    absoluteTotalMeaning :
      HRBase.absolute (Five.algebra (Five.channels normalization))
        (Five.totalRemainder (Five.channels normalization))
      ≡ Dimock.absolute (Dimock.algebra connected)
          (Dimock.totalActivity connected)

    orderTransport : ∀ {left right} →
      Dimock.LessEqual (Dimock.algebra connected) left right →
      HRBase.LessEqual (Five.algebra (Five.channels normalization)) left right

    allowanceIsHalfIncrement :
      totalAllowance allocation
      ≡ Five.totalHalfIncrement (Five.channels normalization)

open GaugeFiveActivityPhysicalHalfInputs public

asHRBetaDimockLocalizationInputs :
  ∀ {Cell Polymer Scalar}
    {normalization : Five.PhysicalFiveChannelHRBetaNormalization Cell Scalar}
    {connected : Dimock.ConnectedActivityStabilityData Polymer Scalar} →
  GaugeFiveActivityPhysicalHalfInputs normalization connected →
  Adapter.HRBetaDimockLocalizationInputs Cell Polymer Scalar
asHRBetaDimockLocalizationInputs
    {normalization = normalization} {connected = connected} inputs = record
  { Adapter.HRBetaDimockLocalizationInputs.normalization = normalization
  ; Adapter.HRBetaDimockLocalizationInputs.connected = connected
  ; Adapter.HRBetaDimockLocalizationInputs.absoluteTotalMeaning =
      absoluteTotalMeaning inputs
  ; Adapter.HRBetaDimockLocalizationInputs.orderTransport =
      orderTransport inputs
  ; Adapter.HRBetaDimockLocalizationInputs.couplingVolumeBelowHalfIncrement =
      subst
        (λ upper → HRBase.LessEqual
          (Five.algebra (Five.channels normalization))
          (Dimock.multiply (Dimock.algebra connected)
            (Dimock.coupling connected) (Dimock.volume connected)) upper)
        (allowanceIsHalfIncrement inputs)
        (orderTransport inputs
          (totalActivityCouplingVolumeBelowAllowance
            (allocation inputs)))
  }

gaugeFiveActivityAllocationLevel : ProofLevel
gaugeFiveActivityAllocationLevel = machineChecked

gaugeFiveActivityToPhysicalHalfAdapterLevel : ProofLevel
gaugeFiveActivityToPhysicalHalfAdapterLevel = machineChecked

physicalFiveGaugeActivityDecayInputsLevel : ProofLevel
physicalFiveGaugeActivityDecayInputsLevel = conditional

physicalFiveGaugeActivityAllowanceInputsLevel : ProofLevel
physicalFiveGaugeActivityAllowanceInputsLevel = conditional
