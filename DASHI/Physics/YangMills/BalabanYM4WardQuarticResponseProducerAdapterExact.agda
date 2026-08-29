{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact where

------------------------------------------------------------------------
-- ROW A SOURCE-FACING ADAPTER FOR THE SHORTEST RESPONSE-KERNEL ROUTE
--
-- Collect exactly the forward producer pieces now needed by the backwards
-- shooting consumer:
--
--   C       from the normalized interaction Cauchy package,
--   L_local from its mixed coupling derivative,
--   R       from the irrelevant/polymer response kernel,
--   D       from the quartic direct-history injection,
--   b       fixed to the Ward floor 1/8388608.
--
-- The canonical Ward theorem chooses gamma from C,L,R,D.  Once the literal
-- generated trajectory identifies its cap with that gamma, all scalar shooting
-- conditions are automatic.  Remaining work is source/same-object physics, not
-- a second numerical gate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact as Gate
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseCanonicalChoiceExact as WardChoice
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

localCauchySource :
  Mixed.MixedInteractionCauchyData → Cauchy.RowACauchySourceConstants
localCauchySource mixed = record
  { Cauchy.RowACauchySourceConstants.gaussianFloor = Ward.wardGaussianFloor
  ; Cauchy.RowACauchySourceConstants.gaussianFloorPositive =
      Ward.wardGaussianFloorPositive
  ; Cauchy.RowACauchySourceConstants.mixedInteraction = mixed
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstant = 0ℚ
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstantNonnegative =
      ℚP.≤-refl
  }

rawWardConstants :
  ∀ {cutoff}
    (mixed : Mixed.MixedInteractionCauchyData)
    (kernel : Kernel.GeometricBetaResponseKernel)
    (quartic : Quartic.QuarticSourceSensitivityData kernel cutoff) →
  WardChoice.WardQuarticResponseConstants
rawWardConstants mixed kernel quartic = record
  { WardChoice.WardQuarticResponseConstants.interactionConstant =
      Cauchy.sourceInteractionConstant (localCauchySource mixed)
  ; WardChoice.WardQuarticResponseConstants.localDerivative =
      Cauchy.sourceLocalDerivativeConstant (localCauchySource mixed)
  ; WardChoice.WardQuarticResponseConstants.responseCoefficient =
      Kernel.responseCoefficient kernel
  ; WardChoice.WardQuarticResponseConstants.sourceCoefficient =
      Quartic.sourceCoefficient quartic
  ; WardChoice.WardQuarticResponseConstants.interactionConstantNonnegative =
      Cauchy.sourceInteractionConstantNonnegative (localCauchySource mixed)
  ; WardChoice.WardQuarticResponseConstants.localDerivativeNonnegative =
      Cauchy.sourceLocalDerivativeConstantNonnegative (localCauchySource mixed)
  ; WardChoice.WardQuarticResponseConstants.responseCoefficientNonnegative =
      Kernel.responseCoefficientNonnegative kernel
  ; WardChoice.WardQuarticResponseConstants.sourceCoefficientNonnegative =
      Quartic.sourceCoefficientNonnegative quartic
  }

record WardQuarticResponseProducer (cutoff : Nat) : Set₁ where
  field
    mixedInteraction : Mixed.MixedInteractionCauchyData
    responseKernel : Kernel.GeometricBetaResponseKernel
    quartic : Quartic.QuarticSourceSensitivityData responseKernel cutoff

    couplingCapIsCanonical :
      Quartic.couplingCap quartic ≡
        WardChoice.wardQuarticResponseGamma
          (rawWardConstants mixedInteraction responseKernel quartic)

    tubeBelowCap :
      Direct.tubeWidth (Quartic.direct quartic)
      ≤ Quartic.couplingCap quartic

    marginExact :
      Direct.marginConstant (Quartic.direct quartic)
      ≡ Ward.wardGaussianFloor
          - Cauchy.sourceInteractionConstant (localCauchySource mixedInteraction)
              * Quartic.couplingCap quartic

    derivativeExact :
      Direct.derivativeBound (Quartic.direct quartic)
      ≡ Cauchy.sourceLocalDerivativeConstant (localCauchySource mixedInteraction)

open WardQuarticResponseProducer public

producerWardConstants :
  ∀ {cutoff} →
  WardQuarticResponseProducer cutoff → WardChoice.WardQuarticResponseConstants
producerWardConstants dataSet =
  rawWardConstants
    (mixedInteraction dataSet)
    (responseKernel dataSet)
    (quartic dataSet)

producerCanonicalGamma :
  ∀ {cutoff} → WardQuarticResponseProducer cutoff → ℚ
producerCanonicalGamma dataSet =
  WardChoice.wardQuarticResponseGamma (producerWardConstants dataSet)

producerCapAtMostOne :
  ∀ {cutoff} (dataSet : WardQuarticResponseProducer cutoff) →
  Quartic.couplingCap (quartic dataSet) ≤ 1ℚ
producerCapAtMostOne dataSet =
  subst
    (λ left → left ≤ 1ℚ)
    (sym (couplingCapIsCanonical dataSet))
    (WardChoice.wardQuarticResponseGammaAtMostOne
      (producerWardConstants dataSet))

producerLinearizedSmallness :
  ∀ {cutoff} (dataSet : WardQuarticResponseProducer cutoff) →
  (Cauchy.sourceInteractionConstant
      (localCauchySource (mixedInteraction dataSet))
    + Cauchy.sourceLocalDerivativeConstant
      (localCauchySource (mixedInteraction dataSet))
    + Gate.fourℚ * Kernel.responseCoefficient (responseKernel dataSet)
        * Quartic.sourceCoefficient (quartic dataSet))
    * Quartic.couplingCap (quartic dataSet)
  < Ward.wardGaussianFloor
producerLinearizedSmallness dataSet =
  subst
    (λ gamma →
      (Cauchy.sourceInteractionConstant
          (localCauchySource (mixedInteraction dataSet))
        + Cauchy.sourceLocalDerivativeConstant
          (localCauchySource (mixedInteraction dataSet))
        + Gate.fourℚ * Kernel.responseCoefficient (responseKernel dataSet)
            * Quartic.sourceCoefficient (quartic dataSet))
        * gamma
      < Ward.wardGaussianFloor)
    (sym (couplingCapIsCanonical dataSet))
    (WardChoice.wardQuarticResponsePaysLinearGate
      (producerWardConstants dataSet))

asQuarticResponseCanonicalGate :
  ∀ {cutoff} (dataSet : WardQuarticResponseProducer cutoff) →
  Gate.QuarticResponseCanonicalGate (quartic dataSet)
asQuarticResponseCanonicalGate dataSet = record
  { Gate.QuarticResponseCanonicalGate.gaussianFloor = Ward.wardGaussianFloor
  ; Gate.QuarticResponseCanonicalGate.interactionConstant =
      Cauchy.sourceInteractionConstant
        (localCauchySource (mixedInteraction dataSet))
  ; Gate.QuarticResponseCanonicalGate.localDerivative =
      Cauchy.sourceLocalDerivativeConstant
        (localCauchySource (mixedInteraction dataSet))
  ; Gate.QuarticResponseCanonicalGate.interactionConstantNonnegative =
      Cauchy.sourceInteractionConstantNonnegative
        (localCauchySource (mixedInteraction dataSet))
  ; Gate.QuarticResponseCanonicalGate.localDerivativeNonnegative =
      Cauchy.sourceLocalDerivativeConstantNonnegative
        (localCauchySource (mixedInteraction dataSet))
  ; Gate.QuarticResponseCanonicalGate.couplingCapAtMostOne =
      producerCapAtMostOne dataSet
  ; Gate.QuarticResponseCanonicalGate.tubeBelowCouplingCap =
      tubeBelowCap dataSet
  ; Gate.QuarticResponseCanonicalGate.marginExact = marginExact dataSet
  ; Gate.QuarticResponseCanonicalGate.derivativeExact = derivativeExact dataSet
  ; Gate.QuarticResponseCanonicalGate.linearizedCombinedSmallness =
      producerLinearizedSmallness dataSet
  }

producerAugmentedShootingData :
  ∀ {cutoff} (dataSet : WardQuarticResponseProducer cutoff) →
  Aug.AugmentedShootingSensitivityData cutoff
producerAugmentedShootingData dataSet =
  Gate.asAugmentedShootingSensitivityData
    (asQuarticResponseCanonicalGate dataSet)

rowAWardQuarticResponseProducerToCanonicalGateLevel : ProofLevel
rowAWardQuarticResponseProducerToCanonicalGateLevel = machineChecked

rowAWardQuarticResponseProducerToShootingLevel : ProofLevel
rowAWardQuarticResponseProducerToShootingLevel = machineChecked

-- Remaining physical/source content is concentrated in constructing this
-- producer from the literal CMP109/CMP119/CMP122 generated trajectory: the
-- response kernel, quartic direct-history injection, and exact recurrence/cap
-- identifications.  The scalar contraction margin is not an additional theorem.
literalWardQuarticResponseProducerLevel : ProofLevel
literalWardQuarticResponseProducerLevel = conditional
