module DASHI.Physics.Plasma.MHDElsasserModalTransferSkewWeldBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDElsasserCouplingExchangeAntisymmetryExact as A

------------------------------------------------------------------------
-- FULL MODAL-TRANSFER SKEW WELD
--
-- The coupling tensor may be antisymmetric while the full transfer still
-- fails to cancel if amplitudes, conjugations, projection, or normalization
-- do not match under exchange.  This owner is the exact BIDI cutset.
------------------------------------------------------------------------

record ModalTransferSkewWeld (coupling : A.ElsasserCouplingExchange) : Set₁ where
  constructor modal-transfer-skew-weld
  field
    Transfer : Set
    firstTransfer secondTransfer : Transfer
    sameTriadReceipt : Set
    exchangedOutputInputSlotsReceipt : Set
    couplingAntisymmetryReceipt : Set
    amplitudeExchangeReceipt : Set
    conjugationConventionReceipt : Set
    projectionOrPressureReceipt : Set
    normalizationReceipt : Set
    fullTransferAntisymmetry : Set
    weldReference : String

open ModalTransferSkewWeld public

record ModalTransferSkewBoundary : Set where
  constructor modal-transfer-skew-boundary
  field
    couplingTensorAntisymmetryAutomaticallyLiftsToFullTransfer : Bool
    couplingTensorAntisymmetryAutomaticallyLiftsToFullTransferIsFalse :
      couplingTensorAntisymmetryAutomaticallyLiftsToFullTransfer ≡ false

    fullTransferSkewWeldCanFeedPseudoEnergyCancellation : Bool
    fullTransferSkewWeldCanFeedPseudoEnergyCancellationIsTrue :
      fullTransferSkewWeldCanFeedPseudoEnergyCancellation ≡ true

    pressureProjectionCanBeIgnoredInFullTransferWeld : Bool
    pressureProjectionCanBeIgnoredInFullTransferWeldIsFalse :
      pressureProjectionCanBeIgnoredInFullTransferWeld ≡ false

canonicalModalTransferSkewBoundary : ModalTransferSkewBoundary
canonicalModalTransferSkewBoundary =
  modal-transfer-skew-boundary false refl true refl false refl
