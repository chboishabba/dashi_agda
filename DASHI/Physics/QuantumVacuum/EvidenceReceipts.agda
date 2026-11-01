module DASHI.Physics.QuantumVacuum.EvidenceReceipts where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- Proof-carrying evidence.  These records are the preferred promotion input;
-- Boolean fields on the survey surface remain only as a computable manifest.
------------------------------------------------------------------------

record ObservableEffectReceipt (c : Surface.ExtractionClaim) : Set where
  constructor observed
  field
    closes : Surface.ExtractionClaim.observableEffect c ≡ true

record CouplingMechanismReceipt (c : Surface.ExtractionClaim) : Set where
  constructor coupled
  field
    closes : Surface.ExtractionClaim.couplingMechanism c ≡ true

record NonEquilibriumReceipt (c : Surface.ExtractionClaim) : Set where
  constructor asymmetric
  field
    closes : Surface.ExtractionClaim.nonEquilibriumAsymmetry c ≡ true

record ResetAccountingReceipt (c : Surface.ExtractionClaim) : Set where
  constructor resetAccounted
  field
    closes : Surface.ExtractionClaim.resetAccounted c ≡ true

record IndependentReplicationReceipt (c : Surface.ExtractionClaim) : Set where
  constructor replicated
  field
    closes : Surface.ExtractionClaim.replicated c ≡ true
    independentLaboratories : Nat

record TypedPromotionWitness (c : Surface.ExtractionClaim) : Set where
  constructor typedPromotion
  field
    observable : ObservableEffectReceipt c
    coupling   : CouplingMechanismReceipt c
    asymmetry  : NonEquilibriumReceipt c
    reset      : ResetAccountingReceipt c
    replication : IndependentReplicationReceipt c

forgetTypedPromotion :
  (c : Surface.ExtractionClaim) →
  TypedPromotionWitness c →
  Surface.PromotionWitness c
forgetTypedPromotion c witness =
  Surface.mkPromotionWitness
    (ObservableEffectReceipt.closes
      (TypedPromotionWitness.observable witness))
    (CouplingMechanismReceipt.closes
      (TypedPromotionWitness.coupling witness))
    (NonEquilibriumReceipt.closes
      (TypedPromotionWitness.asymmetry witness))
    (ResetAccountingReceipt.closes
      (TypedPromotionWitness.reset witness))
    (IndependentReplicationReceipt.closes
      (TypedPromotionWitness.replication witness))

typedPromotionImpliesPromotable :
  (c : Surface.ExtractionClaim) →
  TypedPromotionWitness c →
  Surface.promotable? c ≡ true
typedPromotionImpliesPromotable c witness =
  Surface.promotionWitnessImpliesPromotable c
    (forgetTypedPromotion c witness)
