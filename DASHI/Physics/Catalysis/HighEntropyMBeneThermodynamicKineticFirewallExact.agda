module DASHI.Physics.Catalysis.HighEntropyMBeneThermodynamicKineticFirewallExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction

------------------------------------------------------------------------
-- HE-MBENE THERMODYNAMIC / KINETIC FIREWALL
--
-- A CHE free-energy profile is a thermodynamic descriptor.  The existing
-- chemistry bridge owns proof-relevant reaction enablement.  This module keeps
-- the two coordinates distinct so a downhill computed step cannot masquerade
-- as an admitted kinetic transition.
------------------------------------------------------------------------

record CHEThermodynamicDescriptor
    {transition : Chemistry.Transition}
    (semantics : Reaction.TypedReactionSemantics transition) : Set₁ where
  constructor che-thermodynamic-descriptor
  field
    Downhill :
      Reaction.State semantics → Chemistry.Environment → Set
    limitingPotentialReference : String
    freeEnergyReference : String

open CHEThermodynamicDescriptor public

------------------------------------------------------------------------
-- Even with a downhill thermodynamic receipt, explicit kinetic disablement
-- excludes an admitted reaction step.
------------------------------------------------------------------------

downhillDoesNotOverrideKineticDisablement :
  ∀ {transition : Chemistry.Transition}
    {semantics : Reaction.TypedReactionSemantics transition}
    (thermo : CHEThermodynamicDescriptor semantics)
    {state : Reaction.State semantics}
    {environment : Chemistry.Environment} →
  Downhill thermo state environment →
  (Reaction.Enabled semantics state environment → ⊥) →
  Reaction.AdmittedReaction semantics state environment →
  ⊥
downhillDoesNotOverrideKineticDisablement thermo downhill disabled admitted =
  Reaction.disabledExcludesAdmittedReaction disabled admitted

------------------------------------------------------------------------
-- Conversely, kinetic admission does not manufacture a downhill CHE receipt.
-- They are independent proof obligations unless a domain theorem explicitly
-- connects them.
------------------------------------------------------------------------

record ThermodynamicKineticPair
    {transition : Chemistry.Transition}
    (semantics : Reaction.TypedReactionSemantics transition)
    (thermo : CHEThermodynamicDescriptor semantics)
    (state : Reaction.State semantics)
    (environment : Chemistry.Environment) : Set where
  constructor thermodynamic-kinetic-pair
  field
    downhillReceipt : Downhill thermo state environment
    admittedReceipt : Reaction.AdmittedReaction semantics state environment

record ThermodynamicKineticBoundary : Set where
  constructor thermodynamic-kinetic-boundary
  field
    downhillCHEImpliesKineticEnablement : Bool
    downhillCHEImpliesKineticEnablementIsFalse :
      downhillCHEImpliesKineticEnablement ≡ false

    kineticEnablementImpliesDownhillCHE : Bool
    kineticEnablementImpliesDownhillCHEIsFalse :
      kineticEnablementImpliesDownhillCHE ≡ false

    zeroCHELimitingPotentialEqualsMeasuredReactionRate : Bool
    zeroCHELimitingPotentialEqualsMeasuredReactionRateIsFalse :
      zeroCHELimitingPotentialEqualsMeasuredReactionRate ≡ false

    thermodynamicAndKineticReceiptsMayBePaired : Bool
    thermodynamicAndKineticReceiptsMayBePairedIsTrue :
      thermodynamicAndKineticReceiptsMayBePaired ≡ true

canonicalThermodynamicKineticBoundary : ThermodynamicKineticBoundary
canonicalThermodynamicKineticBoundary =
  thermodynamic-kinetic-boundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- Source-bounded interpretation for the 2026 HE-MBene computation.
------------------------------------------------------------------------

record MBeneCHEInterpretationBoundary : Set where
  constructor mbene-che-interpretation-boundary
  field
    reportedULZeroVsRHEIsThermodynamicCHEClaim : Bool
    reportedULZeroVsRHEIsThermodynamicCHEClaimIsTrue :
      reportedULZeroVsRHEIsThermodynamicCHEClaim ≡ true

    reportedULZeroVsRHEIsExperimentalKineticValidation : Bool
    reportedULZeroVsRHEIsExperimentalKineticValidationIsFalse :
      reportedULZeroVsRHEIsExperimentalKineticValidation ≡ false

canonicalMBeneCHEInterpretationBoundary : MBeneCHEInterpretationBoundary
canonicalMBeneCHEInterpretationBoundary =
  mbene-che-interpretation-boundary true refl false refl
