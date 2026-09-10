module DASHI.Physics.ExoticGravity.LiTorrSignedSIMassCurrentCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.LiTorrComponentResolvedMassCurrentReverseSearchExact as Source
import DASHI.Physics.ExoticGravity.LiTorrSIVelocityGeometryIdentityWeldExact as Weld
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGSIMetrologyBridgeExact as SIM
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current

------------------------------------------------------------------------
-- SIGNED SI MASS-CURRENT COMPILER
--
-- Preserve component identity and sign through the J_m compilation.  The
-- compiler does not infer sign from electric charge and does not collapse
-- cancellation before the component ledger is retained.
------------------------------------------------------------------------

data SignedDirection : Set where
  negativeDirection : SignedDirection
  zeroDirection : SignedDirection
  positiveDirection : SignedDirection

record SignedComponentMassCurrent : Set where
  constructor signed-component-mass-current
  field
    component : Source.SourceComponent
    eligibility : Weld.SIJmEligibilityReceipt
    direction : SignedDirection
    massCurrentDensity : SI.Measurement SIM.MassCurrentDensity SI.unitScale
    componentRevision : String

open SignedComponentMassCurrent public

record MassCurrentCancellationLedger : Set where
  constructor mass-current-cancellation-ledger
  field
    components : List SignedComponentMassCurrent
    positiveComponentsPresent : Bool
    negativeComponentsPresent : Bool
    zeroComponentsPresent : Bool
    cancellationEvaluatedAfterComponentRetention : Bool
    electricalChargeSignUsedAsMassCurrentSign : Bool
    sameApparatusIdentityVerified : Bool
    ledgerRevision : String

open MassCurrentCancellationLedger public

record SignedSIMassCurrentField : Set where
  constructor signed-si-mass-current-field
  field
    apparatusIdentity : String
    ledger : MassCurrentCancellationLedger
    resultingMassCurrentDensity : SI.Measurement SIM.MassCurrentDensity SI.unitScale
    spatialFieldLocator : String
    derivationRevision : String
    sameApparatus : Bool

open SignedSIMassCurrentField public

compileSignedSIMassCurrentField :
  String →
  MassCurrentCancellationLedger →
  SI.Measurement SIM.MassCurrentDensity SI.unitScale →
  String → String → SignedSIMassCurrentField
compileSignedSIMassCurrentField apparatus ledger result spatial rev =
  signed-si-mass-current-field apparatus ledger result spatial rev true

------------------------------------------------------------------------
-- Compatibility adapter toward the existing abstract mass-current owner.
--
-- This adapter remains receipt-parametric because the existing owner carries
-- abstract proof objects for density/mass/charge/velocity/distribution and the
-- derivation.  The SI compiler supplies the concrete signed field but does not
-- fabricate those proof objects.
------------------------------------------------------------------------

record AbstractMassCurrentAdapterInput : Set₁ where
  constructor abstract-mass-current-adapter-input
  field
    signedField : SignedSIMassCurrentField
    bulkSource : Current.Bulk.BulkSourceIntegral
    ComponentDensityReceipt : Set
    componentDensityReceipt : ComponentDensityReceipt
    ComponentMassReceipt : Set
    componentMassReceipt : ComponentMassReceipt
    ComponentChargeReceipt : Set
    componentChargeReceipt : ComponentChargeReceipt
    ComponentVelocityReceipt : Set
    componentVelocityReceipt : ComponentVelocityReceipt
    SpatialDistributionReceipt : Set
    spatialDistributionReceipt : SpatialDistributionReceipt
    MassCurrentDerivationReceipt : Set
    massCurrentDerivationReceipt : MassCurrentDerivationReceipt
    StressEnergyEligibilityReceipt : Set
    stressEnergyEligibilityReceipt : StressEnergyEligibilityReceipt

open AbstractMassCurrentAdapterInput public

adaptSignedFieldToExistingMassCurrent :
  AbstractMassCurrentAdapterInput → Current.MassCurrentSourceReconstructionReceipt
adaptSignedFieldToExistingMassCurrent input =
  Current.mass-current-source-reconstruction-receipt
    (AbstractMassCurrentAdapterInput.bulkSource input)
    (AbstractMassCurrentAdapterInput.ComponentDensityReceipt input)
    (AbstractMassCurrentAdapterInput.componentDensityReceipt input)
    (AbstractMassCurrentAdapterInput.ComponentMassReceipt input)
    (AbstractMassCurrentAdapterInput.componentMassReceipt input)
    (AbstractMassCurrentAdapterInput.ComponentChargeReceipt input)
    (AbstractMassCurrentAdapterInput.componentChargeReceipt input)
    (AbstractMassCurrentAdapterInput.ComponentVelocityReceipt input)
    (AbstractMassCurrentAdapterInput.componentVelocityReceipt input)
    (AbstractMassCurrentAdapterInput.SpatialDistributionReceipt input)
    (AbstractMassCurrentAdapterInput.spatialDistributionReceipt input)
    (AbstractMassCurrentAdapterInput.MassCurrentDerivationReceipt input)
    (AbstractMassCurrentAdapterInput.massCurrentDerivationReceipt input)
    (AbstractMassCurrentAdapterInput.StressEnergyEligibilityReceipt input)
    (AbstractMassCurrentAdapterInput.stressEnergyEligibilityReceipt input)

record SignedSIMassCurrentCompilerBoundary : Set where
  constructor signed-si-mass-current-compiler-boundary
  field
    electricChargeSignDeterminesMassCurrentDirection : Bool
    componentsMayBeCollapsedBeforeLedgerRetention : Bool
    signedSIFieldRequiresSameApparatusIdentity : Bool
    cancellationMayBeEvaluatedAfterRetention : Bool
    signedMassCurrentAloneConstructsStressEnergy : Bool
    signedMassCurrentProvesNegativeEffectiveG : Bool

canonicalSignedSIMassCurrentCompilerBoundary :
  SignedSIMassCurrentCompilerBoundary
canonicalSignedSIMassCurrentCompilerBoundary =
  signed-si-mass-current-compiler-boundary
    false false true true false false
