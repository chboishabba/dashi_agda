module DASHI.Law.SensibLawRegulatoryOperationalisationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Law.AustralianFamilyReportWriterRegulatoryImplementationExact as Regulatory
import DASHI.Law.SensibLawOperationalLegalityExact as Operational

------------------------------------------------------------------------
-- REGULATORY IMPLEMENTATION × OPERATIONAL LEGALITY
--
-- Thin parent-composition only.  A primary Act, delegated power or in-force
-- regulations instrument is not definitionally identical to an operative
-- implementation of each delegated power.  Conversely, failure to locate an
-- implementation in a bounded search is not proof that none exists.
------------------------------------------------------------------------

parentRegulatoryImplementationBoundary : Regulatory.RegulatoryImplementationBoundary
parentRegulatoryImplementationBoundary = Regulatory.canonicalRegulatoryImplementationBoundary

parentOperationalLegalityBoundary : Operational.OperationalLegalityBoundary
parentOperationalLegalityBoundary = Operational.canonicalOperationalLegalityBoundary

record RegulatoryOperationalisationBoundary : Set where
  constructor regulatoryOperationalisationBoundary
  field
    parentRegulatoryImplementationReused : Bool
    parentOperationalLegalityReused : Bool
    enablingPowerAutomaticallyOperationalConstraint : Bool
    regulationsInstrumentAutomaticallyImplementsEveryDelegatedPower : Bool
    implementingProvisionAutomaticallyEffectiveEnforcement : Bool
    regulatorDesignationAutomaticallyEffectiveMonitoring : Bool
    recognitionSchemeAutomaticallyCaseSpecificCompliance : Bool
    unlocatedImplementationAutomaticallyProvesNonExistence : Bool
    formalAuthorityAndOperationalImplementationAreSeparate : Bool
    implementationAndEnforcementAreSeparate : Bool
    sourceSearchAndLegalAbsenceAreSeparate : Bool

open RegulatoryOperationalisationBoundary public

canonicalRegulatoryOperationalisationBoundary : RegulatoryOperationalisationBoundary
canonicalRegulatoryOperationalisationBoundary =
  regulatoryOperationalisationBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    true
    true
    true
