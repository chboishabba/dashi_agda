module DASHI.Economics.AIPolicyBackstopCommercialMoat2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.PolicyBackstopCommercialDisciplineExact as Policy
import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Regulatory

------------------------------------------------------------------------
-- COMMERCIAL-MOAT / STRATEGIC-BACKSTOP SEPARATION
--
-- The testable political-economy hypothesis is that declining model scarcity
-- rents can coexist with increasing sunk-capital / critical-infrastructure
-- salience.  That conjunction may increase demand for policy support, but it
-- is not by itself evidence of regulatory capture, antitrust liability or a
-- legally operative "too big to fail" designation.
------------------------------------------------------------------------

data MoatChannel : Set where
  modelScarcity distribution enterpriseCompliance proprietaryData
    integration capitalScale switchingCost stateProcurement
    nationalSecurityDesignation regulatoryBarrier : MoatChannel

record MoatReading : Set where
  constructor moatReading
  field
    channel : MoatChannel
    strength : Trit
    commercial : Bool
    policyMediated : Bool

open MoatReading public

record CommercialStrategicSeparation : Set where
  constructor commercialStrategicSeparation
  field
    privateScarcityRent : Trit
    ordinarySoftwareMoat : Trit
    sunkInfrastructureExposure : Trit
    criticalInfrastructureSalience : Trit
    stateProcurementSalience : Trit
    regulatoryProtectionSalience : Trit
    privateCommercialViabilityEstablished : Bool

open CommercialStrategicSeparation public

candidateOctober2026CommercialStrategicState : CommercialStrategicSeparation
candidateOctober2026CommercialStrategicState =
  commercialStrategicSeparation neg pos pos pos pos pos false

record BackstopTransitionHypothesis : Set where
  constructor backstopTransitionHypothesis
  field
    capabilityCommoditisation : Bool
    proprietaryRentCompression : Bool
    capitalLockIn : Bool
    strategicStateInterest : Bool
    backstopDemandCouldRise : Bool
    causalCaptureEstablished : Bool

candidateBackstopTransition : BackstopTransitionHypothesis
candidateBackstopTransition =
  backstopTransitionHypothesis true true true true true false

data NationalSecurityFramingImpliesCommercialMoatPermission : Set where
data PolicySupportImpliesRegulatoryCapturePermission : Set where
data StateProcurementImpliesPrivateViabilityPermission : Set where

nationalSecurityFramingDoesNotAutoProveCommercialMoat :
  NationalSecurityFramingImpliesCommercialMoatPermission → ⊥
nationalSecurityFramingDoesNotAutoProveCommercialMoat ()

policySupportDoesNotAutoProveRegulatoryCapture :
  PolicySupportImpliesRegulatoryCapturePermission → ⊥
policySupportDoesNotAutoProveRegulatoryCapture ()

stateProcurementDoesNotAutoProvePrivateViability :
  StateProcurementImpliesPrivateViabilityPermission → ⊥
stateProcurementDoesNotAutoProvePrivateViability ()

------------------------------------------------------------------------
-- Existing repo machinery retained rather than duplicated.
------------------------------------------------------------------------

policySupportStillDoesNotCloseCommercialViability :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
policySupportStillDoesNotCloseCommercialViability =
  Policy.policySupportDoesNotAutoPromoteToCommercialViability

structuralRegulatoryMoatWithoutIntent : Regulatory.RegulatoryMoatReceipt
structuralRegulatoryMoatWithoutIntent =
  Regulatory.canonicalStructuralMoatWithoutIntent

concentratedInterestBoundary : Regulatory.ConcentratedInterestGame
concentratedInterestBoundary = Regulatory.canonicalConcentratedInterestGame

regulatoryMoatStillDoesNotProveConspiracy :
  Regulatory.RegulatoryMoatImpliesConspiracyPermission → ⊥
regulatoryMoatStillDoesNotProveConspiracy =
  Regulatory.moatDoesNotAutoProveConspiracy

capitalMoatHypothesis : Capital.StrategicBackstopTransitionHypothesis
capitalMoatHypothesis = Capital.candidateCommercialToStrategicMoatHypothesis
