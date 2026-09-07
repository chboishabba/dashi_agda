module DASHI.Economics.PolicyBackstopCommercialDisciplineExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- POLICY BACKSTOP / COMMERCIAL DISCIPLINE
------------------------------------------------------------------------

record PolicySupportedProject : Set₁ where
  field
    CommercialReturn StrategicValue SecurityValue IndustrialPolicyValue : Set
    commercialReturnObserved : CommercialReturn
    strategicValueObserved   : StrategicValue
    securityValueObserved    : SecurityValue
    industrialPolicyObserved : IndustrialPolicyValue

open PolicySupportedProject public

record PolicyBackstopReceipt : Set₁ where
  field
    Project : Set
    Backstop : Set
    project : Project
    backstop : Backstop

open PolicyBackstopReceipt public

data CommercialUnviabilityImpliesCancellationPermission : Set where

data PolicySupportImpliesCommercialViabilityPermission : Set where

data StrategicValueImpliesPositiveNPVPermission : Set where

commercialUnviabilityDoesNotAutoPromoteToCancellation :
  CommercialUnviabilityImpliesCancellationPermission → ⊥
commercialUnviabilityDoesNotAutoPromoteToCancellation ()

policySupportDoesNotAutoPromoteToCommercialViability :
  PolicySupportImpliesCommercialViabilityPermission → ⊥
policySupportDoesNotAutoPromoteToCommercialViability ()

strategicValueDoesNotAutoPromoteToPositiveNPV :
  StrategicValueImpliesPositiveNPVPermission → ⊥
strategicValueDoesNotAutoPromoteToPositiveNPV ()
