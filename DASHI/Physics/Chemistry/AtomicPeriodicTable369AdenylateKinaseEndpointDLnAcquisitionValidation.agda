module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseEndpointDLnAcquisitionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseEndpointDLnAcquisitionExact as Subject

open Subject

openEndpointDLnPaid : openEndpointDLnAngstrom ≡ 38
openEndpointDLnPaid = refl

closedEndpointDLnPaid : closedEndpointDLnAngstrom ≡ 20
closedEndpointDLnPaid = refl

openEndpointIs4AKE : openEndpointPdbLabel ≡ "4AKE"
openEndpointIs4AKE = refl

closedEndpointIs1AKE : closedEndpointPdbLabel ≡ "1AKE"
closedEndpointIs1AKE = refl

fullNamedStateDLnTableStillUnpaid : namedIntermediateDLnTablePaid ≡ false
fullNamedStateDLnTableStillUnpaid = refl

endpointValuesDoNotCreateIntermediateTable : endpointValuesCreateIntermediateDLnTable ≡ false
endpointValuesDoNotCreateIntermediateTable = refl

articleIdentityDoesNotCreateNumbers : identityMetadataCreatesEndpointDLn ≡ false
articleIdentityDoesNotCreateNumbers = refl
