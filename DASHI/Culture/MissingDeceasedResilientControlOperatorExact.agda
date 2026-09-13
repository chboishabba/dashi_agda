module DASHI.Culture.MissingDeceasedResilientControlOperatorExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ScientificOperatorFamilyExact as O

leblancResilientControl : O.OperatorFactorisation
leblancResilientControl = O.operator-factorisation
  "Joshua Kyle LeBlanc"
  "DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact"
  O.resilientControlShape
  "harsh environment + sensor/function requirements -> diagnostic state -> autonomous/off-normal response"
  "The shared operator is sensing/verification/control under harsh conditions; FSP qualification remains domain-specific."

mccaslandResilientControl : O.OperatorFactorisation
mccaslandResilientControl = O.operator-factorisation
  "William Neil McCasland"
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact"
  O.resilientControlShape
  "plant + candidate placements + failure family -> Gramian scoring -> robust sensor/actuator placement"
  "Placement optimisation is the reusable control operator; it does not identify the same plant or failure physics as FSP/UAV systems."

zhangDaibingResilientControl : O.OperatorFactorisation
zhangDaibingResilientControl = O.operator-factorisation
  "Zhang Daibing"
  "DASHI.Control.ZhangDaibingUAVControlBidiExact"
  O.resilientControlShape
  "vehicle/sensor state -> localisation/guidance/control -> landing/path/formation response"
  "Autonomy/control shares estimation-action structure while preserving vehicle dynamics and gains as separate science."

chenResilientVerification : O.OperatorFactorisation
chenResilientVerification = O.operator-factorisation
  "Chen Shuming"
  "DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact"
  O.resilientControlShape
  "hardware graph + stimulus + observed trace -> conformance/coverage check -> verification residual"
  "Verification plays the state-assurance role; it is not literally feedback control."

yanResilientFlowControl : O.OperatorFactorisation
yanResilientFlowControl = O.operator-factorisation
  "Yan Hong"
  "DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact"
  O.resilientControlShape
  "inlet flow + actuator state -> shock/boundary-layer response -> controlled flow state"
  "Flow-control response shares sensing/action/residual structure; hypersonic fluid physics remain domain-owned."

resilientControlFactorisations : List O.OperatorFactorisation
resilientControlFactorisations =
  leblancResilientControl ∷ mccaslandResilientControl ∷ zhangDaibingResilientControl ∷
  chenResilientVerification ∷ yanResilientFlowControl ∷ []
