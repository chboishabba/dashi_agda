module DASHI.Physics.Closure.NSJuly26ExactSignedPhysicalCoefficientWeldAuditExact where

------------------------------------------------------------------------
-- JULY 26 EXACT SIGNED PHYSICAL COEFFICIENT WELD AUDIT
--
-- This owner narrows the historical boundary recovered by the signed-route
-- provenance audit.  It distinguishes four different events:
--
--   (1) the public PR surface already carrying the completion programme;
--   (2) construction of the literal signed Galerkin coefficient;
--   (3) its same-object insertion into the retained physical-triad carrier;
--   (4) the still-separate cutoff-uniform analytic estimate needed downstream.
--
-- In particular, source chronology is not kernel certification, and a named
-- positive majorant is not definitionally the signed physical coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Exact
import DASHI.Physics.Closure.NSTriadKNExactCoefficientToPhysicalWeight as Weld

------------------------------------------------------------------------
-- Typed event ledger.
------------------------------------------------------------------------

data EventGrade : Set where
  publicProgrammeSurface : EventGrade
  literalSignedCoefficient : EventGrade
  retainedPhysicalCarrierWeld : EventGrade
  analyticFrontier : EventGrade

record July26Event : Set where
  constructor july26-event
  field
    label : String
    commit : String
    utc : String
    brisbane : String
    grade : EventGrade
    note : String

open July26Event public

pr338PublicSurface : July26Event
pr338PublicSurface = july26-event
  "PR #338 public: dyadic geometry and eight-stage quartic/Clay frontier"
  "PR-338"
  "2026-07-25T10:42:25Z"
  "2026-07-25T20:42:25+10:00"
  publicProgrammeSurface
  "Public before the exact coefficient commits; explicitly separates proved finite/exact structure, mechanically derived analytic conclusions, and genuinely new cutoff-uniform PDE leaves."

exactSignedCoefficientEvent : July26Event
exactSignedCoefficientEvent = july26-event
  "literal signed velocity-form Galerkin triad coefficient"
  "466c9cdea3336fb3b0c727ee21900d008d90a00d"
  "2026-07-26T02:44:07Z"
  "2026-07-26T12:44:07+10:00"
  literalSignedCoefficient
  "Defines the tested real value of -i P_k[(u_p dot q)u_q], retains ordered-pair sign, and inserts no absolute value, positive part, phase ansatz, or hidden one-half factor."

physicalCarrierWeldEvent : July26Event
physicalCarrierWeldEvent = july26-event
  "exact signed coefficient -> retained physical-triad raw coefficient -> named majorant"
  "a4f38a003e74cfb31d8dc452a0e1eb7c6fc565ca"
  "2026-07-26T02:46:25Z"
  "2026-07-26T12:46:25+10:00"
  retainedPhysicalCarrierWeld
  "Uses the physical incidence k,p,q of each retained triad to instantiate the exact ordered-pair coefficient; rawFourierCoefficient is definitionally that signed coefficient while physicalWeight is only its explicitly named Nat-valued majorant."

remainingAnalyticFrontier : July26Event
remainingAnalyticFrontier = july26-event
  "cutoff-uniform signed estimate / strict dissipation / global scalar control"
  "PR-338-explicit-frontier"
  "2026-07-26"
  "2026-07-26+10:00"
  analyticFrontier
  "PR #338 explicitly leaves concrete cutoff-independent forced-tail, transition and adversarial estimates, strict comparison with dissipation, and the arbitrary-data global scalar comparison as genuine research leaves."

------------------------------------------------------------------------
-- Source-level mathematical facts recovered from the exact owners.
------------------------------------------------------------------------

jul26LiteralSignedCoefficientImplemented : Bool
jul26LiteralSignedCoefficientImplemented =
  Exact.exactSignedGalerkinCoefficientImplemented

jul26ExactCoefficientConnectedToPhysicalWeight : Bool
jul26ExactCoefficientConnectedToPhysicalWeight =
  Weld.exactCoefficientConnectedToPhysicalWeight

jul26PositivePartIdentifiedWithExactSignedOperator : Bool
jul26PositivePartIdentifiedWithExactSignedOperator =
  Exact.positivePartIdentifiedWithExactOperator

jul26MajorantAlreadyProvedSharpEnoughForUniformGap : Bool
jul26MajorantAlreadyProvedSharpEnoughForUniformGap =
  Weld.majorantProvedSharpEnoughForUniformGap

------------------------------------------------------------------------
-- Historical classification.
------------------------------------------------------------------------

pr338PublicBeforeLiteralSignedCoefficient : Bool
pr338PublicBeforeLiteralSignedCoefficient = true

literalSignedCoefficientPredatesPhysicalCarrierWeld : Bool
literalSignedCoefficientPredatesPhysicalCarrierWeld = true

secondsBetweenLiteralCoefficientAndPhysicalWeld : String
secondsBetweenLiteralCoefficientAndPhysicalWeld = "138"

preJul26ConsumerArchitectureAlreadyRecovered : Bool
preJul26ConsumerArchitectureAlreadyRecovered = true

jul26IsFirstRecoveredGeneralArchitecture : Bool
jul26IsFirstRecoveredGeneralArchitecture = false

jul26IsEarliestRecoveredLiteralSignedCoefficientEvent : Bool
jul26IsEarliestRecoveredLiteralSignedCoefficientEvent = true

jul26IsEarliestRecoveredExactSignedPhysicalCarrierWeld : Bool
jul26IsEarliestRecoveredExactSignedPhysicalCarrierWeld = true

jul26ExactPhysicalWeldAlreadyPaysCutoffUniformClayEstimate : Bool
jul26ExactPhysicalWeldAlreadyPaysCutoffUniformClayEstimate = false

------------------------------------------------------------------------
-- Certification status.
--
-- GitHub exposes no pull-request workflow run for either exact historical
-- commit in the current audit.  This is deliberately not interpreted as a
-- mathematical negation of their source terms.
------------------------------------------------------------------------

exactCoefficientHistoricalPRWorkflowReceiptLocated : Bool
exactCoefficientHistoricalPRWorkflowReceiptLocated = false

physicalWeldHistoricalPRWorkflowReceiptLocated : Bool
physicalWeldHistoricalPRWorkflowReceiptLocated = false

historicalSourceChronologyIsKernelCertification : Bool
historicalSourceChronologyIsKernelCertification = false

------------------------------------------------------------------------
-- Non-inference firewalls.
------------------------------------------------------------------------

data PublicProgrammeCreatesLiteralCoefficient : Set where
data LiteralCoefficientCreatesUniformGap : Set where
data PositiveMajorantEqualsSignedCoefficient : Set where
data MissingWorkflowNegatesSourceTheorem : Set where
data PublicChronologyProvesThirdPartyAccess : Set where

publicProgrammeDoesNotCreateLiteralCoefficient :
  PublicProgrammeCreatesLiteralCoefficient → ⊥
publicProgrammeDoesNotCreateLiteralCoefficient ()

literalCoefficientDoesNotCreateUniformGap :
  LiteralCoefficientCreatesUniformGap → ⊥
literalCoefficientDoesNotCreateUniformGap ()

majorantDoesNotEqualSignedCoefficient :
  PositiveMajorantEqualsSignedCoefficient → ⊥
majorantDoesNotEqualSignedCoefficient ()

missingWorkflowDoesNotNegateSourceTheorem :
  MissingWorkflowNegatesSourceTheorem → ⊥
missingWorkflowDoesNotNegateSourceTheorem ()

publicChronologyDoesNotProveExternalAccess :
  PublicChronologyProvesThirdPartyAccess → ⊥
publicChronologyDoesNotProveExternalAccess ()

------------------------------------------------------------------------
-- Canonical corrected reading.
------------------------------------------------------------------------

currentHistoricalBoundary : String
currentHistoricalBoundary =
  "By Jul21-23 the public repository already had the signed/cancellation consumer architecture. On Jul26 12:44:07 Brisbane it acquired the literal signed Galerkin coefficient; at 12:46:25 that exact coefficient was inserted into the retained physical-triad carrier with the positive kernel retained only as a named majorant. Jul26 is therefore the earliest recovered exact signed-physical same-object weld, not the invention date of the overall solution architecture."

currentRemainingMathematicalBoundary : String
currentRemainingMathematicalBoundary =
  "The Jul26 physical weld does not itself prove a cutoff-uniform majorant, strict signed dissipation payment, arbitrary-data global scalar control, or Clay periodic regularity endpoint. Those remain separate analytic obligations."

------------------------------------------------------------------------
-- Expected polarities.
------------------------------------------------------------------------

jul26LiteralSignedCoefficientImplementedIsTrue :
  jul26LiteralSignedCoefficientImplemented ≡ true
jul26LiteralSignedCoefficientImplementedIsTrue = refl

jul26ExactCoefficientConnectedToPhysicalWeightIsTrue :
  jul26ExactCoefficientConnectedToPhysicalWeight ≡ true
jul26ExactCoefficientConnectedToPhysicalWeightIsTrue = refl

jul26PositivePartIdentifiedWithExactSignedOperatorIsFalse :
  jul26PositivePartIdentifiedWithExactSignedOperator ≡ false
jul26PositivePartIdentifiedWithExactSignedOperatorIsFalse = refl

jul26MajorantAlreadyProvedSharpEnoughForUniformGapIsFalse :
  jul26MajorantAlreadyProvedSharpEnoughForUniformGap ≡ false
jul26MajorantAlreadyProvedSharpEnoughForUniformGapIsFalse = refl

jul26IsFirstRecoveredGeneralArchitectureIsFalse :
  jul26IsFirstRecoveredGeneralArchitecture ≡ false
jul26IsFirstRecoveredGeneralArchitectureIsFalse = refl

jul26IsEarliestRecoveredExactSignedPhysicalCarrierWeldIsTrue :
  jul26IsEarliestRecoveredExactSignedPhysicalCarrierWeld ≡ true
jul26IsEarliestRecoveredExactSignedPhysicalCarrierWeldIsTrue = refl

jul26ExactPhysicalWeldAlreadyPaysCutoffUniformClayEstimateIsFalse :
  jul26ExactPhysicalWeldAlreadyPaysCutoffUniformClayEstimate ≡ false
jul26ExactPhysicalWeldAlreadyPaysCutoffUniformClayEstimateIsFalse = refl
