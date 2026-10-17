module DASHI.Unified.TOEPrimitiveMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Primitive-leaf recut of the current TOE frontier.
--
-- This module does not re-prove sibling-branch theorems.  It records the first
-- theorem-bearing leaves after contracting wrappers that the owning branches
-- already compile.  Attribution is therefore part of the data.
------------------------------------------------------------------------

data ReceiptAuthority : Set where
  dashiLocalTheorem : ReceiptAuthority
  dashiSiblingFormalSource : ReceiptAuthority
  externalFormalSource : ReceiptAuthority
  externalScientificSource : ReceiptAuthority

record PrimitiveSourceReceipt : Set where
  field
    repository : String
    pullRequest : Nat
    headCommit : String
    moduleName : String
    ownerClaim : String
    authority : ReceiptAuthority
    localAgdaTheorem : Bool

-- Receipt projections intentionally remain namespaced.  DASHITOEEverything
-- re-exports many provenance records and generic names such as `repository` or
-- `authority` must not become ambiguous global theorem-surface names.

siblingReceipt : Nat → String → String → String → PrimitiveSourceReceipt
siblingReceipt pr head moduleName claim = record
  { repository = "chboishabba/dashi_agda"
  ; pullRequest = pr
  ; headCommit = head
  ; moduleName = moduleName
  ; ownerClaim = claim
  ; authority = dashiSiblingFormalSource
  ; localAgdaTheorem = false
  }

siblingFormalSourceIsLocalAgdaTheorem : Bool
siblingFormalSourceIsLocalAgdaTheorem = false

------------------------------------------------------------------------
-- Monster/3B primitive frontier.
------------------------------------------------------------------------

monsterLinearHardeningReceipt : PrimitiveSourceReceipt
monsterLinearHardeningReceipt =
  siblingReceipt 1162 "428e16375796971238ed3aaeb50e76e40aa78696"
    "DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact"
    "Proof-relevant wrapper types exist for the full weight-two linear bridge and literal-zeta single-action producer; neither actual selected Monster inhabitant is supplied there."

monsterHZetaCompilerReceipt : PrimitiveSourceReceipt
monsterHZetaCompilerReceipt =
  siblingReceipt 1162 "428e16375796971238ed3aaeb50e76e40aa78696"
    "DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact"
    "Given concrete Schrodinger/actual constituent fixed-phase representations and same-character transport, compiles the equivariant H_zeta isomorphism and paid recognition wrapper."

monsterIsotypicCompilerReceipt : PrimitiveSourceReceipt
monsterIsotypicCompilerReceipt =
  siblingReceipt 1162 "428e16375796971238ed3aaeb50e76e40aa78696"
    "DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact"
    "Records the companion Lean generic simple-subobject classifier, semisimple/isotypic assembly and post-recognition copy-count compiler; actual Monster instantiation is not paid."

record MonsterPrimitiveFrontier : Set where
  field
    linearHardeningSource : PrimitiveSourceReceipt
    hZetaCompilerSource : PrimitiveSourceReceipt
    isotypicCompilerSource : PrimitiveSourceReceipt
    genericClassifierStillTerminal : Bool
    genericIsotypicAssemblyStillTerminal : Bool
    actualWeightTwoLinearBridgePaid : Bool
    actualLinearRestrictionPaid : Bool
    actualWholeCharacterSimpleNonzeroInputsPaid : Bool
    actualHZetaSameObjectRecognitionPaid : Bool
    actualIsotypicRecognitionPaid : Bool
    actualMultiplicityNinetyPaid : Bool
    actualMultiplicityHomNormalizerActionPaid : Bool
    actualTwelveSeventyEightActionIntertwinerPaid : Bool
open MonsterPrimitiveFrontier public

monsterPrimitiveFrontier : MonsterPrimitiveFrontier
monsterPrimitiveFrontier = record
  { linearHardeningSource = monsterLinearHardeningReceipt
  ; hZetaCompilerSource = monsterHZetaCompilerReceipt
  ; isotypicCompilerSource = monsterIsotypicCompilerReceipt
  ; genericClassifierStillTerminal = false
  ; genericIsotypicAssemblyStillTerminal = false
  ; actualWeightTwoLinearBridgePaid = false
  ; actualLinearRestrictionPaid = false
  ; actualWholeCharacterSimpleNonzeroInputsPaid = false
  ; actualHZetaSameObjectRecognitionPaid = false
  ; actualIsotypicRecognitionPaid = false
  ; actualMultiplicityNinetyPaid = false
  ; actualMultiplicityHomNormalizerActionPaid = false
  ; actualTwelveSeventyEightActionIntertwinerPaid = false
  }

monsterGenericClassifierStillTerminal : Bool
monsterGenericClassifierStillTerminal = genericClassifierStillTerminal monsterPrimitiveFrontier

monsterActualLinearRestrictionPaid : Bool
monsterActualLinearRestrictionPaid = actualLinearRestrictionPaid monsterPrimitiveFrontier

------------------------------------------------------------------------
-- Gauge/QFT/GR primitive frontier.
------------------------------------------------------------------------

pinnedR457CompilerReceipt : PrimitiveSourceReceipt
pinnedR457CompilerReceipt =
  siblingReceipt 1165 "64c8d33320a8e313064a565068ae399566b4de23"
    "DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact"
    "On the canonical pinned route, R114+R119 build R120; R120+R122 build R123; R123+R124 build R125; pinned continuum plus R127 closes R126/R128/R457. No independent R120/R123/R125/R126 or Y_R457=Y_pinned payment remains."

round131RecoveryCompilerReceipt : PrimitiveSourceReceipt
round131RecoveryCompilerReceipt =
  siblingReceipt 1165 "64c8d33320a8e313064a565068ae399566b4de23"
    "DASHI.Physics.QuantumVacuum.CasimirRound131PinnedRecoveryCompilerExact"
    "Pinned-literal = selected qftTarget plus the existing QFTRecoveryReceipt compiles Round131RecoveredQFTAttachment; on the pinned route construction identity is definitional rather than an independent theorem."

sourceNativeTerminalReceipt : PrimitiveSourceReceipt
sourceNativeTerminalReceipt =
  siblingReceipt 1165 "64c8d33320a8e313064a565068ae399566b4de23"
    "DASHI.Physics.QuantumVacuum.Casimir369StressEnergySourceNativeTerminalExact"
    "Authoritative primitive-leaf ordering for the selected Casimir/GRQFT route, beginning with the pinned Yang-Mills construction and R114/R119/R122/R124/R127 source semantics."

record GaugePrimitiveFrontier : Set where
  field
    pinnedR457CompilerSource : PrimitiveSourceReceipt
    round131CompilerSource : PrimitiveSourceReceipt
    terminalSource : PrimitiveSourceReceipt
    round131AttachmentStillPrimitive : Bool
    r457PinnedConstructionIdentityStillPrimitive : Bool
    pinnedYangMillsConstructionPaid : Bool
    r114LiteralStressCoordinatePaid : Bool
    r119SelectedMetricStressSemanticsPaid : Bool
    r122LiteralDensityAnchoringPaid : Bool
    r124DensityFiniteMeasureWeldPaid : Bool
    r127SourceOSSchwingerWeldPaid : Bool
    pinnedLiteralSelectedQFTTargetIdentityPaid : Bool
    selectedGroupQuaternionSU2RealizationPaid : Bool
    selectedQFTCartanFieldRealizationPaid : Bool
    freeMaxwellActionNormalizationPaid : Bool
    selectedCurvatureSameObjectTransportPaid : Bool
    generatedActionPathStressAttachmentsPaid : Bool
    brownMaclayFullStressAttachmentPaid : Bool
    round131AllSectorAssemblyPaid : Bool
    einsteinCommonMetricVariationPaid : Bool
open GaugePrimitiveFrontier public

gaugePrimitiveFrontier : GaugePrimitiveFrontier
gaugePrimitiveFrontier = record
  { pinnedR457CompilerSource = pinnedR457CompilerReceipt
  ; round131CompilerSource = round131RecoveryCompilerReceipt
  ; terminalSource = sourceNativeTerminalReceipt
  ; round131AttachmentStillPrimitive = false
  ; r457PinnedConstructionIdentityStillPrimitive = false
  ; pinnedYangMillsConstructionPaid = false
  ; r114LiteralStressCoordinatePaid = false
  ; r119SelectedMetricStressSemanticsPaid = false
  ; r122LiteralDensityAnchoringPaid = false
  ; r124DensityFiniteMeasureWeldPaid = false
  ; r127SourceOSSchwingerWeldPaid = false
  ; pinnedLiteralSelectedQFTTargetIdentityPaid = false
  ; selectedGroupQuaternionSU2RealizationPaid = false
  ; selectedQFTCartanFieldRealizationPaid = false
  ; freeMaxwellActionNormalizationPaid = false
  ; selectedCurvatureSameObjectTransportPaid = false
  ; generatedActionPathStressAttachmentsPaid = false
  ; brownMaclayFullStressAttachmentPaid = false
  ; round131AllSectorAssemblyPaid = false
  ; einsteinCommonMetricVariationPaid = false
  }

round131AttachmentStillPrimitive : Bool
round131AttachmentStillPrimitive = GaugePrimitiveFrontier.round131AttachmentStillPrimitive gaugePrimitiveFrontier

r457PinnedConstructionIdentityStillPrimitive : Bool
r457PinnedConstructionIdentityStillPrimitive = GaugePrimitiveFrontier.r457PinnedConstructionIdentityStillPrimitive gaugePrimitiveFrontier

gaugePrimitiveSourceLeavesPaid : Bool
gaugePrimitiveSourceLeavesPaid = false

------------------------------------------------------------------------
-- Arithmetic/CM and quantum physical primitive leaves.
------------------------------------------------------------------------

record ArithmeticPrimitiveFrontier : Set where
  field
    canonicalCubicCharacterCubeFibreCertificatePaid : Bool
    cubicJacobiSelectedPrimaryEvaluationPaid : Bool
    splitPrimeFrobeniusPaid : Bool
    sameCurveHeckeGroessencharacterPaid : Bool
    allGoodPrimeEulerAgreementPaid : Bool
open ArithmeticPrimitiveFrontier public

arithmeticPrimitiveFrontier : ArithmeticPrimitiveFrontier
arithmeticPrimitiveFrontier = record
  { canonicalCubicCharacterCubeFibreCertificatePaid = false
  ; cubicJacobiSelectedPrimaryEvaluationPaid = false
  ; splitPrimeFrobeniusPaid = false
  ; sameCurveHeckeGroessencharacterPaid = false
  ; allGoodPrimeEulerAgreementPaid = false
  }

record QuantumPrimitiveFrontier : Set where
  field
    selectedHilbertToFiniteGTPSAttachmentPaid : Bool
    physicalSourceGTPSPaid : Bool
    physicalHamiltonianAttachmentPaid : Bool
    minimizerDerivativePullbackPaid : Bool
    thermodynamicLimitPaid : Bool
    sameStateRTHolographicWeldPaid : Bool
open QuantumPrimitiveFrontier public

quantumPrimitiveFrontier : QuantumPrimitiveFrontier
quantumPrimitiveFrontier = record
  { selectedHilbertToFiniteGTPSAttachmentPaid = false
  ; physicalSourceGTPSPaid = false
  ; physicalHamiltonianAttachmentPaid = false
  ; minimizerDerivativePullbackPaid = false
  ; thermodynamicLimitPaid = false
  ; sameStateRTHolographicWeldPaid = false
  }

record CurrentPrimitiveMaxCut : Set where
  field
    monster : MonsterPrimitiveFrontier
    gaugeQFTGR : GaugePrimitiveFrontier
    arithmeticCM : ArithmeticPrimitiveFrontier
    quantumMatter : QuantumPrimitiveFrontier
    wrapperDebtContracted : Bool
    attributionFirewallRetained : Bool
open CurrentPrimitiveMaxCut public

currentPrimitiveMaxCut : CurrentPrimitiveMaxCut
currentPrimitiveMaxCut = record
  { monster = monsterPrimitiveFrontier
  ; gaugeQFTGR = gaugePrimitiveFrontier
  ; arithmeticCM = arithmeticPrimitiveFrontier
  ; quantumMatter = quantumPrimitiveFrontier
  ; wrapperDebtContracted = true
  ; attributionFirewallRetained = true
  }

primitiveTerminalReading : String
primitiveTerminalReading =
  "The current max-cut is source-leaf exact. Monster begins at actual weight-two/literal-zeta linear restrictions and actual whole-character/simple/nonzero inputs, not generic classifier/isotypic machinery. The selected GRQFT route begins at a concrete pinned Yang-Mills construction plus R114/R119/R122/R124/R127 and pinned-literal=qftTarget, not Round131/R457 wrapper equalities. Arithmetic begins at the cubic-character/Jacobi split-prime evaluation; quantum begins at the same-physical Hilbert/g-TPS/Hamiltonian attachment. Sibling receipts preserve source ownership and do not become local Agda theorems."
