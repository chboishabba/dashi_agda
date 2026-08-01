module DASHI.Physics.YangMills.BalabanClayGate4DimockTrilogyResearchAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source audit for Dimock's three-part exposition of Bałaban's method.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - II. Large Fields",
-- arXiv:1212.5562v2 [math-ph]. No DOI recorded.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - III. Convergence",
-- arXiv:1304.0705v1 [math-ph]. No DOI recorded.
--
-- These papers prove a scalar phi^4_3 stability theorem, not the four-
-- dimensional Yang--Mills theorem.  Their importable value here is the exact
-- architecture: centred odd blocks, weighted local propagators, random-walk
-- localization, normalized polymer contraction, large-field suppression,
-- cluster expansion with holes, connected-activity exponentiation and a final
-- volume-uniform stability bound.  Every gauge-specific identification remains
-- explicit and fail-closed.
------------------------------------------------------------------------

data DimockPart : Set where
  smallFields largeFields convergence : DimockPart

record DimockTrilogyScope : Set₁ where
  field
    centredOddBlocks : Bool
    localGreenFunctionRandomWalks : Bool
    normalizedPolymerReblocking : Bool
    largeFieldSuppression : Bool
    clusterExpansionWithHoles : Bool
    connectedActivityExponentiation : Bool
    scalarPhi4Model : Bool
    nonAbelianGaugeTheorem : Bool

open DimockTrilogyScope public

verifiedDimockTrilogyScope : DimockTrilogyScope
verifiedDimockTrilogyScope = record
  { centredOddBlocks = true
  ; localGreenFunctionRandomWalks = true
  ; normalizedPolymerReblocking = true
  ; largeFieldSuppression = true
  ; clusterExpansionWithHoles = true
  ; connectedActivityExponentiation = true
  ; scalarPhi4Model = true
  ; nonAbelianGaugeTheorem = false
  }

partOrder : DimockPart → Nat
partOrder smallFields = suc zero
partOrder largeFields = suc (suc zero)
partOrder convergence = suc (suc (suc zero))

smallFieldSourceLevel : ProofLevel
smallFieldSourceLevel = standardImported

largeFieldSourceLevel : ProofLevel
largeFieldSourceLevel = standardImported

convergenceSourceLevel : ProofLevel
convergenceSourceLevel = standardImported

dimockTrilogyScopeAuditLevel : ProofLevel
dimockTrilogyScopeAuditLevel = machineChecked

physicalYangMillsUseOfDimockArchitectureInputsLevel : ProofLevel
physicalYangMillsUseOfDimockArchitectureInputsLevel = conditional
