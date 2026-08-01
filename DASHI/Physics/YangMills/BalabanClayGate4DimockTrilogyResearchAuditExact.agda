module DASHI.Physics.YangMills.BalabanClayGate4DimockTrilogyResearchAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source audit for Dimock's three-part exposition of Bałaban's method.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban, I. Small Fields",
-- Reviews in Mathematical Physics 25 (7) (2013), article 1330010.
-- arXiv:1108.1335v2 [math-ph].
-- DOI: 10.1142/S0129055X13300100.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban. II. Large Fields",
-- Journal of Mathematical Physics 54 (9) (2013), article 092301.
-- arXiv:1212.5562v2 [math-ph].
-- DOI: 10.1063/1.4821275.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (11) (2014), 2133--2175.
-- arXiv:1304.0705v1 [math-ph].
-- DOI: 10.1007/s00023-013-0303-3.
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

dimockPublishedMetadataAuditLevel : ProofLevel
dimockPublishedMetadataAuditLevel = machineChecked

dimockTrilogyScopeAuditLevel : ProofLevel
dimockTrilogyScopeAuditLevel = machineChecked

physicalYangMillsUseOfDimockArchitectureInputsLevel : ProofLevel
physicalYangMillsUseOfDimockArchitectureInputsLevel = conditional
