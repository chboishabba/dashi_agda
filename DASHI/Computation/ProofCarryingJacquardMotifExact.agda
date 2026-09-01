module DASHI.Computation.ProofCarryingJacquardMotifExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (_++_)

import DASHI.Combinatorics.ProofFabricCompilerExact as ProofFabric
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Carrying
import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible

------------------------------------------------------------------------
-- STRUCTURAL PROOF MOTIFS ON THE ACTUAL JACQUARD BACKEND
--
-- One proof motif occupies two Jacquard rows x two warp ends = four visible
-- binary cells.  Six even-parity codewords are assigned to the six structural
-- proof motifs.  All other four-cell patterns are rejected by the decoder.
--
-- This is not merely a byte encoding: the decoded symbol is the structural
-- rule-class annotation carried by CertifiedFabricPatch.
------------------------------------------------------------------------

MotifTilePair : Set
MotifTilePair = ProofFabric.ProofWeaveTile × ProofFabric.ProofWeaveTile

motifTiles : Carrying.ProofMotif → MotifTilePair
motifTiles Carrying.premiseMotif =
  ProofFabric.tile00 , ProofFabric.tile00
motifTiles Carrying.branchMotif =
  ProofFabric.tile00 , ProofFabric.tile11
motifTiles Carrying.dischargeMotif =
  ProofFabric.tile01 , ProofFabric.tile01
motifTiles Carrying.rewriteMotif =
  ProofFabric.tile01 , ProofFabric.tile10
motifTiles Carrying.lemmaReferenceMotif =
  ProofFabric.tile10 , ProofFabric.tile01
motifTiles Carrying.conclusionMotif =
  ProofFabric.tile10 , ProofFabric.tile10

motifTileList : Carrying.ProofMotif → List ProofFabric.ProofWeaveTile
motifTileList motif = proj₁ (motifTiles motif) ∷ proj₂ (motifTiles motif) ∷ []

motifJacquardProgram : Carrying.ProofMotif → Jacquard.JacquardProgram 2
motifJacquardProgram motif =
  Visible.compileTilesToJacquard (motifTileList motif)

motifVisiblePattern : Carrying.ProofMotif → Visible.VisiblePattern2
motifVisiblePattern motif =
  Visible.visibleProgram2 (motifJacquardProgram motif)

motifVisibleExecutionExact :
  (motif : Carrying.ProofMotif) →
  motifVisiblePattern motif
  ≡ Visible.visiblePatternOfTiles (motifTileList motif)
motifVisibleExecutionExact motif =
  Visible.jacquardTilesProduceVisiblePattern (motifTileList motif)

------------------------------------------------------------------------
-- Visible structural decoder.
------------------------------------------------------------------------

readVisibleMotif : Visible.VisiblePattern2 → Maybe Carrying.ProofMotif
readVisibleMotif
  ((false , false) ∷ (false , false) ∷ []) =
  just Carrying.premiseMotif
readVisibleMotif
  ((false , false) ∷ (true , true) ∷ []) =
  just Carrying.branchMotif
readVisibleMotif
  ((false , true) ∷ (false , true) ∷ []) =
  just Carrying.dischargeMotif
readVisibleMotif
  ((false , true) ∷ (true , false) ∷ []) =
  just Carrying.rewriteMotif
readVisibleMotif
  ((true , false) ∷ (false , true) ∷ []) =
  just Carrying.lemmaReferenceMotif
readVisibleMotif
  ((true , false) ∷ (true , false) ∷ []) =
  just Carrying.conclusionMotif
readVisibleMotif _ = nothing

visibleMotifRoundtrip :
  (motif : Carrying.ProofMotif) →
  readVisibleMotif (motifVisiblePattern motif) ≡ just motif
visibleMotifRoundtrip Carrying.premiseMotif = refl
visibleMotifRoundtrip Carrying.branchMotif = refl
visibleMotifRoundtrip Carrying.dischargeMotif = refl
visibleMotifRoundtrip Carrying.rewriteMotif = refl
visibleMotifRoundtrip Carrying.lemmaReferenceMotif = refl
visibleMotifRoundtrip Carrying.conclusionMotif = refl

------------------------------------------------------------------------
-- Two reserved even-parity patterns are intentionally not proof motifs.
------------------------------------------------------------------------

reservedStructuralPatternA : Visible.VisiblePattern2
reservedStructuralPatternA =
  (true , true) ∷ (false , false) ∷ []

reservedStructuralPatternB : Visible.VisiblePattern2
reservedStructuralPatternB =
  (true , true) ∷ (true , true) ∷ []

reservedStructuralPatternARejected :
  readVisibleMotif reservedStructuralPatternA ≡ nothing
reservedStructuralPatternARejected = refl

reservedStructuralPatternBRejected :
  readVisibleMotif reservedStructuralPatternB ≡ nothing
reservedStructuralPatternBRejected = refl

------------------------------------------------------------------------
-- Certified logical patch -> actual Jacquard patch -> visible motif -> same
-- structural proof motif.
------------------------------------------------------------------------

patchJacquardProgram :
  {State Rule : Set}
  {system : DASHI.Core.ProofCarryingRuleApplicationExact.RuleApplicationSystem State Rule}
  {assignment : Carrying.MotifAssignment Rule}
  {occurrence : Carrying.RuleOccurrence system} →
  Carrying.CertifiedFabricPatch assignment occurrence →
  Jacquard.JacquardProgram 2
patchJacquardProgram patch =
  motifJacquardProgram (Carrying.physicalMotif patch)

patchVisiblePattern :
  {State Rule : Set}
  {system : DASHI.Core.ProofCarryingRuleApplicationExact.RuleApplicationSystem State Rule}
  {assignment : Carrying.MotifAssignment Rule}
  {occurrence : Carrying.RuleOccurrence system} →
  Carrying.CertifiedFabricPatch assignment occurrence →
  Visible.VisiblePattern2
patchVisiblePattern patch =
  Visible.visibleProgram2 (patchJacquardProgram patch)

certifiedPatchVisibleRoundtrip :
  {State Rule : Set}
  {system : DASHI.Core.ProofCarryingRuleApplicationExact.RuleApplicationSystem State Rule}
  {assignment : Carrying.MotifAssignment Rule}
  {occurrence : Carrying.RuleOccurrence system} →
  (patch : Carrying.CertifiedFabricPatch assignment occurrence) →
  readVisibleMotif (patchVisiblePattern patch)
  ≡ just (Carrying.physicalMotif patch)
certifiedPatchVisibleRoundtrip patch =
  visibleMotifRoundtrip (Carrying.physicalMotif patch)

------------------------------------------------------------------------
-- Entire certified fabric traces compile to sequential Jacquard programs.
------------------------------------------------------------------------

compileFabricTraceToJacquard :
  {State Rule : Set}
  {system : DASHI.Core.ProofCarryingRuleApplicationExact.RuleApplicationSystem State Rule}
  {assignment : Carrying.MotifAssignment Rule}
  {state : State}
  {trace : DASHI.Core.ProofCarryingRuleApplicationExact.CertifiedRuleTrace system state} →
  Carrying.CertifiedFabricTrace assignment trace →
  Jacquard.JacquardProgram 2
compileFabricTraceToJacquard Carrying.fabricDone = []
compileFabricTraceToJacquard
  (Carrying.fabricChoose selected patch rest) =
  patchJacquardProgram patch ++ compileFabricTraceToJacquard rest

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data VisibleMotifAloneProvesAdmissibility : Set where
data AnyFourCellPatternIsAProofMotif : Set where

visibleMotifAloneDoesNotProveAdmissibility :
  VisibleMotifAloneProvesAdmissibility → ⊥
visibleMotifAloneDoesNotProveAdmissibility ()

notEveryFourCellPatternIsAProofMotif :
  AnyFourCellPatternIsAProofMotif → ⊥
notEveryFourCellPatternIsAProofMotif ()

record ProofCarryingJacquardBoundary : Set where
  constructor proof-carrying-jacquard-boundary
  field
    sixStructuralMotifsHaveVisibleJacquardRealisation : Bool
    visibleMotifsDecodeExactly : Bool
    reservedVisiblePatternsRejected : Bool
    certifiedPatchCarriesLogicalAdmissibilitySeparately : Bool
    certifiedFabricTraceCompilesSequentially : Bool
    visibleMotifAloneCreatesRuleAdmissibility : Bool

canonicalProofCarryingJacquardBoundary : ProofCarryingJacquardBoundary
canonicalProofCarryingJacquardBoundary =
  proof-carrying-jacquard-boundary true true true true true false
