module DASHI.Astronomy.LocalGroupFirstLightClaimGraphExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Snowball graph: private source -> artefact -> attributed benchmark claim ->
-- comparison paper -> independent reproduction receipt.
------------------------------------------------------------------------

data ClaimNodeKind : Set where
  privatePostNode : ClaimNodeKind
  artefactNode : ClaimNodeKind
  posterClaimNode : ClaimNodeKind
  scientificSourceNode : ClaimNodeKind
  verificationReceiptNode : ClaimNodeKind
  unresolvedResidualNode : ClaimNodeKind

record ClaimNode : Set where
  constructor claimNode
  field
    nodeKind : ClaimNodeKind
    label : String

record ClaimEdge : Set where
  constructor claimEdge
  field
    edgeFrom : ClaimNode
    edgeTo : ClaimNode
    relationship : String

postNode : ClaimNode
postNode = claimNode privatePostNode "Poppie / NOUS private post — 2026-09-07 23:38"

firstLightArtefactNode : ClaimNode
firstLightArtefactNode = claimNode artefactNode "first-light.png"

lmcClaimNode : ClaimNode
lmcClaimNode = claimNode posterClaimNode "LMC <=0.03 sigma six-component reproduction claim"

sgrClaimNode : ClaimNode
sgrClaimNode = claimNode posterClaimNode "Sagittarius last-printed-digit reproduction claim"

sgrAClaimNode : ClaimNode
sgrAClaimNode = claimNode posterClaimNode "Sgr A* 0.85 sigma frame-agreement claim"

mcConnachieClaimNode : ClaimNode
mcConnachieClaimNode = claimNode posterClaimNode "McConnachie derived-distance RMS reconstruction claim"

kkh86Node : ClaimNode
kkh86Node = claimNode unresolvedResidualNode "KKH 86 1.2 kpc unresolved residual"
