module DASHI.Biology.ConsciousAccessRound7AristotleSourceBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5SourceAtlas as R5
import DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas as R5X

------------------------------------------------------------------------
-- External scholarly provenance is reused from the existing source atlases.
-- Internal theorem provenance names the exact supplied Aristotle archive owner;
-- no DOI or authorship is invented for repository-local theorem files.

canonicalExternalSources : List R4.SourceRecord
canonicalExternalSources =
  R4.serreArithmeticSource
  ∷ R5.chungSpectralGraphSource
  ∷ R5.arichetaOggSource
  ∷ R5X.artinBraidSource
  ∷ []

externalSourceCount : Nat
externalSourceCount = R4.listCount canonicalExternalSources

externalSourceCountIsFour : externalSourceCount ≡ 4
externalSourceCountIsFour = refl

record AristotleArchiveOwner : Set where
  constructor aristotleArchiveOwner
  field
    path : String
    importedTheoremRole : String
    excludedPromotion : String

open AristotleArchiveOwner public

ternaryHubOwner : AristotleArchiveOwner
ternaryHubOwner =
  aristotleArchiveOwner
    "Lean/Integration/TernaryHub.lean"
    "Balanced ternary carriers transport to a common ZMod-3 hub with inversion equivariance."
    "The Agda finite orientation carrier is not claimed to reproduce the full Lean equivalence classification."

ternaryPhaseOwner : AristotleArchiveOwner
ternaryPhaseOwner =
  aristotleArchiveOwner
    "Lean/Spine/TernaryPhase.lean"
    "Real C3 splits into fixed and two-dimensional mean-zero transverse sectors; the cyclic shift has no nonzero real transverse eigenline."
    "The Agda finite phase-direction shadow is not a replacement proof of real representation theory."

tritCarrierOwner : AristotleArchiveOwner
tritCarrierOwner =
  aristotleArchiveOwner
    "Lean/Spine/TritCarrier.lean"
    "Ternary rotation and reflection obey a dihedral conjugacy relation and are structurally distinct."
    "Finite operator separation is not promoted to a faithful braid or continuum representation."

observerOwner : AristotleArchiveOwner
observerOwner =
  aristotleArchiveOwner
    "Lean/Spine/Observer.lean"
    "Observer inheritance requires nonzero anchoring and non-flat transverse channel; constant channels have zero transverse area."
    "Nat-valued area codes are not calibrated neural measurements or Euclidean Gram determinants."

oggOwner : AristotleArchiveOwner
oggOwner =
  aristotleArchiveOwner
    "Lean/Spine/OggGrid.lean"
    "The Ogg CM observer has a unique ramified class and blocks a free ternary equivariant labelling despite cardinality 15 = 5 * 3."
    "The extracted Agda no-go does not construct the full Ogg arithmetic or Monster action."

dualityOwner : AristotleArchiveOwner
dualityOwner =
  aristotleArchiveOwner
    "Lean/Spine/Duality.lean"
    "Odd-dimensional alternating forms are degenerate; Hamiltonian language requires supplied symplectic phase-space structure."
    "The Agda admission gate is not a reproof of the real matrix determinant theorem."

canonicalArchiveOwners : List AristotleArchiveOwner
canonicalArchiveOwners =
  ternaryHubOwner
  ∷ ternaryPhaseOwner
  ∷ tritCarrierOwner
  ∷ observerOwner
  ∷ oggOwner
  ∷ dualityOwner
  ∷ []

archiveOwnerCount : Nat
archiveOwnerCount = R4.listCount canonicalArchiveOwners

archiveOwnerCountIsSix : archiveOwnerCount ≡ 6
archiveOwnerCountIsSix = refl
