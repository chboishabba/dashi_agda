module DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas where

open import DASHI.Core.Prelude
open import Data.List using (_++_)

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5SourceAtlas as R5

artinBraidSource : R4.SourceRecord
artinBraidSource =
  R4.sourceRecord
    "Emil Artin"
    "Theory of Braids"
    "Annals of Mathematics"
    1947
    "10.2307/1969218"
    "Supports the braid generators and Yang--Baxter/Artin relation used by the triadic endpoint action."
    "The finite permutation action factors through the symmetric group and is not claimed to be a faithful braid representation."

falconerFractalSource : R4.SourceRecord
falconerFractalSource =
  R4.sourceRecord
    "Kenneth Falconer"
    "Fractal Geometry: Mathematical Foundations and Applications"
    "John Wiley and Sons"
    2003
    "10.1002/0470013850"
    "Supports self-similar ternary refinement, polar Cantor restriction, and the separation of symbolic address from geometric realization."
    "The repository's finite cyclic wheel is not asserted to be a unique standard object universally named the Cantor wheel."

freudDreamInterpretationSource : R4.SourceRecord
freudDreamInterpretationSource =
  R4.sourceRecord
    "Sigmund Freud"
    "The Interpretation of Dreams"
    "Franz Deuticke"
    1900
    "no DOI recorded"
    "Supplies historical provenance for associative interpretation, latent-theme hypotheses, and attention to what a participant selects or elaborates."
    "Free association is not treated as independent verification, recovered-memory authority, or an external prediction channel."

reserAboriginalMemorySource : R4.SourceRecord
reserAboriginalMemorySource =
  R4.sourceRecord
    "David Reser; Margaret Simmons; Esther Johns; Andrew Ghaly; Michelle Quayle; Aimee L. Dordevic; Marianne Tare; Adelle McArdle; Julie Willems; Tyson Yunkaporta"
    "Australian Aboriginal Techniques for Memorization: Translation into a Medical and Allied Health Education Setting"
    "PLOS ONE"
    2021
    "10.1371/journal.pone.0251710"
    "Supports a bounded example of narrative-place indexing improving finite recall in a medical-education setting."
    "The result is not generalized to all Indigenous traditions or used to reduce Indigenous knowledge to memory technique."

stametsMyceliumSource : R4.SourceRecord
stametsMyceliumSource =
  R4.sourceRecord
    "Paul Stamets"
    "Mycelium Running: How Mushrooms Can Help Save the World"
    "Ten Speed Press"
    2005
    "no DOI recorded; ISBN 9781580085793"
    "Supplies architectural and ecological provenance for mycelial transport, decomposition, mycofiltration, mycoremediation, and restoration-oriented hyperfabric hypotheses."
    "The book is not treated as proof of forest-wide intention, universal optimization, or every popular wood-wide-web claim."

canonicalRound5ExtendedSources : List R4.SourceRecord
canonicalRound5ExtendedSources =
  R5.canonicalRound5Sources
  ++
  (artinBraidSource
    ∷ falconerFractalSource
    ∷ freudDreamInterpretationSource
    ∷ reserAboriginalMemorySource
    ∷ stametsMyceliumSource
    ∷ [])

canonicalRound5ExtendedSourceCount : Nat
canonicalRound5ExtendedSourceCount =
  R4.listCount canonicalRound5ExtendedSources

canonicalRound5ExtendedSourceCountIsTwentyThree :
  canonicalRound5ExtendedSourceCount ≡ 23
canonicalRound5ExtendedSourceCountIsTwentyThree = refl
