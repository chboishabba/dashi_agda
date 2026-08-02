module DASHI.Foundations.TernaryGolay.MathieuSourceAtlas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources added for the explicit Mathieu-action and real stabilizer-chain
-- tranche.  Citations identify external theorem/presentation inputs; the
-- coordinate transport, design preservation and finite group enumerations
-- are recomputed independently in this repository.
------------------------------------------------------------------------

leechM12PresentationEntry : Sources.SourceEntry
leechM12PresentationEntry =
  Sources.sourceEntry
    "John Leech"
    "A Presentation of the Mathieu Group M12"
    "Canadian Mathematical Bulletin 12(1), 41-43"
    1969
    (Sources.doiRecorded "10.4153/CMB-1969-005-8")
    "https://doi.org/10.4153/CMB-1969-005-8"
    Sources.externalTheoremAwaitingFormalImport
    "source of the compact 12-point permutation presentation; the published labelling is transported to the locally computed S(5,6,12) design before use"

conwayElkiesMartinEntry : Sources.SourceEntry
conwayElkiesMartinEntry =
  Sources.sourceEntry
    "John H. Conway, Noam D. Elkies, and Jeremy L. Martin"
    "The Mathieu Group M12 and Its Pseudogroup Extension M13"
    "Experimental Mathematics 15(2), 223-236"
    2006
    (Sources.doiRecorded "10.1080/10586458.2006.10128958")
    "https://doi.org/10.1080/10586458.2006.10128958"
    Sources.externalTheoremAwaitingFormalImport
    "source connecting the M12/M13 game, ternary Golay code, 12-by-12 Hadamard matrices, double covers and automorphism groups"

atlasM11Entry : Sources.SourceEntry
atlasM11Entry =
  Sources.sourceEntry
    "R. A. Wilson, R. A. Parker, S. Nickerson, J. N. Bray, and collaborators"
    "ATLAS of Finite Group Representations: Mathieu group M11"
    "ATLAS of Finite Group Representations"
    2026
    Sources.noDOIRecordedHere
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M11/"
    Sources.externalTheoremAwaitingFormalImport
    "calibration for the M11 subgroup L2(11) of order 660 and index 12; it is not identified with the ordered two-point stabilizer, whose local orbit arithmetic gives order 720"

mathieuSupplementSources : List Sources.SourceEntry
mathieuSupplementSources =
  leechM12PresentationEntry
  ∷ conwayElkiesMartinEntry
  ∷ atlasM11Entry
  ∷ []

mathieuSupplementSourceCount : Nat
mathieuSupplementSourceCount = Sources.sourceCount mathieuSupplementSources

mathieuSupplementSourceCountIsThree :
  mathieuSupplementSourceCount ≡ 3
mathieuSupplementSourceCountIsThree = refl

mathieuSourceAtlasReceipt : GenericReceipt.GenericReceipt
mathieuSourceAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Mathieu action source atlas supplement"
    "DASHI.Foundations.TernaryGolay.MathieuSourceAtlas"
    "mathieuSupplementSources"
    "John Leech's two-generator presentation, Conway-Elkies-Martin's Hadamard/Golay double-cover construction, and the ATLAS M11/L2(11) subgroup calibration are attached with author, title, URL and DOI where available"
    "the citations do not replace coordinate transport, code/design preservation, group-order enumeration, stabilizer disambiguation or an Agda proof of group isomorphism"
    "agda -i . DASHI/Foundations/TernaryGolay/MathieuSourceAtlas.agda"

mathieuSourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim mathieuSourceAtlasReceipt ≡ false
mathieuSourceAtlasReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse mathieuSourceAtlasReceipt
