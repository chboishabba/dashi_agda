module DASHI.Physics.YangMills.BalabanClayLargeFieldVerifiedLiteratureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Gate-4 large-field provenance.
--
-- These records identify sources and their role.  Importing this module does
-- not inhabit any large-field analytic theorem.
------------------------------------------------------------------------

record LargeFieldLiteratureSource : Set where
  constructor source
  field
    authors : String
    title : String
    venueYearPages : String
    doi : String
    arxiv : String
    theoremOrMechanism : String
    relationshipToDASHI : String

open LargeFieldLiteratureSource public

balabanLargeFieldI : LargeFieldLiteratureSource
balabanLargeFieldI = source
  "Tadeusz Bałaban"
  "Large Field Renormalization. I. The Basic Step of the R Operation"
  "Communications in Mathematical Physics 122 (1989), 175--202"
  "10.1007/BF01257412"
  ""
  "construction of the R operation for expressions associated with large-field regions"
  "primary gauge-theory source for large-field regions, determining sets, the T operation and the basic R step"

balabanLargeFieldII : LargeFieldLiteratureSource
balabanLargeFieldII = source
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "10.1007/BF01238433"
  ""
  "localization, exponentiation, boundary terms, R-operation bounds and completion of the stated ultraviolet-stability theorem"
  "primary gauge-theory source for Gate-4 large-field closure and the scale-uniform admissible-coupling-domain target"

dimockBalabanI : LargeFieldLiteratureSource
dimockBalabanI = source
  "J. Dimock"
  "The Renormalization Group According to Balaban. I. Small Fields"
  "Reviews in Mathematical Physics 25 (2013), expository scalar phi-four analysis"
  ""
  "arXiv:1108.1335"
  "small-field RG architecture in a three-dimensional scalar model"
  "architectural exposition only; not authority for four-dimensional non-Abelian gauge estimates"

dimockBalabanII : LargeFieldLiteratureSource
dimockBalabanII = source
  "J. Dimock"
  "The Renormalization Group According to Balaban. II. Large Fields"
  "arXiv preprint"
  ""
  "arXiv:1212.5562"
  "large-field contribution to the partition function in a three-dimensional scalar phi-four model"
  "translation aid for characteristic functions, enlargements and exponentiation; Balaban remains the gauge-specific authority"

largeFieldVerifiedSources : List LargeFieldLiteratureSource
largeFieldVerifiedSources =
  balabanLargeFieldI ∷ balabanLargeFieldII ∷
  dimockBalabanI ∷ dimockBalabanII ∷ []
