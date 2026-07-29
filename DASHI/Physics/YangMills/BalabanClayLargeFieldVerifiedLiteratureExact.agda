module DASHI.Physics.YangMills.BalabanClayLargeFieldVerifiedLiteratureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Gate-4 large-field provenance.
--
-- The primary dependency order below follows the sequence cited by Bałaban in
-- Large Field Renormalization I and II.  These records identify sources and
-- their role.  Importing this module does not inhabit any analytic theorem.
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

balabanSmallFieldI : LargeFieldLiteratureSource
balabanSmallFieldI = source
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Communications in Mathematical Physics 109 (1987), 249--301"
  "10.1007/BF01215223"
  ""
  "small-field effective action, background/fluctuation construction and coupling renormalization"
  "primary predecessor for the existing OneStepRGCutset small-field coordinates, Ward and coupling-flow lanes"

balabanClusterExpansionsII : LargeFieldLiteratureSource
balabanClusterExpansionsII = source
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions"
  "Communications in Mathematical Physics 116 (1988), 1--22"
  "10.1007/BF01239022"
  ""
  "exponentiated cluster representation of the fluctuation-field integral"
  "primary predecessor for polymer localization, connected-family counting and exponentiation; exact theorem matching remains pending"

balabanConvergentRenormalizationExpansions : LargeFieldLiteratureSource
balabanConvergentRenormalizationExpansions = source
  "Tadeusz Bałaban"
  "Convergent Renormalization Expansions for Lattice Gauge Theories"
  "Communications in Mathematical Physics 119 (1988), 243--285"
  "10.1007/BF01217741"
  ""
  "inductive complete effective densities including large-field domains and preservation under renormalization"
  "primary candidate for the component-family convergence, localization-norm stability and effective-density invariant-shape bridges consumed by Gate 4; theorem-level attribution remains pending direct verification"

balabanLargeFieldI : LargeFieldLiteratureSource
balabanLargeFieldI = source
  "Tadeusz Bałaban"
  "Large Field Renormalization. I. The Basic Step of the R Operation"
  "Communications in Mathematical Physics 122 (1989), 175--202"
  "10.1007/BF01257412"
  ""
  "construction of the R operation for expressions associated with large-field regions"
  "primary gauge-theory source for large-field regions, determining sets, component classes, the T operation and the basic R step"

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
  "translation aid for characteristic functions, enlargements and exponentiation; Bałaban remains the gauge-specific authority"

balabanPrimaryGate4DependencySequence : List LargeFieldLiteratureSource
balabanPrimaryGate4DependencySequence =
  balabanSmallFieldI ∷ balabanClusterExpansionsII ∷
  balabanConvergentRenormalizationExpansions ∷
  balabanLargeFieldI ∷ balabanLargeFieldII ∷ []

largeFieldVerifiedSources : List LargeFieldLiteratureSource
largeFieldVerifiedSources =
  balabanSmallFieldI ∷ balabanClusterExpansionsII ∷
  balabanConvergentRenormalizationExpansions ∷
  balabanLargeFieldI ∷ balabanLargeFieldII ∷
  dimockBalabanI ∷ dimockBalabanII ∷ []
