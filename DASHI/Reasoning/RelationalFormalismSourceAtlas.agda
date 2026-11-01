module DASHI.Reasoning.RelationalFormalismSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- Relational-formalism source atlas.
--
-- This module reuses DASHI.Core.AttributedSourceCore rather than defining a
-- parallel citation schema.  Every row records author, title, publication,
-- year, DOI state, canonical URL, bounded formalisation relationship and the
-- explicit authority boundary supplied by the shared source core.
--
-- Sources constrain vocabulary and candidate mechanisms.  They do not prove
-- the motive, diagnosis, guilt, trauma status or causal history of any named
-- participant or family.  Finite cobordism/path-marker sources live in the
-- dedicated RelationalBranchGeometrySourceAtlas.
------------------------------------------------------------------------

freudPsychopathologySource : Attr.AttributedSource
freudPsychopathologySource = Attr.mkNoDOISource
  "Sigmund Freud"
  "The Psychopathology of Everyday Life"
  "S. Karger / original German publication"
  "1901"
  "https://archive.org/details/psychopathologyo00freu"
  Attr.academicBookSource
  "Historical parapraxis provenance only: slips and substitutions may be structured, but a slip does not prove hidden wish, deliberate comparison, stable projection or recovered memory."
  Attr.publicAttribution

freudDreamSource : Attr.AttributedSource
freudDreamSource = Attr.mkNoDOISource
  "Sigmund Freud"
  "The Interpretation of Dreams"
  "Franz Deuticke"
  "1900"
  "https://archive.org/details/die-traumdeutung"
  Attr.academicBookSource
  "Historical provenance for latent/manifest and associative transformation; no universal symbol dictionary or personal unconscious finding is imported."
  Attr.publicAttribution

leveltLexicalAccessSource : Attr.AttributedSource
leveltLexicalAccessSource = Attr.mkDOISource
  "Willem J. M. Levelt; Ardi Roelofs; Antje S. Meyer"
  "A theory of lexical access in speech production"
  "Behavioral and Brain Sciences"
  "1999"
  "10.1017/S0140525X99001776"
  "https://doi.org/10.1017/S0140525X99001776"
  Attr.academicArticleSource
  "Supports staged conceptual, lemma and phonological access with monitoring and correction; it does not establish the personal meaning of an individual speech error."
  Attr.publicAttribution

harleyMacAndrewSource : Attr.AttributedSource
harleyMacAndrewSource = Attr.mkDOISource
  "Trevor A. Harley; Siobhan B. G. MacAndrew"
  "Constraints Upon Word Substitution Speech Errors"
  "Journal of Psycholinguistic Research"
  "2001"
  "10.1023/A:1010421724343"
  "https://doi.org/10.1023/A:1010421724343"
  Attr.academicArticleSource
  "Supports semantic, associative, shared-feature and phonological constraints on naturally occurring substitutions; no unique family or psychodynamic cause follows."
  Attr.publicAttribution

harseyFreydSource : Attr.AttributedSource
harseyFreydSource = Attr.mkDOISource
  "Sarah J. Harsey; Jennifer J. Freyd"
  "The Influence of Deny, Attack, Reverse Victim and Offender and Insincere Apologies on Perceptions of Sexual Assault"
  "Journal of Interpersonal Violence"
  "2023"
  "10.1177/08862605231169751"
  "https://doi.org/10.1177/08862605231169751"
  Attr.academicArticleSource
  "Supports the bounded possibility that deny/attack/role-reversal sequences alter responsibility and credibility judgements; no family dispute is automatically classified as deliberate DARVO."
  Attr.publicAttribution

dutaSheafHypergraphSource : Attr.AttributedSource
dutaSheafHypergraphSource = Attr.mkDOISource
  "Iulia Duta; Giulia Cassara; Fabrizio Silvestri; Pietro Lio"
  "Sheaf Hypergraph Networks"
  "arXiv"
  "2023"
  "10.48550/arXiv.2309.17116"
  "https://doi.org/10.48550/arXiv.2309.17116"
  Attr.academicArticleSource
  "Supports typed stalk, incidence and restriction-map carriers for higher-arity local-to-global relations; no clinical inference or neural identity claim is imported."
  Attr.publicAttribution

lasalleAttractorSource : Attr.AttributedSource
lasalleAttractorSource = Attr.mkDOISource
  "Joseph P. LaSalle"
  "Some Extensions of Liapunov's Second Method"
  "IRE Transactions on Circuit Theory"
  "1960"
  "10.1109/TCT.1960.1086720"
  "https://doi.org/10.1109/TCT.1960.1086720"
  Attr.academicArticleSource
  "Supports decreasing-value and invariant-set language for distinguishing activity from transport toward a desired basin; no empirical relational Lyapunov function is inferred."
  Attr.publicAttribution

aubinViabilitySource : Attr.AttributedSource
aubinViabilitySource = Attr.mkDOISource
  "Jean-Pierre Aubin"
  "A Survey of Viability Theory"
  "SIAM Journal on Control and Optimization"
  "1990"
  "10.1137/0328044"
  "https://doi.org/10.1137/0328044"
  Attr.academicArticleSource
  "Supports separating globally nameable options from state-dependent viable trajectories; nominal possibility is not thereby agent feasibility or moral desirability."
  Attr.publicAttribution

bellmanDynamicProgrammingSource : Attr.AttributedSource
bellmanDynamicProgrammingSource = Attr.mkDOISource
  "Richard Bellman"
  "Dynamic Programming"
  "Princeton University Press"
  "1957"
  "10.1515/9781400835386"
  "https://doi.org/10.1515/9781400835386"
  Attr.academicBookSource
  "Supports state-indexed finite policy comparison and continuation value; no unique scalar utility or empirical life-policy optimum is imported."
  Attr.publicAttribution

sorkinQuantumMeasureSource : Attr.AttributedSource
sorkinQuantumMeasureSource = Attr.mkDOISource
  "Rafael D. Sorkin"
  "Quantum Mechanics as Quantum Measure Theory"
  "Modern Physics Letters A"
  "1994"
  "10.1142/S021773239400294X"
  "https://doi.org/10.1142/S021773239400294X"
  Attr.academicArticleSource
  "Supports separating diagonal, pairwise-interference and higher-order residual accounting; the relational branch model is not literal quantum mechanics, a Born rule or quantum cognition."
  Attr.publicAttribution

ivyLimitedBeddingSource : Attr.AttributedSource
ivyLimitedBeddingSource = Attr.mkDOISource
  "Autumn S. Ivy; Kristen L. Brunson; Curt A. Sandman; Tallie Z. Baram"
  "Dysfunctional nurturing behavior in rat dams with limited access to nesting material: A clinically relevant model for early-life stress"
  "Neuroscience"
  "2008"
  "10.1016/j.neuroscience.2008.04.019"
  "https://doi.org/10.1016/j.neuroscience.2008.04.019"
  Attr.academicArticleSource
  "Supplies animal-model provenance for distinguishing total maternal contact from fragmented and abnormal sequencing under limited bedding; it does not identify a human caregiver or prove a human causal pathway."
  Attr.publicAttribution

davisUnpredictableSignalsSource : Attr.AttributedSource
davisUnpredictableSignalsSource = Attr.mkDOISource
  "Elysia Poggi Davis; Stephanie A. Stout; Jenny Molet; Brian Vegetabile; Laura M. Glynn; Curt A. Sandman; Kevin Heins; Hal Stern; Tallie Z. Baram"
  "Exposure to unpredictable maternal sensory signals influences cognitive development across species"
  "Proceedings of the National Academy of Sciences"
  "2017"
  "10.1073/pnas.1703444114"
  "https://doi.org/10.1073/pnas.1703444114"
  Attr.academicArticleSource
  "Supports treating temporal predictability and transition structure as variables distinct from signal quantity; no finite response trace diagnoses trauma or determines an individual developmental outcome."
  Attr.publicAttribution

feldmanSynchronySource : Attr.AttributedSource
feldmanSynchronySource = Attr.mkDOISource
  "Ruth Feldman"
  "Parent-infant synchrony and the construction of shared timing; physiological precursors, developmental outcomes, and risk conditions"
  "Journal of Child Psychology and Psychiatry"
  "2007"
  "10.1111/j.1469-7610.2006.01701.x"
  "https://doi.org/10.1111/j.1469-7610.2006.01701.x"
  Attr.academicArticleSource
  "Supports shared timing, contingency and synchrony as relational dimensions separate from raw attention volume; it does not define a universal optimum or establish a particular family finding."
  Attr.publicAttribution

tronickContradictoryMessagesSource : Attr.AttributedSource
tronickContradictoryMessagesSource = Attr.mkDOISource
  "Edward Tronick; Heidi Als; Lauren Adamson; Susan Wise; T. Berry Brazelton"
  "The infant's response to entrapment between contradictory messages in face-to-face interaction"
  "Journal of the American Academy of Child Psychiatry"
  "1978"
  "10.1016/S0002-7138(09)62273-1"
  "https://doi.org/10.1016/S0002-7138(09)62273-1"
  Attr.academicArticleSource
  "Supports mismatch, contradictory signalling and repair-sensitive face-to-face interaction as developmental provenance; no laboratory paradigm is equated with an adult family episode."
  Attr.publicAttribution

barkleyInhibitionSource : Attr.AttributedSource
barkleyInhibitionSource = Attr.mkDOISource
  "Russell A. Barkley"
  "Behavioral inhibition, sustained attention, and executive functions: Constructing a unifying theory of ADHD"
  "Psychological Bulletin"
  "1997"
  "10.1037/0033-2909.121.1.65"
  "https://doi.org/10.1037/0033-2909.121.1.65"
  Attr.academicArticleSource
  "Supports inhibition, working-memory and executive-control mechanisms as candidate explanations for interruption or rapid response; explanation is not exemption, diagnosis of a person or proof that repair is impossible."
  Attr.publicAttribution

canonicalRelationalSources : List Attr.AttributedSource
canonicalRelationalSources =
  freudPsychopathologySource
  ∷ freudDreamSource
  ∷ leveltLexicalAccessSource
  ∷ harleyMacAndrewSource
  ∷ harseyFreydSource
  ∷ dutaSheafHypergraphSource
  ∷ lasalleAttractorSource
  ∷ aubinViabilitySource
  ∷ bellmanDynamicProgrammingSource
  ∷ sorkinQuantumMeasureSource
  ∷ ivyLimitedBeddingSource
  ∷ davisUnpredictableSignalsSource
  ∷ feldmanSynchronySource
  ∷ tronickContradictoryMessagesSource
  ∷ barkleyInhibitionSource
  ∷ []

canonicalRelationalSourceAtlas : Attr.AttributedSourceAtlas
canonicalRelationalSourceAtlas = Attr.mkSourceAtlas
  "relational shared-state, developmental attunement and branch-selection sources"
  "DASHI.Reasoning.RelationalFormalismSourceAtlas"
  canonicalRelationalSources
  "Bounded provenance for lexical intrusion, defensive reversal, typed hyperfabric, PNF-preserving relational state, attractor/viability selection, branch interference, developmental signal sequencing, synchrony and ADHD candidate mechanisms."

canonicalRelationalSourceCount : Nat
canonicalRelationalSourceCount = Attr.sourceCount canonicalRelationalSources

canonicalRelationalSourceCountIsFifteen :
  canonicalRelationalSourceCount ≡ 15
canonicalRelationalSourceCountIsFifteen = refl

canonicalRelationalSourceAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority canonicalRelationalSourceAtlas ≡ false
canonicalRelationalSourceAtlasDoesNotCreateAuthority =
  Attr.atlasCreatesAuthorityIsFalse canonicalRelationalSourceAtlas
