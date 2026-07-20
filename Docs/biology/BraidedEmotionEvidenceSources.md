# Braided emotion evidence source registry

## Status

This document supplies source provenance for the bounded evidence rows in
`DASHI.Biology.BraidedEmotionEvidenceRegistry` and the structured receipts in
`DASHI.Biology.BraidedEmotionEvidenceProvenance`.

The Agda rows are not proofs that a disputed emotion theory is true. They record
which kinds of observations motivate a claim, the explanatory scale at which the
claim is used, what would count against an over-strong reading, and whether a
source supports, qualifies, conflicts with, or underdetermines a claim.

## Stable citation keys

The formal source records use compact citation keys. Full bibliographic metadata
remains in documentation rather than being reproduced inside Agda terms.

- `Barrett2017TheoryConstructedEmotion` — Lisa Feldman Barrett, “The theory of
  constructed emotion: an active inference account of interoception and
  categorization,” *Social Cognitive and Affective Neuroscience* 12(1), 2017.
- `ElfenbeinAmbady2002EmotionRecognitionMetaAnalysis` — Hillary Anger Elfenbein
  and Nalini Ambady, “On the universality and cultural specificity of emotion
  recognition: a meta-analysis,” *Psychological Bulletin* 128(2), 2002.
- `Gendron2015CultureEmotionPerception` — work by Maria Gendron and colleagues on
  cultural and conceptual variation in emotion perception. This key refers to
  the source family used to qualify universal-category readings; source-specific
  rows should be split further before quantitative promotion.
- `MenonUddin2010SalienceNetwork` — Vinod Menon and Lucina Q. Uddin, “Saliency,
  switching, attention and control: a network model of insula function,” *Brain
  Structure and Function* 214, 2010.
- `TugadeFredrickson2004EmotionalGranularity` — Michele M. Tugade, Barbara L.
  Fredrickson, and Lisa Feldman Barrett, “Psychological resilience and positive
  emotional granularity,” *Journal of Personality* 72(6), 2004.
- `Kimmerer2013BraidingSweetgrass` — Robin Wall Kimmerer, *Braiding Sweetgrass:
  Indigenous Wisdom, Scientific Knowledge, and the Teachings of Plants*, 2013.

The Kimmerer key records provenance for a normative and relational influence. It
is not an empirical-neuroscience citation, a permission claim, or evidence that
DASHI formalises Indigenous knowledge.

## Dialectical evidence relations

`EvidenceRelation` has four constructors:

- `supports` — the source supplies positive warrant for a bounded claim;
- `qualifies` — the source narrows the claim or blocks a stronger reading;
- `conflictsWith` — the source provides materially contrary evidence;
- `underdetermines` — the source is compatible with multiple theories and does
  not select a unique mechanism or ontology.

The same source family may support one level of description while qualifying a
stronger one. Cross-cultural recognition results, for example, may support
recurrent affective structure while task and cultural variation qualify strong
claims of context-independent natural kinds.

## Source families

### Cross-cultural regularity and variation

Relevant traditions include work by Paul Ekman and collaborators on recurring
expressive recognition, James Russell on conceptual and methodological limits,
Hillary Elfenbein and Nalini Ambady on cultural in-group advantage, and later
open-ended and field-based studies showing substantial category and task
variation.

Registry consequence: recurring regularities and cultural variation are held
together. Neither perfect universal natural kinds nor arbitrary unconstrained
categories are promoted.

### Construction, concepts, and language

Relevant traditions include Lisa Feldman Barrett's theory of constructed
emotion, work by Kristen Lindquist and colleagues on conceptual knowledge and
language, and research on semantic interference, category learning, affect
labelling, and emotional granularity.

Registry consequence: concepts and words may alter differentiation, attention,
report, memory, and regulation, but language is not treated as having unlimited
power to manufacture any episode from any bodily and worldly condition.

### Appraisal and action readiness

Relevant traditions include Nico Frijda's action-readiness account and appraisal
work associated with Klaus Scherer, Richard Lazarus, Phoebe Ellsworth, Craig
Smith, and others.

Registry consequence: goal relevance, agency, control, norm relation, and action
preparation are important strands without becoming the whole episode.

### Interoception and predictive processing

Relevant traditions include interoceptive and active-inference work associated
with Anil Seth, Karl Friston, Hugo Critchley, Sarah Garfinkel, Lisa Feldman
Barrett, and collaborators.

Registry consequence: prediction, precision, autonomic regulation, and
prediction-error language are marked as mechanistic candidates and
model-dependent interpretations, not as a completed total theory of emotion.

### Neural measurement and reverse inference

Relevant traditions include distributed-network, lesion, electrophysiological,
connectivity, and multivariate decoding studies, together with critiques of
reverse inference and person-independent mind reading.

Registry consequence: fMRI, EEG, connectivity, and decoded patterns remain
measurement proxies. They do not by themselves recover the complete lived,
relational, cultural, or ethical meaning of an episode.

### Relational, cultural, and phenomenological inquiry

Relevant traditions include developmental, interpersonal, anthropological,
enactive, ecological, phenomenological, feminist, and critical approaches to
emotion.

Registry consequence: relation, institution, history, land, culture, and power
may be constitutive of an episode's meaning while remaining distinct from claims
about subpersonal neural implementation.

### Reciprocity, obligation, and provenance

The braid and provenance architecture is materially inspired by Robin Wall
Kimmerer, especially *Braiding Sweetgrass*. See
`Docs/acknowledgements/RobinWallKimmerer.md`.

Registry consequence: obligation-bearing knowing is explicitly marked as a
normative and relational commitment rather than an empirical neuroscience
result. DASHI's “dialectical braid” is a DASHI extension and is not attributed to
Kimmerer as her terminology.

## Promotion boundary

No row or structured receipt grants:

- theorem authority to an empirical association;
- causal authority to a measurement proxy;
- diagnosis or treatment authority;
- cultural authority or permission to represent Indigenous knowledge;
- a global victory declaration for any one emotion theory.

Future refinements should add source-specific effect estimates, replication
status, contrary findings, and narrower population/task scopes before any
stronger evidential promotion.
