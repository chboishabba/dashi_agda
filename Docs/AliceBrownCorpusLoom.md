# Alice Brown Education Corpus Loom

## Purpose

This document records a source-bound cross-paper synthesis. Each paper remains a separate evidence fibre. The repository distinguishes:

1. claims supported by a source paper;
2. cross-paper inferences proposed by the corpus loom;
3. DASHI formal extensions;
4. hypotheses requiring new empirical work.

The loom does not claim that any author or paper states the complete combined theory.

## Source registry

### 1. AI-assisted student-feedback classification

**Title:** *Making sense of student feedback and engagement using artificial intelligence*

**Authors:** Christopher Dann; Petrea Redmond; Melissa Fanshawe; Alice Brown; Seyum Getenet; Thanveer Shaik; Xiaohui Tao; Linda Galligan; Yan Li.

**Journal:** *Australasian Journal of Educational Technology* 40(3), 58-76 (2024).

**DOI:** `10.14742/ajet.8903`

**Source contribution:** A feasibility/MVP result showing that manually OEF-labelled feedback can train an NLP/deep-learning classification and aggregate-visualisation prototype.

**Boundary:** Classification remains a proxy, not student meaning, complete voice, equity, individual truth, causal redesign effect, or pedagogical authority.

### 2. Student voice and epistemic agency

**Title:** *Repositioning Student Voice and Agency: A Call for the Epistemic Expansion of Scholarship of Teaching and Learning Inquiry*

**Authors:** Alice Brown; Megan Kimber.

**Journal:** *Active Learning in Higher Education* 27(2), 253-264 (2026).

**DOI:** `10.1177/14697874261426374`

**Source contribution:** Critiques extractive SoTL practices that position students as passive data sources and calls for students to contribute as domain experts and knowledge producers.

**Cross-paper use:** Supplies epistemic-participation gates for the AI-feedback pipeline: students may shape questions, contest coding frames, co-interpret outputs, choose or reject support candidates, and review returned evidence.

### 3. Student-identified online-learning support strategies

**Title:** *Supporting online learning in teacher education: student-identified strategies and social constructivist implications*

**Authors:** Seyum Getenet; Katie Burke; Melissa Fanshawe; Alice Brown.

**Journal:** *Distance Education* (online first, 2026).

**DOI:** `10.1080/01587919.2026.2669288`

**Source contribution:** Analysis of 584 pre-service-teacher responses identified five themes:

- learner autonomy and flexibility;
- accessible and centralised resources;
- meaningful interaction with peers and teachers;
- self-organisation;
- guided scaffolding.

**Cross-paper use:** These become optional, many-to-many pedagogical `+1` candidate families for OEF residuals, not universal prescriptions.

### 4. Custodianship of an ecology of data

**Title:** *Custodians of an ecology of data: Foundational theory and practice for data analysis in a complex world*

**Authors:** Roxanne Finn; Alice Brown.

**Journal:** *Qualitative Research* 25(1), 110-129 (2025).

**DOI:** `10.1177/14687941241234293`

**Source contribution:** Develops an eco-behavioural, person-place co-constituted approach to qualitative analysis through five responsibilities:

- map system edges and intersections;
- analyse affordances of place;
- attend to minutiae and effort after meaning/value;
- consider flows of value;
- learn with and curate data pedagogically.

**Cross-paper use:** Restores ecological context hidden by a flat feedback-classification surface. A comment becomes an event within a person-place hyperfabric rather than a context-free semantic object.

### 5. Parental allyship conceptual lens

**Title:** *Parental Allyship for Children With Dyslexia: A Conceptual Lens on Disability Experience*

**Authors:** Rachel Leslie; Alice Brown; Ellen Larsen.

**Journal:** *Learning Disability Quarterly* 48(1), 3-12 (2025).

**DOI:** `10.1177/07319487241251730`

**Source contribution:** Extends disability-experience analysis to parent allies through primary, vicarious, and primary-adjacent experience.

**Boundary:** Parent allyship does not replace the child's primary experience, identity, or voice.

### 6. Advocacy and allyship distinction

**Title:** *It is more than the average parent goes through: using the experiences of Australian parents of dyslexic children to draw a distinction between advocacy and allyship*

**Authors:** Rachel Leslie; Ellen Larsen; Melissa Fanshawe; Alice Brown.

**Journal:** *Australian Journal of Learning Difficulties* 29(1), 53-74 (2024).

**DOI:** `10.1080/19404158.2024.2342523`

**Source contribution:** Interviews with ten Australian parents support a situated distinction between routine advocacy and the additional responsibilities and disability-adjacent experiences of parental allyship.

**Boundary:** The qualitative sample does not establish prevalence or universal parent trajectories.

### 7. Parent-school partnership barriers

**Title:** *The Perceptions Parents of Dyslexic Children Have on Barriers to Meaningful Parent-School Partnerships in Australia*

**Authors:** Rachel Leslie; Melissa Fanshawe; Ellen Larsen; Alice Brown.

**Journal:** *Exceptionality* 33(1), 40-58 (2025).

**DOI:** `10.1080/09362835.2024.2389081`

**Source contribution:** Reports parent-perceived interpersonal and systemic barriers, including cases in which parent expertise was not welcomed by schools.

**Boundary:** Parent perceptions remain valid situated evidence but do not alone prove institutional intent or every participant's state.

## Corpus-level developmental braid

```text
OEF engagement vocabulary
  -> scalable feedback classification
  -> ecology/person-place context restoration
  -> student epistemic participation
  -> student-identified support candidate families
  -> plural student/parent/teacher/researcher/institution/model observers
  -> co-designed local enactment
  -> evidence return and recharting
```

This sequence is a DASHI synthesis, not a quotation or single-paper claim.

## Shared interpretive-coding architecture

```text
source material
  + coding frame
  + situated interpreter
  -> categorised-meaning candidate
```

Manual thematic analysis, qualitative content analysis and supervised machine classification differ in where interpretation is located and how it is compiled. None produces semantic identity without uncertainty, reflexivity, missingness and contestability receipts.

## Multi-observer boundary

```text
student projection != parent projection
parent projection != teacher projection
teacher projection != institutional record
researcher interpretation != participant meaning
model prediction != whole educational ecology
```

The corpus loom preserves these as local sections of a larger hyperfabric.

## Cross-paper research hypotheses

The current corpus supports formulating, but does not yet empirically establish:

1. whether student co-design changes OEF coding frames and downstream dashboard interpretations;
2. whether overlapping OEF fibres predict student-valued support combinations better than exclusive categories;
3. whether ecology-of-data custodianship improves context retention and participant contestability in AI-assisted analysis;
4. whether student-selected support handles reduce local engagement residuals over repeated offerings;
5. how student, parent, teacher and institutional observer surfaces disagree and can be glued without erasure.

## Implemented modules

- `DASHI/Biology/EducationCorpusSourceRegistry.agda`
- `DASHI/Biology/StudentVoiceEpistemicAgencyBridge.agda`
- `DASHI/Biology/StudentIdentifiedSupportStrategiesBridge.agda`
- `DASHI/Biology/EcologyOfDataHyperfabricBridge.agda`
- `DASHI/Biology/ParentAllyshipMultiObserverBridge.agda`
- `DASHI/Biology/InterpretiveCodingSystem.agda`
- `DASHI/Biology/CrossPaperDialecticalDevelopment.agda`
- `DASHI/Biology/AliceBrownCorpusLoom.agda`

The aggregate composes the new corpus layer with the existing OEF/AI, student-engagement, education/body-memory, residual, hyperfabric, governance and pedagogical `+1` surfaces.
