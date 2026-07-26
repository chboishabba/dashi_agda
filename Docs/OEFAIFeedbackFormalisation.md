# OEF AI Feedback Formalisation

## Source

**Paper:** *Making sense of student feedback and engagement using artificial intelligence*

**Authors:** Christopher Dann, Petrea Redmond, Melissa Fanshawe, Alice Brown, Seyum Getenet, Thanveer Shaik, Xiaohui Tao, Linda Galligan, and Yan Li.

**Journal:** *Australasian Journal of Educational Technology*, 40(3), 58–76 (2024).

**DOI:** `10.14742/ajet.8903`

**Institutional setting:** University of Southern Queensland, Toowoomba, Queensland, Australia.

## Source-bounded reading

The paper is retained as a successful MVP / feasibility study. It demonstrates that manually labelled student feedback can train an NLP/deep-learning prototype to classify later feedback using the Online Engagement Framework and visualise aggregate signals at faculty, school, programme, and course levels.

The source reports:

- 383 manually labelled training feedback sentiments;
- 311 later testing feedback sentiments;
- 76% overall reported accuracy;
- category-specific precision, F1, recall, and balanced accuracy;
- uneven training counts and performance across the five engagement elements;
- open issues around label balance, annotation bias, ambiguity, sarcasm, domain-specific language, data quality, and single-institution scope.

The formalisation does not replace the paper’s claim with a stronger one. It preserves the MVP contribution while making its promotion boundaries explicit.

## Five OEF engagement fibres

The five elements are represented as overlapping fibres rather than mutually exclusive student essences:

1. **Social engagement** — community, belonging, relationships, and trust.
2. **Cognitive engagement** — critical thought, metacognition, integration, justification, deep disciplinary understanding, and distributed expertise.
3. **Behavioural engagement** — academic skills, opportunities and challenges, multidisciplinary skills, agency, online norms, and peer support.
4. **Collaborative engagement** — learning with peers, faculty relationships, institutional opportunities, and professional networks.
5. **Emotional engagement** — expectations, assumptions, motivation, and commitment to learning.

A comment about learning through online forum discussion may inhabit cognitive, behavioural, collaborative, and social fibres simultaneously. Overlap is therefore retained as signal rather than treated as classification failure.

## Formal pipeline

```text
student ecology / feedback hypervoxel
  → voluntary end-of-course textual projection
  → human OEF interpretation and labels
  → cleaned labelled training surface
  → model-predicted OEF bundle and sentiment proxy
  → aggregate visualisation
  → contextual human review
  → residual hypothesis
  → small, reversible, agency-safe pedagogical +1 candidate
  → evidence return
```

The machine scales a human coding frame. It does not remove interpretation or directly observe engagement truth.

## Main residual vector

The implementation distinguishes:

- sampling residual;
- non-response residual;
- annotation residual;
- classification residual;
- semantic residual;
- multi-label compression residual;
- ecological residual;
- intersectional residual;
- temporal residual;
- pedagogical residual.

These residuals interact and are not collapsed into the single reported accuracy number.

## Hard boundaries

```text
AI classification ≠ student meaning
survey response ≠ complete student voice
respondents ≠ full cohort
no response ≠ neutral / satisfied / disengaged
missing classification ≠ missing engagement
sentiment proxy ≠ wellbeing truth
aggregate chart ≠ individual student
high aggregate engagement ≠ equitable engagement
end-point feedback ≠ longitudinal trajectory
later-semester transfer ≠ causal redesign effect
OEF categories ≠ whole student ecology
dashboard output ≠ pedagogical authority
candidate +1 ≠ automatic intervention
```

## Intersectional and privacy lift

Axis-aware analysis is permitted only under:

- opt-in consent;
- privacy protection;
- minimum-cell governance;
- no reidentification;
- no deficit promotion;
- local contextual review.

Group differences remain aggregate candidate surfaces and cannot be projected into individual diagnosis or deficit ontology.

## Longitudinal lift

The paper’s training-semester to later-testing-semester structure is retained as a weak transfer surface. Stronger trajectory or intervention claims require repeated measurements, comparable cohorts, implementation receipts, student interpretation, confound audit, and replication.

## Pedagogical +1 routing

AI output may route attention toward possible support handles, including clearer navigation, explicit expectations, peer connection, teacher presence, reduced overload, or chosen human check-ins. A handle becomes an admissible `+1` only after student choice, contextual fit, low burden, non-shaming, non-surveillance, human review, opt-out, and measurable evidence-return gates pass.

## Modules

- `DASHI/Biology/OEFMultiFibreFeedbackHyperfabric.agda`
- `DASHI/Biology/OEFOverlapAnalytics.agda`
- `DASHI/Biology/FeedbackNonResponseGovernance.agda`
- `DASHI/Biology/IntersectionalFeedbackPrivacyBoundary.agda`
- `DASHI/Biology/LongitudinalEngagementTrajectory.agda`
- `DASHI/Biology/PedagogicalJPlusOneRouting.agda`
- `DASHI/Biology/OEFAIFeedbackFormalisation.agda`

The aggregate module also binds the new source-specific layer to the existing `StudentEngagementEvidenceBridge` and `EducationBodyMemoryBridge` formalisms.
