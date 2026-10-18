# Digital-ESD open knowledge commons roadmap

Status: design/source-integration note. This document does not establish educational effectiveness or final manuscript inclusion.

## Core shift

The open-source/open-education lane should not be represented merely as another infrastructure feature. The stronger candidate architecture is a shared knowledge commons in which learners, teachers, parents/families, curriculum stewards and wider communities can inspect, discuss, revise, translate, adapt and contribute while provenance and role remain explicit.

```text
one-way content delivery
!= shared knowledge commons
```

The user-supplied design intent is wiki/forum-like collaboration, multimodal presentation, multilingual adaptation, and external concept/entity linking (including Wikidata/QID-style identity) over a versioned public knowledge substrate.

## Primary source anchors

The source-bounded normative/design anchors currently retained are:

1. UNESCO, *Recommendation on Open Educational Resources (OER)* (2019): open licensing, no-cost access, reuse, repurposing, adaptation, redistribution, translation, accessible formats, multilingual/local-language resources, stakeholder capacity, co-creation and international collaboration.
2. UNESCO-UNICEF-ITU, *Charter for Public Digital Learning Platforms* (2026): public digital learning platforms as digital commons; multilingual support, disability accessibility, low-cost-device/limited-connectivity support, open standards, reuse licensing and interoperability.
3. UNICEF, *Accessible Digital Textbooks for All* (2026): disability-inclusive, flexible digital materials and systems-oriented accessibility.
4. CAST, *Universal Design for Learning Guidelines 3.0* (2024): learner agency, collective learning, multimodal representation, multilinguality, assistive technology compatibility and active challenge to exclusionary practices.

These sources constrain a candidate architecture. They do not prove that a named platform or curriculum is inclusive, effective or sustainable.

## DASHI repository fixture

GitHub repository metadata observed 2026-09-17 records `chboishabba/dashi_agda` as public, with issues and wiki enabled, forks present, and repository `license = null`.

Therefore:

```text
publicly readable / technically forkable
!= explicit open-source or OER reuse licence
```

If DASHI is intended to function as a reusable global curriculum commons, explicit licensing is a concrete unpaid implementation/governance coordinate. Public visibility alone is not sufficient legal permission to reuse, modify and redistribute.

## Shared stakeholder roles

Current candidate shared roles:

- learner/student;
- teacher/educator;
- parent/family;
- curriculum steward/designer;
- wider community contributor.

A role grants no universal authority by itself. Collaboration should retain role, provenance, source identity, revision history, review state and consumer-specific authority.

```text
contribution opportunity
!= contribution uptake
!= curriculum authority
!= epistemic correctness
```

The existing `StudentVoiceEpistemicAgencyBridge` remains authoritative for learner participation: survey capture or feedback alone is not voice/agency; learners may instead shape questions, contest coding frames, co-interpret, co-design and review returned evidence.

## QID / Wiki-style identity

A shared curriculum can use Wikidata/QID-style external identities to make concepts cross-language and machine-addressable, but the existing repository identity boundary remains:

```text
QID presence
!= source identity
!= publication identity
!= semantic truth
!= curriculum authority
```

Entity linking is navigation/addressability. It cannot substitute for source attribution, claim evidence or local interpretation.

## Multilingual and multimodal curriculum

The target should distinguish:

```text
translation available
!= semantic equivalence verified

multimodal presentation
!= realised accessibility

open licence
!= disability access
```

Useful implementation coordinates include local/indigenous language adaptation, captions/sign language/audio description where relevant, text/audio/image/video/diagram/interactive alternatives, assistive-technology compatibility, low-connectivity/offline paths, and versioned source files that can actually be adapted.

## "Who is not at the table?"

The canonical `DigitalESDStudyIntersectionalAbsenceAuditExact` remains mandatory beside the commons layer. An open contribution interface can still systematically exclude participants through disability access, language, connectivity, device cost, time, safety, disclosure requirements, platform literacy, institutional power or category design.

```text
open contribution interface
!= inclusive participation
```

The current 11-question absence audit should therefore apply not only to studies but to the curriculum/platform governance itself: who can read, who can edit, who can review, whose edits are accepted, who must disclose needs, who lacks connectivity, who bears moderation labour, who has merge authority, and whose future options are changed.

## Material/environmental substrate

The canonical `DigitalESDMaterialEnvironmentalSubstrateExact` also remains mandatory. Open source and OER can improve reuse/interoperability and potentially reduce duplication, but openness does not dematerialise computing.

```text
open source / OER
!= low environmental burden
```

The commons still depends on semiconductor fabrication, devices, networking/data centres, electricity, water, materials, maintenance, repair, replacement and end-of-life pathways. TSMC/IEA/e-waste/LCA evidence stays source-bounded and cannot manufacture the footprint of a named educational deployment.

## Candidate architecture

```text
OpenDigitalESDCommons =
  open/licensed knowledge objects
  x provenance/version history
  x shared stakeholder collaboration
  x multilingual adaptation
  x multimodal/accessibility support
  x QID/external-entity addressability
  x intersectional absence audit
  x material/environmental lifecycle audit
  x evidence/claim-ceiling discipline
```

No factor pays another automatically.

## Next implementation frontier

1. choose and document explicit repository/content licensing if the intended reuse rights are to be real rather than implied;
2. distinguish code licence, educational-content licence and third-party/source-material rights where necessary;
3. define contribution/review/merge roles for learner, teacher, parent/family, curriculum steward and community contributors;
4. define multilingual/multimodal/accessibility acceptance tests;
5. define QID/source-attribution linking conventions without truth promotion;
6. run the existing intersectional absence and material/environmental audits against the platform/curriculum itself;
7. treat any educational deployment with students/colleagues as an experiment/evaluation whose claims remain bounded by its design, sample, uncertainty and PNF predicate receipts.
