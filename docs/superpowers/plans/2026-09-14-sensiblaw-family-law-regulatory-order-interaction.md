# SensibLaw Family-Law Regulatory and Order Interaction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add source-bounded Australian family-law regulatory-status and order-interaction owners without collapsing enabling legislation, operative subordinate law, family-violence orders, parenting orders, information sharing, child-protection jurisdiction, or case application.

**Architecture:** Keep two independent owners. `AustralianFamilyReportWriterRegulatoryImplementationExact` records Part IIIAA / s 11K enactment and the current bounded search state of the Family Law Regulations 2024. `AustralianFamilyLawOrderInteractionExact` models Division 11 ss 68P-68T plus Subdivision DA information-sharing as distinct statutory mechanisms. Both reuse `AttributedSourceCore` and retain negative-search and authority non-promotion firewalls.

**Tech Stack:** Agda, existing DASHI Core/Law owners, Federal Register of Legislation and Attorney-General's Department primary sources.

**Spec:** continuation of PR #911 roadmap and its source/authority firewalls.

## Global Constraints

- Citation/imported source never imports proof or legal authority.
- Enabling power != operative regulation.
- Negative search != proof of nonexistence.
- Commonwealth supremacy principle != complete operational order-interaction rule.
- Information existence != requested != received != admitted != correctly weighted.
- Child-protection law/jurisdiction remains separately typed from family-law proceedings.
- No case-specific legal conclusion or breach finding is created by these owners.

---

### Task 1: s 11K implementation-status owner

**Files:**
- Create: `DASHI/Law/AustralianFamilyReportWriterRegulatoryImplementationRegression.agda`
- Create: `DASHI/Law/AustralianFamilyReportWriterRegulatoryImplementationExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`
- Produces: source atlas, bounded search receipt, regulatory-layer status, WrongType firewalls.

- [ ] Write regression importing the absent production owner and requiring enabling-power / operative-regime / negative-search distinctions.
- [ ] Verify exact branch lookup of production owner returns 404.
- [ ] Add minimal source-bound production owner.
- [ ] Preserve `implementingProvisionLocated = false` and `absenceOfImplementingProvisionProved = false` as separate coordinates.
- [ ] Commit.

### Task 2: family-law order interaction owner

**Files:**
- Create: `DASHI/Law/AustralianFamilyLawOrderInteractionRegression.agda`
- Create: `DASHI/Law/AustralianFamilyLawOrderInteractionExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`
- Produces: typed mechanisms for ss 68P-68T, Subdivision DA information sharing, and child-protection separation.

- [ ] Write regression requiring the federal-order / family-violence-order distinction and statutory reconciliation mechanisms.
- [ ] Verify exact branch lookup of production owner returns 404.
- [ ] Add minimal production owner with `68Q` inconsistency effect and `68R` state/territory court variation power kept distinct.
- [ ] Add information-sharing stage lattice and firewalls.
- [ ] Add child-protection-jurisdiction non-collapse boundary.
- [ ] Commit.

### Task 3: aggregate / Pareto wiring

**Files:**
- Modify: `DASHI/Law/Everything.agda`
- Modify: PR #911 narrative.

**Interfaces:**
- Consumes: Tasks 1-2.
- Produces: aggregate imports and explicit next acquisition frontier.

- [ ] Export both production owners through `DASHI.Law.Everything`.
- [ ] Update PR roadmap with source-paid vs unpaid coordinates.
- [ ] Preserve certification as a separate status and do not block further source implementation on CI.
