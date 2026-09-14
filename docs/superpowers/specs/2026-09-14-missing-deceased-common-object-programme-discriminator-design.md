# Missing/Deceased Common Object / Programme Discriminator Design

## Purpose

Add an object-first causal-linking layer above the existing twenty-scientist science/custody BIDI. The new layer must test whether the observed event cluster is better explained by independent events and roster selection, broad strategic-sector exposure, one or more shared programmes/objects with ordinary succession/disruption, or coordinated targeting related to a shared programme.

The layer must not encode related disappearance/death as a fact. It must preserve the repo's existing firewalls: technical adjacency does not create a common engineering stack; geography does not create common cause; programme identity does not create targeting; source repetition does not create independent corroboration.

## Core hypothesis family

```text
H0 = independent events + roster/media selection
H1 = shared strategic-sector exposure, no common programme
H2 = shared programme/object with ordinary succession/disruption
H3 = coordinated targeting related to that programme/object
```

Every new receipt is evaluated for which hypotheses it supports, weakens, or leaves unchanged. H3 requires operational evidence beyond timing, technical adjacency, geography, or strategic plausibility.

## Object-first graph

```text
CandidateProgramme
  -> CandidateObject*
  -> RequiredCapability*
  -> PersonCapabilityReceipt*
  -> CrossPersonProgrammeReceipt*
  -> EventChronologyReceipt*
  -> HypothesisDiscrimination
```

Programmes may contain multiple objects. A candidate object need not consume all twenty science fibres; forcing all twenty into one literal machine is prohibited.

## Initial candidate object/programme classes

1. **Long-duration autonomous extreme-environment aerospace/space platform**
   - plausible ordinary-engineering consumer of plasma/environment modelling, fission-power I&C, high-temperature/oxygen-service/structural materials, fault-tolerant placement, hardware verification, autonomy, space weather, high-speed flow control, molecular diagnostics, remote astronomy/planetary inference, and data-security governance.
   - serves as a strong ordinary-engineering null/control.

2. **High-energy experimental/test infrastructure**
   - plausible consumer of accelerator/radiographic engineering, controls, fault tolerance, advanced materials, molecular diagnostics, hardware verification, data governance, precision-force testing, and mechanism discrimination.
   - may represent a facility family rather than one vehicle.

3. **Advanced propulsion / anomalous-field research testbed**
   - speculative candidate centred on Ning Li/Amy Eskridge and bounded supporting capabilities.
   - must retain Ning's negative/static and rotating test constraints.
   - capability fit cannot promote operational exotic propulsion.

4. **Strategic R&D portfolio**
   - programme contains multiple interacting objects and can explain cross-domain breadth without requiring a single integrated machine.
   - person-to-object membership requires exact work/custody evidence.

## Required evidence classes

### Capability-fit evidence

Shows that a person's source-backed science could satisfy a declared object requirement. This is design-space compatibility only.

### Cross-person programme/object evidence

At least one literal cross-person receipt is required before a candidate can be promoted beyond capability fit. Preferred receipts include:

- common programme/contract/grant identifier;
- shared requirements/specification;
- interface-control document;
- procurement or subcontract chain;
- shared apparatus/facility identifier;
- dated handoff/custody transfer;
- common work package;
- same-object source naming two or more relevant participants/components.

### Event chronology evidence

Events must be typed, not collapsed:

- disappearance;
- death, cause/manner state where known;
- homicide/accident/illness where source-backed;
- retirement/separation;
- stale institutional surface;
- posthumous publication;
- ordinary role transition/succession.

A temporal-concentration analysis must separate event type, age/exposure window, publication lag and source-discovery lag.

### Coordinated-targeting evidence

H3 cannot be promoted without operational evidence such as:

- pre-event common tasking;
- common security incident/case identifier;
- coordinated access revocation;
- unusual workstation/records action across cases;
- common adversary/counterparty linked to the same programme object;
- cross-case investigative linkage predating public/media aggregation;
- common operational action against multiple relevant people.

## Candidate scoring

The object-first layer should rank candidate programmes/objects by a conservative score tuple, not a single scalar:

```text
(explainedCapabilityCount,
 literalCrossPersonReceiptCount,
 inventedInterfaceCount,
 eventAlignmentCount,
 alternativeExplanationDebt,
 targetingEvidenceCount)
```

No candidate wins merely by covering many science fibres. High capability coverage with zero cross-person receipts remains a design-space hypothesis.

## Temporal concentration

Add a typed event-time surface that can carry exact dates/ranges and event classes. The first version may record the statistic contract and current known event coordinates without claiming a population-level p-value until an appropriate comparison population is sourced.

Required distinctions:

```text
calendar proximity != causal proximity
publication date != work date
death date != disappearance date
posthumous publication != post-loss participation
stale webpage date != succession date
```

## Reuse

Reuse existing owners rather than creating parallel theories:

- `MissingDeceasedUAPAdversarialClaimDiscriminatorExact`
- `MissingDeceasedSouthwestGeographyDiscriminatorExact`
- `MissingDeceasedTwentyScientistScienceCapabilityBidiExact`
- `MissingDeceasedTwentyScientistScienceExecutionKernelExact`
- `MissingDeceasedStrategicRoleCapabilityFibreExact`
- existing attribution/snowball/same-object machinery.

## New owner

`DASHI/Culture/MissingDeceasedCommonObjectProgrammeDiscriminatorExact.agda`

Core records/types:

- `HypothesisClass = H0 | H1 | H2 | H3`
- `CandidateProgramme`
- `CandidateObject`
- `RequiredCapability`
- `PersonCapabilityReceipt`
- `CrossPersonProgrammeReceipt`
- `EventClass`
- `EventChronologyReceipt`
- `HypothesisDiscriminationReceipt`

Initial candidates are the four classes above. They begin unpromoted unless existing literal receipts already pay the relevant edge.

## Firewalls

The owner must export exact booleans/propositions equivalent to:

```text
capabilityFitPaysProgrammeIdentity = false
temporalClusterPaysCoordination = false
programmeIdentityPaysTargeting = false
geographyPaysCommonCause = false
technicalAdjacencyPaysCommonProgramme = false
commonObjectRequiresLiteralCrossPersonReceipt = true
coordinatedTargetingRequiresOperationalEvidence = true
portfolioObjectMembershipRequiresSameObjectReceipt = true
sourceRepetitionPaysIndependentCorroboration = false
```

## First Pareto search

After the owner exists, the first investigation tranche should search for literal cross-person objects rather than broad thematic similarity:

1. common programme/contract/grant identifiers spanning two or more scientists;
2. shared facility/apparatus identifiers;
3. procurement/interface-control/work-package documents;
4. pre-event handoff/custody/succession records;
5. cross-case security/investigative identifiers predating media aggregation.

The search must include negative controls and matched ordinary explanations.

## Certification boundary

Source-written structure is not Agda/kernel certification. TDD contract lands first. No GREEN or typecheck claim without a runnable exact-head receipt.
