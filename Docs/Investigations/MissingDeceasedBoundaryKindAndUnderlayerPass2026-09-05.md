# Missing/deceased scientist boundary-kind and underlayer pass — 2026-09-05

## Purpose

The open-science / knowledge-release lane is now split by **boundary kind**. A private-to-public transition is not treated as a single feature.

Current boundary kinds:

- ordinary patent confidentiality;
- contractual proprietary boundary;
- controlled-government data;
- export-controlled boundary;
- classified national-security boundary;
- internal institutional boundary;
- discretionary disclosure boundary.

The corresponding firewall is:

`patent publication != declassification != proprietary-period expiry != export-control release != discretionary disclosure`.

## Reza / Jacinto patent: exact routine boundary closed

US patent application `09/954,835`, *Burn-resistant and high tensile strength metal alloys*, was filed 2001-09-18 and published as `US20030053926A1` on 2003-03-20. USPTO/35 U.S.C. 122 provides the relevant application-confidentiality -> publication regime.

Thus the same USPTO application record closes:

`confidential application -> public application publication`.

This is a genuine same-object B witness, but its kind is **ordinary patent confidentiality**. It does not establish classified declassification, export-control release, all underlying test data becoming public, or a person-specific discretionary release decision.

This is important negative pressure against raw boundary-counting: many inventors can satisfy B merely through ordinary patent publication.

## POAMS: non-routine boundary documented, completed all-layer transfer not closed

NASA/TM-20205010911 documents a Space Act proprietary period and later public technical memorandum. The report also says V5 hardware/data remained in Quantum Machines possession. The resulting topology is:

- contractual proprietary boundary: documented;
- governance restriction later ended: documented;
- public technical report: documented;
- public release of complete underlying V5 data: not established;
- public accessibility of V5 hardware: not established;
- Amy's 2020 unnamed review object = final TM: strong candidate, not exact identity.

POAMS therefore remains the strongest **non-routine** boundary case, but not an Amy-specific completed same-object transfer.

## LeBlanc / NASA FICS-FSP

NASA's 2024 Fission Instrumentation & Controls Workshop restricted attendance to U.S. persons. The later public NTRS presentation `20250008475` reports workshop outcomes including the live FICS/CINDI database, working groups, and draft technology-growth path.

Current status:

- access-bounded workshop context: supported;
- later public outcome reporting: supported;
- workshop material/database itself later made public as the same object: not established;
- FICS/CINDI database access status: not located in this pass.

Therefore this is **contextual boundary adjacency**, not a completed same-object transition.

## Chavez / DARHT-Scorpius

DOE/NNSA and LANL publicly expose substantial DARHT/Scorpius accelerator architecture and programme purpose. DOE's DARHT environmental record separately notes that details of nuclear-weapons design are classified, and Scorpius/subcritical experiments exist to produce stockpile-relevant radiographic/plutonium data.

Current status:

- public accelerator/programme architecture: supported;
- classified national-security environment: supported;
- exact Scorpius dataset/design object shown to move classified -> public: not located;
- Chavez-specific declassification/release agency: not established.

Therefore this too is contextual boundary adjacency rather than a completed B witness.

## Loureiro / Viriato

The Viriato paper, arXiv version, MIT profile and EUROfusion material publicly expose model, algorithms, implementation architecture, scaling/performance and benchmarks. This pass still did not locate an authoritative public source-code repository or a prior private/restricted state of the same Viriato code artifact.

So:

- deep technical externalisation: supported;
- source-code public release: unresolved;
- prior bounded code state: unresolved;
- same-object boundary transition: not established.

## Current hierarchy

| Case | Boundary kind | Same-object completed? | Current reading |
|---|---|---:|---|
| Reza/Jacinto patent | ordinary patent confidentiality | yes | real but routine B witness |
| POAMS | contractual proprietary | no all-layer completion | strongest non-routine boundary case |
| LeBlanc/FICS | internal/access-bounded context | no | contextual adjacency |
| Chavez/Scorpius | classified national-security context | no | contextual adjacency |
| Loureiro/Viriato | unresolved | no | deep externalisation, no boundary receipt |

## Consequence for H_B

The old binary hypothesis `private/restricted -> public` is too broad.

The live stronger hypothesis is now:

`H_B* = roster enrichment for non-routine same-object technical boundary transitions`.

Routine patent confidentiality must be separately controlled. Like-for-like enrichment requires matching on boundary mechanism.

The first unresolved leaf is therefore not "find any B witness". One already exists. It is:

1. close a **non-routine** same-object roster transition; and
2. compare it against matched peers with the same opportunity and boundary mechanism.

The highest-value candidate remains Amy/POAMS, where exact object identity is still the missing weld.
