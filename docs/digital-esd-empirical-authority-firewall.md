# Digital-ESD empirical authority firewall

## Purpose

This note applies the repository's provenance/authority discipline to the digital-ESD review workflow.

The controlling separation is:

```text
formal/reproducible processing
!= extraction correctness
!= empirical grounding
!= claim truth
!= admitted claim ceiling
```

The review may later retain stable hashes for database exports, source snapshots, extraction tables or generated synthesis artifacts. Those hashes improve provenance and reproducibility. They do not create empirical authority.

## Core firewalls

The formal owner `DigitalESDEmpiricalAuthorityFirewallExact` blocks:

```text
formal entailment -> empirical grounding
procedural reproducibility -> extraction correctness
complete attribution -> claim support
content/hash identity -> claim truth
source discussion rhetoric -> admitted claim ceiling
stable export -> search completeness
```

The constructive collisions are especially important:

1. the same formal consequence may be derivable from externally grounded premises or from merely transcribed/stipulated premises;
2. the same deterministic extraction procedure may reproducibly emit a correct extraction or a wrong extraction.

Therefore neither derivability nor reproducibility is a sufficient statistic for the corresponding epistemic query.

## Relationship to the 20-coordinate extraction method

This is **not a 21st extraction coordinate**.

The current review method remains:

```text
19 base coordinates
+ 1 structured study-claim-ceiling bundle
= 20 effective top-level coordinates
```

The authority firewall governs promotion across those coordinates. It asks whether the retained source/design/statistical/provenance receipts genuinely pay the requested consumer claim.

## Exact source attribution still matters

`AttributedSource` remains mandatory because attribution answers a different question:

```text
which exact source object did this claim/extraction come from?
```

It does not answer:

```text
is the claim true?
is the source's broadest interpretation warranted?
was the extraction correct?
is this source independent corroboration?
```

Thus:

```text
provenance != proof != empirical support != authority
```

## Content-addressed and reproducible review artifacts

If search exports, PDFs, extraction tables or synthesis snapshots are later content-addressed, the permitted inference is approximately:

```text
same retained content -> same deterministic processing result
```

where the processing function is itself fixed.

The forbidden promotion is:

```text
same CID/hash -> correct extraction
same CID/hash -> source truth
same CID/hash -> complete search
same CID/hash -> sufficient evidence
```

A reproducibly wrong parser remains wrong. A perfectly archived paper may contain an unsupported claim. A stable search export may still reflect a malformed query.

## Interaction with the study-claim ceiling

The source paper's discussion/conclusion is itself evidence to be attributed, not the authority that sets the review's claim ceiling.

The ceiling remains design-relative:

```text
exact source
x design
x realised sample / analytic corpus
x measurement
x uncertainty
x scope / transport
-> strongest admissible claim kind
```

Therefore:

```text
paper says "transformation"
!= review has evidence of system transformation
```

and:

```text
paper says "caused"
!= causal identification is paid
```

The review may legitimately synthesize a narrower claim than the source's rhetoric.

## Interaction with Python/static automation

`scripts/check_agda_static.py` and future extraction automation have procedural roles only.

They may provide receipts for:

- deterministic parsing;
- module/path consistency;
- import resolution;
- structural syntax checks;
- required-field presence;
- reproducible extraction transformations;
- content hashes and lineage.

They do not provide receipts for:

- Agda kernel typing;
- empirical truth;
- correct interpretation of a paper;
- causal identification;
- representativeness;
- search completeness;
- source independence.

The automation rule is:

```text
automation can preserve or test a declared invariant;
it cannot create the empirical premise the invariant ranges over.
```

## Roadmap consequence

The operational review loop becomes:

```text
search receipt
-> exact source acquisition
-> attributed source identity
-> extraction / design-statistical receipts
-> extraction correctness review
-> source-specific claim ceiling
-> synthesis
-> reproducible artifact / hash
```

with the important non-commutation:

```text
hashing or formalising earlier in the chain
cannot pay a missing empirical/source obligation later in the chain.
```

This is the review analogue of the wider DASHI rule that citation, publication, formal entailment, model satisfiability and content-addressed transport do not by themselves create semantic or empirical authority.

## Status

Source-written method boundary only. This note does not claim database execution, source inclusion, empirical validation, Agda kernel certification, or final manuscript findings.
