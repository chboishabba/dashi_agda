# Source Attribution Policy

DASHI is a formal-and-bridge repository. When a module, theorem surface, bridge,
empirical interpretation, calibration, or documentation claim is derived from
an external source, **source attribution is required whenever attribution is
available**.

The goal is not citation ornament. Provenance is part of the claim boundary:
readers and downstream formal consumers should be able to tell which statements
come from an external source, which are repository reconstructions, and which
are new DASHI extensions.

## Preferred identifier order

Use the strongest stable identifier available. Prefer, roughly:

1. **DOI** (and, where useful, its `https://doi.org/...` resolver form);
2. another stable scholarly or standards identifier, such as an arXiv DOI/ID,
   PMID/PMCID, ISBN, RFC, Handle, archival identifier, or canonical dataset ID;
3. a stable canonical publisher, institutional, repository, or project URL;
4. **author + title + venue/year** when no stronger stable identifier is known;
5. any other useful attribution that lets a reviewer recover the source.

A source does **not** become unattributed merely because it lacks a DOI. A link,
author, title, theorem locator, repository commit, dataset identifier, or other
recoverable provenance is better than silence.

## Placement

For source-derived Agda modules, put attribution near the top of the module and,
when the source is structurally important, expose it in a typed source/registry
surface rather than leaving it only in prose comments. Include as much of the
following as is available and useful:

- authors;
- title;
- stable identifier / DOI;
- journal, book, conference, repository, dataset, or other venue;
- year and volume/pages where applicable;
- theorem, proposition, section, equation, page, commit, or dataset-version
  locator when a formal import depends on a particular result;
- a short source boundary describing what is actually imported.

For documentation, place citations close enough to the claim that the source
relationship is obvious.

## Source claim versus DASHI extension

Attribution does not confer authority and does not promote an imported claim to
an internally proved theorem. Keep these layers visibly distinct:

```text
external source claim / datum
        !=
DASHI formal reconstruction of that claim
        !=
DASHI cross-paper or cross-module inference
        !=
new DASHI theorem / extension
        !=
promotion or external adjudication
```

If a paper motivates a synthetic finite witness, observer theorem, bridge, or
new abstraction that the paper itself does not state, cite the paper as the
motivation/source calibration and label the new result as a **DASHI extension**.
Do not attribute repository mathematics back to the external authors.

## Temporal provenance and repository priority

For repository-native priority or chronology questions, record the **first
implementation date** separately from all later validation/publication dates.
The preferred first-implementation receipt is the earliest recoverable Git
commit that actually contains the relevant definition, theorem body, proof
surface, compiler, or exact object. Record:

- the exact commit SHA;
- the Git timestamp in UTC;
- the same timestamp in the explicitly named local timezone when useful;
- what kind of implementation existed at that commit (for example theorem
  statement, exact representation, compiler, open consumer, candidate receipt,
  or completed proof);
- the validation state actually evidenced at that time.

Do **not** collapse these chronology events:

```text
first source implementation
        !=
first successful type-check
        !=
first exact-head CI/kernel receipt
        !=
first pull request
        !=
first merge
        !=
first publication / external release.
```

A source commit can establish that an artefact was in the repository at a given
time even when it had not yet been type-checked. It does **not** establish that
the artefact was mathematically correct or kernel-certified. Conversely, a later
type-check does not erase or redefine an earlier source-implementation date.

When a later refactor is provably the same mathematical object, retain the
original first-implementation timestamp and separately record the refactor. If
same-object identity is not established, give the new object its own timestamp.
Do not backdate from comments, plans, filenames, issue prose, or similarity of
intent alone.

The typed repository-neutral carrier for these distinctions is
`DASHI.Core.FirstImplementationTimestampExact`.

## Missing or uncertain metadata

Do not fabricate bibliographic metadata. If a DOI or canonical identifier is
not known, use the best recoverable attribution currently available and say
that the stronger metadata is unavailable or unverified. It is acceptable to
improve attribution later when a more stable identifier is found.

## Repository-native work

Purely repository-native definitions and theorems do not need an invented
external citation. When provenance could otherwise be ambiguous, label the
work as repo-native, synthetic, derived internally, or a DASHI extension.

For substantial repository-native theorem work, especially priority-sensitive
research, prefer adding the first-implementation commit/timestamp receipt as
well as ordinary source attribution for any external mathematical inputs.

## Review expectation

A source-derived change should normally fail review if it presents a paper,
external theorem, empirical result, dataset, standard, or externally developed
construction as source-free when recoverable attribution was available.

Stable identifiers are preferred because they survive link rot and make audits
cheaper, but **some accurate provenance is required where available; DOI is a
preference, not a gate that excludes sources without one**.
