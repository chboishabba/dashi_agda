# Paper-audit verification phase

[Back to the paper-corpus overview](README.md)

Every paper lane returns a source-preserving theorem extraction, not a conclusion label. The orchestrator then runs the following checks.

## 1. Source fidelity

- Confirm author, exact title, version and DOI or repository identifier.
- Separate theorem, lemma, hypothesis, heuristic, numerical observation and prose claim.
- Preserve the source’s quantifiers and domain.
- Record whether the result is periodic, whole-space, axisymmetric, conditional, finite-cutoff or full-system.

## 2. Mathematical extraction

- Identify the first implication not already classical or checked in repository.
- State its exact preconditions and postcondition.
- Name every constant and its dependence on `q,Q,N,T*`, viscosity and initial data.
- Place the statement at its first node on the L0–L23 ladder.

## 3. Falsification

Run the smallest relevant exact tests:

- constant and affine fields;
- high–high to low and high–high to zero Fourier interactions;
- additive energy floors;
- finite-horizon versus global quantifiers;
- zero hysteresis gap;
- supercritical amplitude scaling;
- spectral-projector eigenvalue crossing;
- low-frequency Poincaré failure;
- generic property transport under a supplied exact integral equality.

The concrete time map and BKM change-of-variables equality for any source remain open until separately constructed. A counterexample narrows only the implication it satisfies. It does not erase unrelated local lemmas.

## 4. Highest-alpha acceptance gate

A surviving producer advances only when:

- it is scale-correct;
- constants are cutoff-uniform;
- no continuation norm is assumed on the right;
- all source terms are named;
- its viscosity allocation is explicit;
- it composes with adjacent ladder nodes;
- and it reduces the number or scope of `physicalProducerOpen` clauses.

## 5. Static and kernel verification

Run:

```bash
AGDA_JOBS=1 bash scripts/check_ns_luo_claim_corpus_highest_alpha_round24.sh
```

The checker cascades through Round 23, rejects holes, postulates, unsafe options, trust primitives and placeholders, verifies every identifier currently stored in the typed source corpus, checks all twenty-four L0–L23 node names and fail-closed status theorems, checks every relative documentation link declared by this tranche, and invokes pinned Agda 2.9 on the cumulative Round 24 validation root.

An absent or failed kernel result leaves every new lane unpromoted. A code-review bot result is not a substitute for kernel verification.

## Queue-quality metrics

Continue refinement only when one of these changes materially:

- fewer load-bearing open lemmas;
- a smaller or more precise physical producer;
- a new exact counterexample;
- removal of an uncontrolled norm or hidden assumption;
- improved cutoff uniformity;
- an explicit reduction in the total viscosity tax;
- a new source with a genuinely distinct mechanism;
- successful kernel coverage of a substantive theorem.
