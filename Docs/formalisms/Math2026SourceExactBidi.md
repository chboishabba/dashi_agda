# 2026 source-exact mathematics BIDI tranche

This follow-up starts from merged PR #661 and the current repository source-attribution policy.

## Attribution invariant

External source claim / datum is kept distinct from DASHI reconstruction, DASHI cross-module inference, new DASHI theorem, and promotion or external adjudication. Stable DOI/arXiv/canonical source identifiers are included where recovered; metadata is not invented where unavailable.

## Dujella prime-power Diophantine tuples

Primary source: Andrej Dujella, *Prime-power Diophantine tuples* (2026 preprint, 13 pp.; no DOI asserted here). The supplied manuscript proves a uniform bound for positive reduced `D(±p^r)`-tuples, then derives the prime-square corollaries and the `O(r)` recurrence. The source proof architecture is represented as:

```text
preliminary lower bound
+ prime-power factorization / e-vs-e-bar branch
-> easy-branch gap

full-modulus congruence
-> negative-sign hard-branch control
-> toric monomial-saturated eliminant
+ exact Jacobian nonvanishing certificate
-> polynomial nonvanishing
-> uniform gap

uniform gap
+ bounded-|n| input
+ large-element input
-> reduced prime-power < 2^121
-> p-divisible recurrence
+ D(±1) terminal bounds
-> positive prime-square < 2^122
-> arbitrary nonzero-integer D(p^2) < 2^123.
```

The source explicitly explains why an unsaturated homogeneous resultant is insufficient at fixed coordinate base points and replaces it with a toric certificate. Appendix A describes an exact-rational interval certificate using `Fraction`, `isqrt`, integer arithmetic and a 120-term determinant evaluation. DASHI records that external certificate architecture but does not claim an Agda replay yet.

### AI attribution

The supplied preprint acknowledges use of **ChatGPT 5.6 Sol (OpenAI)** and says that discussions about earlier versions of the Dujella--Luca argument and attempts to prove nonvanishing of the eliminant led to the toric elimination lemma (Lemma 6.1). It separately states that Dujella is responsible for the proofs, verification and final presentation.

The supplied open-problems supplement labels Problem 5.6 as solved by Dujella with assistance from **ChatGPT 5.6 Sol Plus**. DASHI preserves these as two source label surfaces rather than silently identifying the model labels.

## de Bruijn--Newman

Source welds now distinguish:

```text
Polymath published analytic criterion
+ Platt--Trudgian published verified-height input
+ Gomila candidate parameters
+ final-time interval package
+ intermediate-time barrier package
+ same-parameter compatibility
+ exact certificate replay
+ criterion application
-> Lambda upper bound.
```

Published sources:

- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function, and a new upper bound for the de Bruijn-Newman constant*, Research in the Mathematical Sciences 6 (2019), DOI `10.1007/s40687-019-0193-1`, arXiv `1904.12438`.
- Dave Platt and Tim Trudgian, *The Riemann hypothesis is true up to 3·10^12*, Bulletin of the London Mathematical Society 53 (2021), 792--797, DOI `10.1112/blms.12460`.
- Jude Gomila, public candidate audit repository `judegomila/dbn-lambda-01787854-candidate-audit`; candidate status is not promoted to peer review.

The exact already-merged rational package `129/800`, `87677/2500000`, `893927/5000000` is reused rather than duplicated. External certificate replay and the final criterion application remain explicit open Agda obligations.

## Cross-frontier BIDI

The new repo-native cross-pollination owner consumes the existing RH, NS and YM frontier owners without attributing its generic theorem pattern to their external sources.

### RH

The current G2 owner already demonstrates:

```text
checked Lean proof provenance != transported Agda proof terms
```

and keeps the target-centred local-zero harmonic-analysis estimate open. It also records a genuine no-go: strict off-energy-below-cluster cannot be the final consumer under unchanged projective balance, so a balance-breaking premise or changed comparison object is required.

### Navier--Stokes

The Round285 owner demonstrates BIDI route rejection: the bounded almost-periodic persistent-bad route has been ruled out for the declared badness predicate, while the direct signed critical-cone covariance theorem remains the highest-alpha physical leaf. A failed route is retained as a theorem-level no-go rather than weakened into a new assumption.

### Yang--Mills

The merged Round132--144 / Round140 architecture demonstrates same-object discipline: a compiler can be machine checked while literal physical source inhabitation remains conditional. Generated action, density, coupling history and stress insertion require explicit equality/realization maps; matching names do not make parallel objects identical.

## Shared rule

Across all five settings the reusable DASHI invariant is:

```text
announcement / matching prose / output number
    -/-> source-exact proof stage

external kernel receipt or exact numerical certificate
    -/-> Agda proof term

downstream compiler closure
    -/-> source-leaf inhabitation

proved no-go for one route
    -> redirect the search
    != relabel the failed premise.
```

Prime-gap source reconstruction remains intentionally gated: the current repo has the claim/provenance surface, but no exact new manuscript plus Alexeev Lean artifact has yet been recovered into this tranche, so no theorem statement is invented.
