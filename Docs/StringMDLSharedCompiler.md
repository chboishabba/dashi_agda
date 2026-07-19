# String MDL shared compiler contract

## Scope

This tranche formalises the compression substrate discussed for the shared SB/SL
compiler. It does **not** perform lemmatisation, canonical-word collapse, or semantic
root identification.

The compression problem is:

```text
state = (corpus, dictionary, segmentation)
L(state) = L(dictionary) + L(corpus | dictionary, segmentation)
```

Dictionary entries are reusable string factors only. Examples such as `dut + y`,
`dut + ies`, `br + own`, and `bla + ck` are admissible when they reduce the exact
two-part code length; they are not semantic assertions.

## Formal modules

- `DASHI.Compression.StringMDLCore`
  - exact two-part MDL state contract
  - exact reconstruction and source preservation
  - admissible move semantics
  - strict and non-worsening move witnesses
  - explicit candidate-family cost and family-relative minimum
  - fail-closed boundary against semantic canonicalisation and unbounded optimum claims
- `DASHI.Compression.DashiGuidedSearch`
  - integer-friendly Dashi coordinate/proposal interface
  - actual proposal-list membership witness
  - exact-MDL acceptance gate
  - proofs that guided accepted moves preserve source and strictly descend MDL
  - explicit boundary: embedding guides search but cannot authorize moves
- `DASHI.Interop.SharedCompilerDualSurface`
  - one shared compiler core and canonical state IR
  - SB general-state projection
  - SL legal/normative projection
  - explicit rejection of a second legal parser
- `DASHI.Compression.Everything`
  - focused aggregate import surface

## Guarantees

For every `ExactImprovement` witness:

1. the move is admissible;
2. reconstructed source text remains exact;
3. source text is preserved across the move;
4. exact MDL length strictly decreases.

For every `GuidedExactStep` witness:

1. the candidate occurs in the embedding guide's proposal list;
2. the exact MDL witness names the same move;
3. the embedding cannot substitute for exact acceptance;
4. the accepted move preserves source and strictly decreases MDL.

Global optimality is represented only relative to an explicit `CandidateFamily`, whose
family-description cost is included in the comparison. This leaves room for exhaustive
or DASHI-contracted search over a declared family without silently promoting an
unbounded universal optimum.

## Zelph boundary

A recursive graph engine such as Zelph may maintain and traverse candidate substring,
segmentation, dependency, and rewrite graphs. It may also evaluate structural
constraints and prioritize recursive search. The formal authority remains:

```text
Dashi/Zelph proposal graph -> exact admissibility -> exact MDL comparison -> apply
```

Thus graph recursion and Dashi coordinates may reduce operations dramatically while
reconstruction and acceptance remain independent of heuristic quality.

## Next implementation lane

The next concrete layer should instantiate the abstract contracts with:

1. a typed move algebra (`Promote`, `Merge`, `Split`, `Refactor`, `ReplaceSpan`);
2. exact incremental code-length deltas;
3. a versioned string-factor dictionary and segmentation state;
4. a Dashi ultrametric/chamber coordinate used only for candidate ordering;
5. bounded exact benchmarks against BPE/unigram-style baselines and exhaustive
   subproblems.
