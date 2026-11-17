# SensibLaw / ITIR semantic promotion policy

## Status

This is a formal interoperability policy for the SensibLaw/ITIR runtime boundary.
It does not parse text, replace spaCy, decide legal truth, or grant legal authority.

The checked Agda surfaces are:

- `DASHI.Interop.SensibLawSemanticPromotionPolicy`
- `DASHI.Interop.SensibLawSemanticPromotionPolicyRegression`

They extend the existing:

- `DASHI.Algebra.TetralemmaBridge`
- `DASHI.Interop.SensibLawResidualLattice`
- `DASHI.Core.AuthorityNonPromotionCore`

## ZKP frame

### O — objective

Prevent a runtime extraction hint from silently becoming canonical semantic truth.
Extraction remains lane-local; promotion is centralized and bounded.

### R — risk

The recurring failure shape is:

```text
surface form / regex / lexical overlap -> semantic label -> downstream truth
```

Moving the strings into a registry does not fix that shape. Numerical lexical
thresholds do not fix it either.

### C — contract

Runtime lanes emit a `SemanticCandidate` with four evidence bits:

- `structuralFor`
- `structuralAgainst`
- `heuristicFor`
- `heuristicAgainst`

plus:

- `basis = structural | heuristic | mixed`
- `targetComponent`
- `provenance`

`basis` is descriptive. Canonical promotion is computed only from the two
structural bits.

### S — state

The canonical promotion result reuses the existing tetralemma carrier:

| structuralFor | structuralAgainst | promoted position |
| --- | --- | --- |
| true | false | affirmation |
| false | true | negation |
| true | true | both |
| false | false | neither |

The four positions classify the evidence state. They do not prove the underlying
legal proposition true or false in the world.

### L — lattice

The operational ordering remains:

```text
heuristic hint < structural candidate < promoted evidence position
```

The promotion space remains only four-cornered:

```text
affirmation | negation | both | neither
```

Nuance belongs in orthogonal fields such as target component, provenance,
qualifier, wrapper, and residual level. It must not create a local explosion of
truth-state constructors.

### P — policy

1. Runtime parsing and extraction stay outside the policy module.
2. Surface-form, regex, lexical-overlap, and domain-vocabulary signals may be
   retained as heuristic evidence for review.
3. Heuristic evidence cannot alter canonical promotion.
4. Mixed candidates promote only to the extent independently supported by their
   structural evidence bits.
5. No structural support means `neither`, even where heuristic hints are strong.
6. Opposed structural evidence is preserved as `both`; it is not collapsed.
7. The gate does not grant truth, legal, admissibility, runtime, empirical, or
   external authority.

### G — governance

Runtime adapters should map their outputs as follows:

```text
spaCy dependency/span evidence -> structuralFor / structuralAgainst
lexical or regex hint           -> heuristicFor / heuristicAgainst
```

A direct assignment from a lexical hit to a canonical promoted position violates
this contract.

Repository guards should eventually enforce:

- truth-bearing runtime fields are projections of the central promotion gate;
- lexical hints cannot populate structural evidence fields;
- new truth-state constructors require a lattice-level proof obligation;
- candidate provenance and target component remain present;
- absence or parser failure falls closed to `neither`.

### F — gap

The target invariant is:

```text
number of canonical promotion states reachable from heuristic evidence alone = 0
```

## Proven laws

The Agda module proves by computation:

- structural-for only promotes to `affirmation`;
- structural-against only promotes to `negation`;
- opposed structural evidence promotes to `both`;
- absent structural evidence promotes to `neither`;
- every heuristic-only candidate promotes to `neither`;
- changing heuristic bits cannot change the promoted result;
- mixed evidence without structural support promotes to `neither`;
- the formal gate carries a closed authority-non-promotion bundle.

## SensibLaw integration boundary

The intended Python-side shape is conceptually:

```python
candidate = {
    "basis": "structural" | "heuristic" | "mixed",
    "structural_for": bool,
    "structural_against": bool,
    "heuristic_for": bool,
    "heuristic_against": bool,
    "target_component": str,
    "provenance": str,
}
```

The runtime implementation may use richer span packets, dependency evidence,
receipts, and source IDs. Those are preserved upstream and projected into this
small gate; they are not replaced by it.

## Non-claims

- The tetralemma position is not a judicial finding.
- `affirmation` is not verified truth.
- `negation` is not a finding of falsity.
- `both` is not dialetheist commitment; it records opposed structural support.
- `neither` is not falsity; it is the fail-closed absence of promotable structural
  evidence.
- This module does not certify spaCy accuracy or a particular parser profile.
