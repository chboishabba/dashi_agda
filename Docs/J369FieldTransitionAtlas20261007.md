# J369 finite-field and transition atlas — 2026-10-07

This tranche turns the PR #1053 finite-field ticket and requested graph-style visualisation into deterministic numerical outputs. It intentionally does **not** use generative imagery.

## Generator

```bash
python3 scripts/j369_field_transition_atlas.py --outdir /tmp/j369-field-atlas
```

Outputs: `fieldBracketTable.csv`, `fieldCandidates.csv`, `atlasManifest.json`, `fieldRelationGraph.svg`, `legacyMass18TransitionGraph.svg`, `legacyMass18EdgeDensity.svg`, `legacyMass18Transitions.csv`, and `OggSSPFiniteFieldBracketGenerated.agda`.

`./scripts/check_j369_field_transition_atlas.sh` runs stdlib-only tests, regenerates the outputs, and diffs the committed small certificates.

## Field-bracket results

The generator independently re-derives all 16 authoritative rows. In particular:

- `196830` is bracketed by `196817` and `196831`;
- `196831` passes exact integer primality testing, so `196830 = |GF(196831)^*|` numerically;
- `80 = |GF(81)^*|`, with `81 = 3^4`;
- `810 = |GF(811)^*|`;
- exact fields occur at `5, 9, 27, 31, 81, 243, 729`.

Frobenius-orbit hypotheses numerically confirmed:

- `3 = orbits(GF(4)/GF(2))`;
- `6 = orbits(GF(9)/GF(3))`, also `orbits(GF(16)/GF(2))`;
- `10 = orbits(GF(16)/GF(4))`;
- `15 = orbits(GF(25)/GF(5))`;
- `24 = orbits(GF(81)/GF(3)) = orbits(GF(64)/GF(4))`.

The two distinct realizations of 24 show directly that orbit count alone cannot identify a tower.

T5 now records the **field-side** subfield lattice mechanically. For example, `GF(81)=GF(3^4)` contributes subfield sizes `[3,9,81]`, and the `GF(81)/GF(3)` candidate for carrier 24 carries the same field-side chain. This is deliberately not an object-side recognition statement: matching that lattice against a DASHI sub-carrier lattice still requires an independently constructed object map and recognition proof.

## The 1,330-state numerical graph

`DASHI.Biology.FRACTRANSSPTransitionExact` already owns a four-exponent legacy projection with total `firstEnabledStep`. Restricting `(a47,b53,c59,d71)` to non-negative states of total mass 18 gives

```text
C(18 + 4 - 1, 4 - 1) = C(21,3) = 1330
```

states. One total transition per state gives exactly **1,330 nodes and 1,330 directed edges**.

This matches the node/edge counts in the supplied browser screenshot, but does **not** identify the graphs. Under the deterministic 37-column embedding used here, the DASHI graph has **233 distinct 2D displacement vectors**; the screenshot reports 12. The repository therefore records the 1330/1330 coincidence while rejecting same-graph promotion.

## Recognition boundary

All field/tower hits remain numerical candidates. `OggSSPFiniteFieldBracketExact.agda` records object map, arrow map, action intertwining, orbit map, representative compatibility, stabilizer preservation/reflection, and semantic `pi0` payment as **unpaid**. T5 field-side lattice data is generated, but object/subfield-lattice matching is not inferred from cardinalities.

The `80/81` interpretation remains open as a semantic recognition problem despite the exact cardinal arithmetic.
