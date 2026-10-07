# J369 finite-field and transition atlas — 2026-10-07

This tranche turns the PR #1053 finite-field ticket and requested graph-style visualisation into deterministic numerical outputs. It intentionally does **not** use generative imagery.

## Generator

```bash
python3 scripts/j369_field_transition_atlas.py --outdir /tmp/j369-field-atlas
python3 scripts/j369_kernel_field_recognition.py --output /tmp/kernelFieldRecognition.json
```

Outputs include `fieldBracketTable.csv`, `fieldCandidates.csv`, `atlasManifest.json`, `fieldRelationGraph.svg`, `legacyMass18TransitionGraph.svg`, `legacyMass18EdgeDensity.svg`, `legacyMass18Transitions.csv`, `kernelFieldRecognition.json`, and generated Agda certificates.

`./scripts/check_j369_field_transition_atlas.sh` runs both stdlib-only test suites, regenerates the outputs, and diffs the committed small certificates.

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

T5 records the **field-side** subfield lattice mechanically. For example, `GF(81)=GF(3^4)` contributes subfield sizes `[3,9,81]`. Matching that lattice against a DASHI sub-carrier lattice still requires an independently constructed object map and recognition proof.

## K4/K5/K6 structural promotion

`OggSSPTriadicKernelF3LinearExact.agda` now source-writes the coordinate `F3` operations on the existing `TriadicPAdicCodec.Kernel d` carrier using

```text
zer = 0, pos = 1, neg = 2 = -1.
```

The finite scalar laws are paid by exhaustive constructors and lifted pointwise to kernels. The source now proves the additive group laws, scalar identity/zero laws, both distributivity laws, scalar associativity, and that the pre-existing codec inversion is exactly scalar multiplication by `-1`. Thus `Kernel d` has a source-written `F3` vector-space law bundle, in particular for `K4`, `K5`, and `K6`.

`scripts/j369_kernel_field_recognition.py` then checks selected irreducible polynomial presentations for degrees 4, 5 and 6. The resulting coordinate fields have orders `81`, `243`, and `729`; their nonzero multiplicative groups contain primitive elements of exact orders `80`, `242`, and `728` respectively. Every nonzero coordinate is exhaustively checked to have an inverse.

The generated Frobenius orbit profiles are:

```text
GF(81):  3 fixed + 3 two-cycles + 18 four-cycles
GF(243): 3 fixed + 48 five-cycles
GF(729): 3 fixed + 3 two-cycles + 8 three-cycles + 116 six-cycles
```

For the already-existing `C2` negation action, punctured `K4/K5/K6` split into exactly `40/121/364` two-cycles. Thus the coordinate object map and the `-1` action intertwiner are now genuinely paid. The selected extension-field multiplication remains a chosen presentation, not a theorem that prior DASHI actions already supplied that multiplication.

## The 1,330-state numerical graph

`DASHI.Biology.FRACTRANSSPTransitionExact` already owns a four-exponent legacy projection with total `firstEnabledStep`. Restricting `(a47,b53,c59,d71)` to non-negative states of total mass 18 gives

```text
C(18 + 4 - 1, 4 - 1) = C(21,3) = 1330
```

states. One total transition per state gives exactly **1,330 nodes and 1,330 directed edges**.

This matches the node/edge counts in the supplied browser screenshot, but does **not** identify the graphs. Under the deterministic 37-column embedding the DASHI graph has 233 distinct 2D displacement vectors. An exhaustive scan of row-major widths `2..200` finds **no** 12-vector realization; the minimum is 196 vectors, reached at widths 173 and 189. The screenshot's 12-vector statistic is therefore not recovered by this embedding family.

## Full signed-weave graph frontier

The repository already pays the full 15-lane carrier path:

```text
SSP15 internal lane
  <-> chosen Ogg prime lane
  <-> SignedSSP prime lane
  -> pointed signed lane
  -> full SSPValuation
  -> SignedSSPExecutionState/program machinery.
```

However `SignedSSPFRACTRANWeaveExact` does **not** currently own a canonical total step

```text
SignedSSPExecutionState -> SignedSSPExecutionState.
```

`OggSSPFullSignedTransitionGraphFrontierExact.agda` makes that missing constructor explicit as `FullSignedTransitionGraphSocket`. No full 15-lane transition graph is generated until such a scheduler is supplied; inventing one for visualization would exceed the current formal source.

## Recognition boundary

The old blanket numerical field candidates remain unrecognized. The new `K4/K5/K6` cut pays more narrowly:

- coordinate object map: paid;
- full additive/scalar `F3` vector-space law surface: paid in source;
- `C2` arrow/action seam for negation: paid;
- runtime orbit profiles: paid;
- selected finite-field multiplication/inverses: runtime paid;
- canonicity of that multiplication from prior repo semantics: unpaid;
- full action-groupoid recognition against field multiplication/Frobenius: unpaid.

So the remaining mathematical frontier is no longer cardinal arithmetic or `F3` linearity. It is to derive a canonical multiplication/Frobenius action from independently existing DASHI structure, or prove that no such promotion is justified, and separately to construct the missing canonical total step for the full signed 15-lane execution state.
