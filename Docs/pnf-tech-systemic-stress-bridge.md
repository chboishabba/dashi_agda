# PNF → tech/systemic-stress bridge

This bridge connects the repository's existing PNF spectral-field and braid-transport architecture to the technology/systemic-stress and quotient-MDL crisis stack.

It does **not** turn PNF similarity, news alignment, or evidence braids into a market prediction. Its job is narrower and more useful: preserve the provenance, temporal revisions, contradictions, support changes, residual terminations, and candidate-reference paths around a detected BAD window.

## Reused PNF architecture

The bridge directly imports:

- `DASHI.Interop.PNFBraidTransportField`
- `DASHI.Interop.PNFSpectralFieldArchitectureReceipt`
- `DASHI.Promotion.PNFSpectralEmpiricalBasinValidation`

The PNF architecture already separates:

1. raw evidence;
2. evidence-span PNF emission;
3. corrected product-base / PNF-only summaries;
4. residual meet/join graph and Laplacian;
5. graph, DAG, and tree projections;
6. fibre-field and braid transport;
7. spectral coordinates and vector-index lookup;
8. resolver, selector, and ITIR validation;
9. support-packet or candidate-signal output.

The braid layer additionally preserves source events, revision slices, strand roles, crossing kinds, candidate refs, fibres, and termination at `noTypedMeet`.

## Cross-pollination

The PNF layer can contribute:

- source-event binding for a BAD window;
- revision lineage and correction/retraction history;
- contradiction and support-strengthening/weakening traces;
- evidence-fibre residual termination;
- historical analogue candidates;
- receipted scenario-attribution candidates.

The crisis layer separately contributes:

- market observations;
- latent-fragility / proximity / active / abating phase classification;
- quotient/compression-fracture diagnostics;
- the balance-sheet and funding transmission chain;
- MDL, side-information, holdout, and competing-model gates.

The formal seam therefore keeps four questions distinct:

1. **What evidence and revisions surround the BAD window?** — PNF.
2. **Where does stress appear concentrated?** — scenario attribution.
3. **Is the selected quotient/model ceasing to compress the market observations?** — compression regime.
4. **Is the financial transmission mechanism independently observed and validated?** — crisis/MDL receipt.

## Two residual meanings

The bridge explicitly prevents a common category error.

A PNF residual records incomplete typed meet/join, contradiction, support mismatch, or transport termination between evidence fibres. An economic residual records model mismatch and loss of compression in observed market structure.

They may corroborate one another, but they are not definitionally identical. The bridge exposes `corroboratedButDistinctResiduals` rather than collapsing the two.

## Hard gates

A PNF scenario-evidence receipt is ready only when all of the following are supplied:

- source event binding;
- revision lineage binding;
- braid-signature binding;
- resolver receipt;
- selector receipt;
- ITIR receipt;
- event/news and market-clock alignment;
- no lookahead;
- complete source-side-information accounting;
- transport treated as navigation rather than truth;
- PNF residual kept distinct from economic residual;
- vector similarity kept distinct from semantic truth;
- historical analogy kept distinct from causal attribution;
- news alignment kept distinct from prediction.

The stronger joined gate additionally requires the already-defined validated tech/crisis quotient-MDL gate, including independent market-plumbing observations and transmission evidence.

## Canonical fixtures

The canonical PNF architecture is intentionally not commit-ready: its resolver, selector, ITIR, clock-alignment, and complete side-information receipts remain absent. Consequently, the canonical AI-capex and Greece-style PNF/news fixtures remain `unsupportedLevel` as systemic-mechanism claims.

A fully receipted PNF attachment can accompany an independently validated crisis receipt, but it does not upgrade the mechanism promotion level. Promotion remains projected entirely from the crisis/transmission/MDL receipt.

## Runtime deliverables

The formal bridge implies the following empirical implementation contract:

1. Emit a stable BAD-window identifier and exact market-time interval.
2. Bind every article/source event to publication time, ingestion time, revision time, URL, and content digest.
3. Emit PNF source, fibre, crossing, residual, and braid-signature receipts.
4. Run resolver and selector without access to forward outcomes.
5. Preserve all rejected candidates and search multiplicity as side information.
6. Align PNF event clocks with the market observation window explicitly.
7. Compare historical analogue ranking on a train/holdout split.
8. Build the market-plumbing and transmission receipt independently.
9. Report PNF attribution, compression regime, mechanism status, and MDL status as separate columns.
10. Never convert an adverse structural trit or PNF candidate into an automatic short or production trade.

## Added modules

- `DASHI.Interop.PNFTechSystemicStressBridge`
- `DASHI.Interop.PNFTechSystemicStressBridgeRegression`

Both are imported by `DASHI.Economics.SystemicCrisisSignalAll`, allowing the focused Agda lane to exercise the integration transitively.
