# Aristotle introspective round trip

Source: *Aristotle: IMO-level Automated Theorem Proving*, The Harmonic Team, arXiv:2510.01346v1, DOI `10.48550/arXiv.2510.01346`.

This receipt applies the DASHI introspective method to the paper's proof-search semantics:

1. formalise the theory;
2. render a deterministic visual projection;
3. recover structure from the raster with OpenCV;
4. formalise the recovered structure and compare it with the source specimen.

## Source model

`DASHI/Reasoning/AristotleMCGSHypergraphExact.agda` formalises the paper-level search kernel: state/action hypergraph, OR-at-state and AND-at-action proof semantics, observer fibres, guarded quotient proof transport, and monotone preservation of already-proved lemmas across feedback refinement.

`DASHI/Reasoning/AristotleMCGSIntrospectiveSpecimen.agda` instantiates a finite regression corpus with:

- six states `S0 S1 S1p S2 S3 S4`;
- seven actions `A0 A1 A2 T1 T1p T2 T3`;
- successful AND branch `A0 : S0 -> [S1,S2]`;
- successful alternative `A1 : S0 -> [S3]`;
- failed branch `A2 : S0 -> [S4]`;
- four terminal successful actions;
- distinct fine states `S1` and `S1p` in one observer fibre.

The specimen contains constructive certificates that `S0,S1,S1p,S2,S3` are proved, and negative witnesses that `S4` and `A2` cannot be proved in this finite graph.

## Introspective visual refinements

The first visual/decode attempt failed.  The action detector used near-square bounding boxes, so circular proved-state contours were admitted as apparent action boxes.  The recovered graph therefore had the wrong action set.  The repair was not a manual correction to the recovered data: the visual alphabet and decoder were refined so actions are wide rectangles while states remain circles.

The second attempt recovered all nodes, proof-status glyphs, fibre tags and undirected incidences, but exposed a deeper faithfulness defect: a generic visible line had quotiented the two typed incidence relations

`source(a) = s`

and

`s in targets(a)`

into one generic connection relation.  The renderer was refined again so source incidences are thick and target incidences are thin.

The first directed decoder then exposed a geometric false positive: the candidate long segment `S0--T2` overlaps the real collinear `S2--T2` segment.  The decoder now applies a typed-node occlusion rule: a candidate edge is rejected if its interior passes through another detected node.

## Final visual grammar

- circle: state;
- wide rectangle: action;
- double outline: proved;
- single outline: unproved;
- triangle tag: member of the one nontrivial observer fibre;
- thick state/action incidence: action source;
- thin state/action incidence: action target.

`artifacts/introspection/aristotle/aristotle_mcgshypergraph_faithful.svg` is the deterministic source visualisation.  `scripts/aristotle_introspective_roundtrip.py` rasterises it and recovers the signature from pixels using OpenCV.

## Final pixel recovery

The final decode recovers exactly:

- state count `6`;
- action count `7`;
- proved states `{S0,S1,S1p,S2,S3}`;
- unproved state `{S4}`;
- proved actions `{A0,A1,T1,T1p,T2,T3}`;
- unproved action `{A2}`;
- the exact action source function;
- the exact action target lists;
- the shared observer-fibre tag `{S1,S1p}`.

The decoder exits successfully only after asserting those values against its declared regression signature.  The extracted semantic receipt is checked in at `artifacts/introspection/aristotle/opencv_decode_faithful.json`.

## Formal recovered witness

`DASHI/Reasoning/AristotleMCGSRecoveredWitness.agda` models the values recovered from the pixel artifact, then proves pointwise:

- `stateStatusExact`;
- `actionStatusExact`;
- `sourceExact`;
- `targetsExact`;
- `fibreTagExact`.

These are bundled as `canonicalCVRoundTripExact : CVRoundTripExact`.

Thus, on this declared finite Aristotle regression corpus, the final visual observer satisfies the intended semantic round trip:

`Decode(OpenCV, Raster(Render(G))) ~= G`

for the recovered signature consisting of state/action cardinalities, proof status, directed hypergraph incidence and the declared nontrivial observer fibre.

The earlier failures are substantively useful: they demonstrate that visualisation is itself an observer and can perform illicit quotients.  The introspective loop detects those quotients by consumer failure and refines the visual observer until the declared consumer-relevant structure separates again.
