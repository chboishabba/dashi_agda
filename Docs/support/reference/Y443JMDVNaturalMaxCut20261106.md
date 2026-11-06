# Y443 / JMD two-generator trace / existing V-natural: exact max-cut

Date: 2026-11-06. Branch: agent/y443-monster-vnatural-maxcut-20261106.

## Attribution and ownership

- **A. A. Ivanov**, *Y-groups via Transitive Extension*, J. Algebra **218**
  (1999), 412-435, DOI [10.1006/jabr.1999.7882](https://doi.org/10.1006/jabr.1999.7882):
  Y_443 spider/central-word identification and group-theoretic source.
- **J. N. Bray**, [Monster presentations](https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html):
  twelve Coxeter generators, 79 relators for M x C2.
- **TauCeti**, [formalized Lean Y443 presentation](https://taucetiproject.org/docs/TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Monster.html):
  separate existing Lean transcription of the diagram, spider and central
  words, with relator and written-length checks.
- **James Michael DuPont (JMD / meta-introspector)**:
  [reported 10-step Y443 two-generator closure](https://x.com/introsp3ctor/status/2118462748845805690);
  user-supplied report runner gives eight *report-level* sanity checks,
  twelve new involutions, a 10-step trace and names
  `closure_pair_eq_top_of_paths`. These are JMD's results, not DASHI's.
  The underlying path words, exact generated group and Lean proof receipts
  were not supplied with the report text. Do not convert the eight checks
  into an invented formal proof.
- **Fedor K. Popov and Leonardo Rastelli**, [Lean_VOA](https://github.com/Fedor-Popov/Lean_VOA)
  and [their 2026 preprint](https://arxiv.org/abs/2611.06616):
  independent Lean formal VOA/Moonshine module construction.
- **DASHI**: the finite transcription and constructive word/action transport
  in the new Agda files below, reusing the existing Agda `VNaturalConstruction`
  and literal `VOAGroupAction`. No original claim to the historical theorem.

## Exact structure: Y443 is not a generic appearance of the number 12

Vertex names:
`a, b1,c1,d1,e1, b2,c2,d2,e2, b3,c3,d3`.

Edges: `a-b1-c1-d1-e1`, `a-b2-c2-d2-e2`,
`a-b3-c3-d3` (common central a).

```text
12 involutions:  x^2 = 1
11 edges:        (xy)^3 = 1
55 nonedges:     (xy)^2 = 1
spider:          (a b1 c1 a b2 c2 a b3 c3)^10 = 1
central:         (a b3 c3 d3 b1 c1 b2)^9 = 1
```

The first 78 Coxeter relations have written length 310; adding the
90-letter spider gives 79 and 400; adding Ivanov's 63-letter central
relator gives 80 and 463. The *historical group identification* is
Y443 / <f312> ~= M, where spider Y443 ~= M x C2. The finite word
transcription **does not** prove finiteness, the Monster order, the
centrality of f312, simplicity or this isomorphism.

## Prior code reused rather than reimplemented

- `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda`:
  the FLM-shaped `Vnatural` obtained from the existing fixed-point
  and twisted summands, under its `OrbifoldVOAAssembly` input.
- `DASHI/Moonshine/VertexOperatorAlgebraCore.agda`:
  literal VOA carrier/group-action owner.
- `DASHI/Moonshine/VertexOperatorAlgebraLinearActionReceiptExact.agda`:
  explicit linearity obligations on that same action.
- `DASHI/Moonshine/MonsterGradedVOALiteralActionSameObjectBidiExact.agda`:
  trace / state-action same-object transport.
- `DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda`:
  restriction to the mode-one Griess product.
- `DASHI/Moonshine/TwistedModuleModularity.agda`:
  `GroupWithInverse` donor reused directly.
- `DASHI/Moonshine/Monster3BNormalizerBridge.agda` and PRs
  [#1098](https://github.com/chboishabba/dashi_agda/pull/1098),
  [#1250](https://github.com/chboishabba/dashi_agda/pull/1250):
  the **different** natural Suzuki 12 and 12+78 multiplicity problem.
  Those dimensions alone are not an image of the twelve Y443 involutions.
- Existing B4 Coxeter/Weyl and Coxeter--Todd lattice implementations are
  distinct carriers; none supplies the Y443 spider quotient automatically.

## Formal proof dependency / ZKP O-R-C-S-L-P-G-F

**O — Objects.** Exact `Y443CoxeterPresentationExact.Node` (12 sites),
`Word`, positive relator lists, `TM.GroupWithInverse G`,
`VN.VNaturalConstruction` and the existing `VOAGroupAction`.

**R — Relations.** The 78 Coxeter, spider and central relators are
enumerated as words. Their evaluation in a selected group is an explicit
`RelatorsSatisfied` obligation, not a source theorem disguised as a
Boolean.

**C — Construction.** `Y443VNaturalPairGenerationExact.TwoWord` is the
freely generated word syntax on `u,v` and inverses. The already-existing
V-natural action is used directly; no new VOA carrier or Monster object.

**S — Same object.** `Y443VNaturalPairWeld` indexes the node generator
map, the word certificate, its universal generation property, the 80
relator witness and the literal VOA action by the *same G*. No agreement
based only on group order or dimension is sufficient.

**L — Lemmas, implemented.**
- `nodeCount`, `pairCount`, `elevenEdges`, `fiftyFiveNonedges`;
- `coxeterRelatorCount`, `coxeterWrittenLength`;
- `spiderLength`, `centralRelatorLength`;
- `doubleMonsterRelatorCount`, `monsterRelatorCount`;
- `doubleMonsterWrittenLength`, `monsterWrittenLength`;
- `identityRepresented`, `productRepresented`, `inverseRepresented`;
- `Y443JMDTracePowerExact.powerRepresented` (natural-power closure),
  `traceStepThreeX4` and `traceStepFourBeta` (JMD's w^5 and w^6
  subgroup propagation), and `traceStepsThreeAndFour`;
- `nodeRepresented`, `pairWordsSurjective` (constructive word for EVERY
  element when JMD node-word and generation certificates are supplied);
- `pairWordActionMatchesLiteral` (on the actual selected V-natural
  carrier, no parallel action).

**P — Preconditions still requiring actual providers.**
P0 `NodeWordCertificate`: *all twelve* exact `u,v` words, including
the path1 and path3 derivations of JMD's ten-step trace.
P0a JMD's actual `w` word and equalities `x4 = w^5`,
`beta = w^6`, now consumable by the proved `JMDStepsTwoToFour` module;
`w` has not been reconstructed from the report alone.
P1 `NodeGeneration`: the presentation-induced node-generation
theorem for the *same* selected source group.
P2 `RelatorsSatisfied`: evaluate all **80** relations in that group,
including the spider and Ivanov's final central word.
P3 source-derived isomorphism to the selected DASHI Monster carrier
and the required action on `Vnatural` (with correct automorphism laws).
P4 full automorphism/faithfulness and finite character/graded trace
compatibility using the actual selected representation, not merely labels.

**G — Guards.** No postulates, holes, order-inference-by-arithmetic,
or assertion that 12 Suzuki dimensions = 12 Y443 involutions. The
fact that JMD reports `H = Y443` is tracked as attributed external data
until the exact proof/witness is ingested.

**F — Finish/test.** First run the finite regression, then golden Agda
typechecking. Both files must pass in the same source tree. Replaying
JMD's certificate and the selected Monster/VOA identity are separate
promotion gates.

## Reproducibility and status

```bash
python3 scripts/check_y443_vnatural_pair_bridge.py --finite-only
python3 scripts/check_y443_vnatural_pair_bridge.py
```

The second command fails rather than pretending success if `agda` is
missing. The first command provides an independently executable source
transcription audit, *not* Agda kernel acceptance.

**Current state:** source-written conditional two-generator surjectivity,
plus constructive JMD trace steps 2--4 subgroup-word propagation,
and same-V-natural-action proof, finite arithmetic independently checked.
Agda has not been executed in this environment. The JMD words/Lean
certificate and an actual Monster same-object witness have not been
imported. Do not mark the unified Monster = Aut(V-natural) theorem as
established on this basis.
