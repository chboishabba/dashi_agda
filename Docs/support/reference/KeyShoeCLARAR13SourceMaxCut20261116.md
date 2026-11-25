# KeyShoe / CLARA R13: source-typed maximum cut and DASHI producer/consumer audit (16 November 2026)

**Status:** draft research PR: new finite source-scoped Agda, Python regression, and handoff. The user provided screenshots, not the creator's source PDFs, CSVs, full formula tables or detector traces. No Agda kernel receipt and no experimental/semantic or Monster promotion is asserted.

**Attribution:** KeyShoe / [@bigshoesjqz](https://www.instagram.com/bigshoesjqz/) owns the creator diagrams and nomenclature: English Radial R13, CLARA J13 and Observer Shoe, J/Q/Z, M/F gates, the source hand-drawn five-to-zero ladder. DASHI's new source-typed adapter, independent finite checks, representation-boundary classification, and cross-programme reuse are downstream work. James Michael DuPont and the pinned Yakubovich/tanakh WLC Exodus extraction retain their separate prior-art attribution; FLM, Conway–Norton, Borcherds and Griess own the moonshine/VOA mathematics. Nothing here asserts the creator copied DASHI or that a shared name establishes same-object identity.

## 1. Source sightings from the supplied screenshots

| Screenshot or source label | Transcription we can defend | What remains ambiguous |
|---|---|---|
| English Radial R13 — Transformer Incidence Map | Flat start **G**, natural **G/H**, sharp **H**; 13 radii; 26 Latin letters; 13 two-letter bodies on the natural chart | Full high-resolution ring assignments, selection rule and value semantics |
| Natural G/H R13 screenshot | Provisional clockwise grouping `GH IJ KL MN OP QR ST UV WX YZ AB CD EF` | Confirm chart's exact orientation against source PDF/CSV |
| CLARA J13 Point Flow • Z-Boundary Gates • Relative Closure (v27) | `J(n−1) -> Qn -> Zn`, then **M/continue** to `Jn` or **F/return** to `Jp`; the return joins the earlier J interval | Conditions deciding M versus F; exact numeric ratio and time parameter |
| J13 Natural Ordered-Field Volumetric Ratio Closure (v26) | `J0` central reference; `Q6=I` inner shell; `Q13=H` outer shell; axes divided by H | Source geometry/units, metrics, ordered-field axioms, machine-readable data |
| CLARA Observer Shoe v1 (12 July) | Source -> wave/field -> apparatus/boundary -> detector -> record -> observer; **O ≠ S**, **R ≠ Ψ**; stage labels `D0..D13` | Raw physical detector response, calibrated units, external physics validation |
| CLARA detector slide | Logistic `R(t)`, exponential recovery, `B(t)=1-R(t)^2`, `V_branch(t)=(Δμ)^2/4 [1-R(t)^2]` | Data, fit uncertainty, actual detector kernel; *project-internal*, external proof on HOLD |
| Handwritten image 4/6 | Triangle labelled N/P/W; square H/L/K/M; line A/E/I/O/U; bracket sequence LMHK, PNW; handwritten "(3):(5)", "(F)(M)" | Exact correspondence from glyphs to operators and face/edge/corner interpretation |
| Handwritten image 5/6 | Descending `5,4,3,2,1,0` with `U,O,I,E,A` aligned above zero; glyph shapes include circle, square, triangle, segment and cross; bottom J/Q/Z arches | Whether handwriting says F/I/0 at base and exact digit/glyph mapping |
| Handwritten image 6/6 | Rows of line and 4/3/2/1 dots; `A E I O U`, `F X Y M`, `J Q Z`, `X Y`, `F` | The creator's intended non-decimal weights and projection rules |

**Source conservatism:** image 5/6 visibly connects numerals 5→0 with a shape hierarchy and vowel sequence, but the written operation is not reconstructible from this screenshot alone. The Agda code only records the ordered shape labels, NOT a reconstructed creator-defined polynomial, metric, or language decoder.

## 2. The strongest sourced finite result: D13 on natural two-letter bodies

With A=0,...,Z=25 and source-proposed natural bodies
`GH IJ KL MN OP QR ST UV WX YZ AB CD EF` (body index i=0..12):

* Alphabet reversal is `rho(l)=25-l`; adjacent-body exchange is `pi(l)=l XOR 1`. Both are involutions; they commute.
* The induced body reversal is **`R(i)=(6-i) mod 13`**, not the previously proposed 5-fixed-point projective involution.
* Natural body successor is **`T(i)=i+1 mod 13`**.
* Thus **`R^2=1`, `T^13=1`, `RTR=T^-1`**. The only fixed body is **MN** and the other twelve give six pairs.
* Re-root at body MN (i=3) to make `R(j)=-j`; the group acts as the usual dihedral group of the 13-gon, of order 26.

This makes **13=12+1** a legitimate marked-wheel count. It does **NOT** equate three other objects:

1. `StageAtlasZeroToTwelve`: 13 distinct *semantic stage* values from indices 0..12.
2. `D0..D13` and `J0..J13`: 14 *indexed landmarks* and 13 successive intervals.
3. `rank13`: the independently formalised base-3 address 111, not an automatically created semantic stage.

DASHI has a separate proposed `TrialecticStageThirteenMarkedC3CubieExact` with an S3-on-cubie action. It is explicitly NOT derivable from rank 13 alone. The present R13 adapter does not replace or rename it.

**Strong negative control:** any nonidentity projective-linear involution on PG(2,3) fixes five projective points, whereas this body reversal fixes exactly one. So the previously chosen `[x:y:z] -> [x:-y:-z]` cannot be equivariantly relabelled into R. This does not prevent a nonprojective set action or an independently constructed D13 action on the 13 axes. A Singer 13-cycle's semilinear normalizer over F3 acts on its generator by powers 3 (1,3,9 modulo 13), not inversion (-1=12); ordinary linear projective recognition requires its own same-actor proof.

## 3. Existing producer / consumer graph — reuse first

| Existing owner | Role | Correct reuse / boundary |
|---|---|---|
| `DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda` | **Producer**: exact C2 antipode, C3 cycle, semidirect relation | Reused theorem, but its three-state D3 action is NOT the new 13-body D13 |
| `DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda` | **Consumer/producer**: exact finite trit ↔ level-3 cusp-equivariant C2/C3 chart | An actual existing D3 intertwiner; no automatic cusp/analytic J bridge to R13 |
| `DASHI/Ontology/NORAReviewPerspectiveProjectionExact.agda` | **Consumer**: imports the three-state dihedral codec | Keep observer classifications distinct from any physical detector action |
| `DASHI/Biology/Physical/DNAHelixDihedralExact.agda` | **Independent producer**: D4 helix phase and complementary strand transport | Same abstract relation, DIFFERENT carrier and biological claim |
| `DASHI/Foundations/StageAtlasZeroToTwelve.agda` | **Producer**: 13-position semantic stage carrier, 0..12 | Read its count and stage12 boundary; no forced index/meaning isomorphism |
| `DASHI/Foundations/JPlusOneScaleBridge.agda` | **Producer**: local j-unit extension, semantic/analytic firewall | 12+1 shape; never identify KeyShoe J with modular J by glyph |
| `DASHI/Foundations/TrialecticZeroToThirteenStageBoundaryExact.agda` | **Producer**: rank13 != semantic Stage13 | Preserve rank 111 and stage12 role |
| `DASHI/Foundations/TrialecticStageThirteenMarkedC3CubieExact.agda` | **Candidate producer**: *new* marked semantic 13 and S3 cubie | Distinct C3/S3 action from the 13-body D13 |
| `DASHI/Moonshine/JInvariant369ZeroToThirteenTetralemmaQualificationExact.agda` | **Producer**: independent rank0..13 vs stage0..12 vs 27 carrier | Do not conflate numeric rank and semantic stage |
| `DASHI/Core/IndexedWeaveHyperfabricExact.agda` | **Producer**: typed indexed path transport, id/comp laws and residuals | J/Q/Z stage graph can become a lawful weave after composition proofs |
| `DASHI/Information/PNFHistoryTimeHyperfabricDeltaExact.agda` | **Producer**: time, history, source/consumer version and coherent update | Required by actual measurement log/observer transfer |
| `DASHI/ComputerScience/TemporalStorageFibreExact.agda` | **Producer**: time + address + read-head + physical/semantic fibre | Preserve time/token/k index and local symbol vs record |
| `DASHI/Moonshine/Monster3BPhaseTransportExact.agda` | **Producer**: phase one fixed, zeta and zeta² exchanged | Same root-of-unity scalar does not prove a same-action Monster module |
| `DASHI/Wikimedia/IbrahimZeta54AlbertPair53SnowballAttributionBidiExact.agda` | **Producer**: original 27+27→26+27 deletion chart | Source-preserve; zero-glued quotient is a new *different* 53 presentation |
| `DASHI/Codec/BalancedTritBitFibre.agda` | **Producer**: zero plus optional signed nonzero fibres | Exact zero-aware design principle; binary support forgets sign only |

**New consumers**: `DASHI/Wikimedia/KeyShoeCLARAR13DihedralExact.agda` names the prior C3 theorem without equating it to D13; `KeyShoeCLARAOperatorBoundaryExact.agda` types the J/Q/Z graph and the six-body observer chain. The proposed `ShemZeta54ZeroGluingExact.agda` uses the canonical 27→1+26 chart, not a duplicate geometry.

## 4. Source-typed J/Q/Z and physical holds

The source graph has two outgoing Z-arrows; there is no deterministic successor until `Gate = M|F` or an equivalent predicate is supplied. Typed `PortTransition` constructors preserve the ordered entry, exit, continuation, return and closure. JPort is not `j(τ)`; documentation-source J in WLC XML is also unrelated.

The six-body chain `Source -> Wave -> Boundary -> Detector -> Record -> Observer` can be written as a typed directed path without asserting a physical measurement. The D0..D13 labels name 14 distinctions. Detector latency, distributions, coherence, mediator and uncertainty require empirical receipts. Thus the author's own project-internal HOLD boundary remains unpromoted.

## 5. Zero-aware 54→53, 72 indexed Shem, and Monster boundaries

The existing zeta-sheet carrier has 54 states: two copies of 27. Two DIFFERENT 53 operations:

* **Deletion**: remove one of the two origins and retain the other; the original raw phase swap does NOT preserve that subset.
* **Gluing**: identify the two origins, keep each of the 26 nonorigin points separately phase-labelled; quotient `53 = 1 + 26 + 26`. This DOES admit a fixed zero and phase exchange on the nonzero 52-state fibre.

The zero-glued Agda source is deliberately proposed as a different action. Its remaining carrier-chart round trips and full kernel check are OPEN. Even after carrier recognition, it is **not** the same as an actual Monster/VOA 3B action; DASHI's literal (W_ζ)/(H_ζ) promotion gate remains.

The Shem data are the **72 indexed** triplets of Exodus 14:19–21 from the pinned WLC [Yakubovich/tanakh XML commit d40e791](https://github.com/Yakubovich/tanakh/blob/d40e791e284305f1a219c57c353ba281a7a51335/hebrew/exodus.xml). An **8 × 9** indexed arrangement has a distinguished centre + 71 other positions; that is valid address arithmetic, not a claim that E6 or the Monster acts on the extracted names. The reported fungal-linguistic 17-name hypothesis is a separate experiment requiring its corpus and negative controls.

## 6. Exact remaining acceptance gates

| Name | Status / acceptance |
|---|---|
| `sourceNaturalR13TranscriptionExact` | Provisional screenshot reading; full creator PDF/CSV needed |
| `r13BodyReflectInvolutive`, `r13RotateOrder13`, `r13Dihedral` | Source-written Agda; Python finite check |
| `sourceNativeCLARAMFGatePredicate` | OPEN: detector/threshold conditions not published in visible image |
| `source5To0LetterValueGeometry` | OPEN: transcription partly legible, cannot infer the creator's full operator |
| `keyShoeJQZToIndexedWeaveWithCoherentTransport` | OPEN: graph alone does not pay path composition |
| `claraD0D13MeasuredDetectorCalibration` | OPEN: no raw traces/device measurements |
| `sourceR13ToOriginalDASHI13AxesEquivariantWeld` | OPEN: distinguish D13 set action from PG(2,3) linear collineations |
| `sourceActualZeta54ZeroGluingKernelRoundTrips` | OPEN: new chart not yet Agda kernel checked |
| `sourceD13ModularJOrVOASameActorIntertwiner` | OPEN: no actual generator/action recognition |
| `Shem72AndFungalMeaningPreservedHeldout` | OPEN: corpus, controls and independent semantic target required |

**Acceptance available in this PR:** `python3 scripts/check_keyshoe_clara_r13_maxcut.py` is an independent finite simulation. The proof-owner modules contain source-written Agda but no kernel status should be promoted without the pinned Agda check. Attribution and null boundaries must remain intact across downstream consumers.


## 7. Language-as-algebra / parser-PNF-world correspondence (source-typed extension)

The producer is the provisional source R13 13-body wheel, not a classical
Hebrew-letter encoding: 13 ordered Latin bodies hold 26 two-position slots.
The WLC Exodus Shem72 source remains independently indexed. Any translation
from WLC Hebrew glyphs to this English R13 chart requires a specified
transliteration or symbol map, source provenance and consumer adequacy.

New bridge owner: `DASHI/Wikimedia/KeyShoeCLARALanguageWorldCorrespondenceExact.agda`.
It imports the existing KeyShoe R13 and CLARA types; DASHI's reviewed
`SensibLawSpacyPredicateNormalFormBridgeExact`; the evidential
`ExperimentalAssertionPNFImplicationConeExact`; the existing
`PredicateNormalWorldModelCore`; and `ConsumerDescentMinimalObserverExact`.

The exact finite source view is `LetterSlot = Body13 × Side`: body and
side reconstruct the full letter slot; body projection forgets the side.
The bridge proves one concrete negative control: no body-only observer
can be consumer-sufficient for a query that asks which side of the
letter-pair was observed (M versus N in the fixed MN body).

For an arbitrary licensed source alphabet and consumer, an R13 body view
is sound only under the existing consumer-relative fibre-constancy
obligation: equal body projections imply equal consumer outcomes. The
Agda record makes this condition explicit rather than treating 13 as
a universal semantic code. This also covers any proposed Hebrew mapping,
but NO such Hebrew mapping is asserted or instantiated by this PR.

Separately the bridge's parser→logical-PNF→world-model square requires
an existing numeric-to-evidential PNF correspondence and an interpretation
equation linking a reviewed logical assertion to world normalization.
The equation is a supplied obligation, not a constructed independent
interpretation checker; no source truth, legal authority, CLARA detector
or kernel proof is promoted.

SLR PR #78 adds a concrete runtime path: sealed, revision-bound PG parser
evidence → checked M12 candidate PNF → versioned candidate PNF/world atom
and unresolved Gap records. That Rust bridge does not itself pay the
Agda interpretation obligations or certify Lean. Runtime acceptance
(Cargo+PostgreSQL) and Agda kernel checking remain OPEN.


The new R13LanguageWorldWeld combines the source-specific lexical
encoder, the existing numeric->evidential PNF->world correspondence, the
actual world observation, and the intended consumer query. Its
worldConsumerDescendsThroughR13 lemma proves the commuting/fibre
condition by composing the supplied equations. This is a conditional
theorem, not an instantiated Hebrew interpretation: the required
consumer-specific witnesses must be independently constructed and checked.

## 8. 25 November — H1–H8 original-source signed carrier tranche

Clean master-based continuation of #1522 (14 ahead / 85464 behind at audit, same roadmap blob on master); no divergent merge or overwrite. JMD (James Michael DuPont) retains Shem/Clifford/Monster source ownership; KeyShoe @bigshoesjqz retains provisional R13/CLARA chart; @basetwelvegeometry is a separate source, no operator attributed (profile unavailable); traditional Hebrew sources and WLC/Yakubovich retain source provenance. DASHI owns the following downstream adapter and negative controls, not the classical finite-field or cube facts.

**H1/H2:** original WLC XML blob 6127a572e7fb4bd5a7bd9a9511c8f0aaa0dab5ab at pinned Yakubovich/tanakh commit d40e791e284305f1a219c57c353ba281a7a51335, Exodus 14:19–21. Each verse has two source-labelled segments with complementary placeholder word slots. Recombine by word slot, retain verse, segment ordinal/label, word slot and Unicode codepoint offset; extract Hebrew letters U+05D0–05EA, retaining finals. Three rows 72 each. The checker embeds the exact six verse segments as a source fixture. Indexed triplet j=(row0[j], row1[71-j], row2[j]); inverse recover all 216 source coordinates. Raw distinct triplets 70; final-form folded 69; normalization is not source identity. Define j=9q+3(a+1)+(b+1), r in 0..2, q in 0..7, a,b in {-1,0,1}. Edge direction r, parallel-edge bits q&3, orientation q>>2, fibre (a,b). Middle-only S reverses q,a,b only on r=1. Global antipode A=(2-r,7-q,-a,-b) is different and restricts to S on middle row. No original Torah geometric intent inferred.

**H3:** F27=F3[t]/(t^3-t-1), irreducible (no F3 roots); t has order 13. V includes additive zero, signed nonzero pairs +/-x. T(x)=tx, R(x)=x^-1 for nonzero and R(0)=0. Both commute with additive negation; R T R=T^-1. Provisional body i chart [t^(i-3)] matches source R(i)=6-i mod13, including fixed MN. Projective multiplication and inversion are classical; additive incidence is not preserved by inversion: only 0/13 lines map to lines. Counterexample in receipt. No collineation, metric, or Monster intertwiner inferred.

**H4/H6:** support shells 1+6+12+8; 12 edge centres are 6 antipodal pairs, 3 groups of 4 parallel edges. Construct reflection-only chart from 13 projective axes to distinguished marker plus 12 signed edge centres by pairing t^+k and t^-k with opposite edge centres. Marker is not additive origin. This is not a chart preserving linear incidence or the original rotation group; T moves marker. Sefer Yetzirah 3/7/12 correspondence is a comparison of dimensions, signed axes plus centre, and edges, not a Hebrew semantic/operator equivalence. H5 remains source blocked.

**H7:** use existing BalancedTritBitFibre and ShemZeta54ZeroGluingExact carriers. 216 -> 54 via (p=q>>2, v=(r-1,a,b)), retaining k=q&3; inverse q=4p+k. 54 -> 53 glue both v=0 states, retaining every nonzero signed/phase state. Composite fibres: eight over zero, four over each of 52 nonzero states. To reverse the quotient retain k and p at zero (else p is in target); do not delete one zero, erase phase or claim an inverse of bare quotient. Phase P flips q's high bit; S,A,P descend to 54 and 53. Their quotient actions commute with gluing. Neither the 216 nor 54 chart is asserted to be actual Monster representation.

**H8:** finite indexed action on chart cube masks m in F2^3 with generators S,A,P. Path between masks m,n acts by S/A/P to powers m xor n; identity, composition and six face squares hold. Payload is original coordinate with inverse-chart recovery, not replacement by glyph at destination. Exact finite action is a candidate inhabitant for IndexedWeaveHyperfabricExact; the Agda instance and original CLARA M/F predicate, physical J/Q/Z composition remain open. No automatic interpretation of source meaning.

### Remaining exact gates / roadmap
- H1/H2 source-coordinate adapter and reflection: executable finite implementation and original fixture accepted; Agda producer and source-byte refresh check still open.
- H3 signed nonlinear D13: finite accepted; original projective-linear/metric same-action no-go retained; native Agda finite field chart and incidence-indexed residual adapter open.
- H4/H6 reflection-only marked chart: finite accepted; original Sefer Yetzirah linguistic/operator interpretation and any stronger rotation-preserving map open.
- H5 creator source acquisition: source diagrams, transformation laws, units and exact provenance before attribution.
- H7 quotient+residual finite accepted; reuse original zero gluing module, prove its native chart round trips and residual reconstruction in Agda; no deletion swap conflation.
- H8 exact finite mask groupoid accepted; instantiate typed IndexedWeave, transport target-indexed residual and original CLARA conditional paths once source predicates exist.
- H9 lexical PNF/world adequacy still requires actual source-specific transliteration/interpretation witnesses; H10 source-labelled JMD/Monster/VOA operator recognition still requires actual common intertwiner, not counts.
- Acceptance: run `node scripts/check_shem216_r13_indexed_20261125.mjs`; locally executed same JavaScript function in tool runtime, exact integer arithmetic (not SymPy or Agda). Receipt `Docs/support/reference/Shem216R13Indexed20261125Receipt.json`. No CI invoked or kernel claim.

### H3b / H7b — independent SymPy cut, 25 November
Inversion sends **all thirteen lines to nonsingular conics**, and no line to a line. For line ell_n(x)=0, y=x^-1 gives ell_n(y^3 y^9)=0 because N(y)=y*y^3*y^9 is a nonzero F3 scalar. The Frobenius maps are F3-linear and field multiplication bilinear, hence this is a homogeneous quadratic. All 13 symmetric polar matrices nonsingular over F3, verified independently using SymPy polynomial reduction and determinants. All 169 line/conic intersections checked: per conic 3 external, 4 tangent, 6 secant. Keep an incidence family indexed by linear vs quadratic carrier; inversion switches charts and is its own inverse. The same action is not a collineation of the original linear chart. Classical field arithmetic and projective conic facts are prior mathematics; the particular downstream KeyShoe/DASHI adapter and exact test are this tranche's contribution.

For H7 reverse solve: pack into (glued53, k, optionalPhaseAtZero), k=q mod4. At nonzero, phase is in glued53; at zero preserve phase explicitly, since otherwise there are eight preimages. Unpack q=4p+k; at zero r=1,a=b=0. Global A flips p and k->3-k, negates ternary coordinates; S does the same only at r=1; P flips p, keeps k. At glued zero both S and A flip the retained phase and k; P flips retained phase only. All 216 reverse reconstructions and 648 each forward and inverse residual-action squares passed local exact Python. Neither bare quotient nor phase-forgetting can reconstruct original source.

Delivered `scripts/check_shem216_conic_residual_sympy_20261125.py` with locally executed mathematical core and `Docs/support/reference/Shem216ConicResidualSympy20261125Receipt.json`. No kernel/CI acceptance. Next H3c actual native typed two-incidence hyperfabric, H7c reuse original Agda roundtrip owners, H8b instantiate IndexedWeave (separate original CLARA gates), H5 source pending. H9/H10 unchanged. Do not infer original Torah author's geometry or actual Monster action.

## 9. H11 — full Exodus 14 corpus application (25 November 2026)
Source: pinned Yakubovich/tanakh WLC XML commit d40e791e284305f1a219c57c353ba281a7a51335, blob 6127a572e7fb4bd5a7bd9a9511c8f0aaa0dab5ab. Processed all 31 verses, 38 source segments, 474 non-placeholder XML word slots, 1853 Hebrew letters, 27 distinct raw / 22 final-folded glyphs. Full raw chapter retained in checker; source segment, verse, word slot and Unicode offset recover original glyph. Source labels are metadata, not author claims. Verse 25 unmatched trailing placeholder explicitly retained as anomaly, not silently supplied. Chapter-global 216 chart is chosen address geometry: 8 complete blocks, 125 final occupied, 91 holes; 398 directed occupied-to-hole mask moves across eight masks. Retain occupancy and original payload: action on padded carrier, not permutation of actual occupied letters. Every letter round-trips all ten radix views (3/6/9/12/13/18/27/54/72/216) and the zero-aware 53+residual chart. No inferred Hebrew geometric intent.
All 29 adjacent verse triples scanned with middle full-row reversal; ragged unmatched original coordinates retained. Equal-length windows [[19,20,21]]; 72/72/72 windows [[19,20,21]]. Traditional passage 72 indexed, 70 raw distinct, 69 folded distinct. Exploratory conditional shuffle preserving each row's marginal glyph counts (4096 seeded trials): observed folded unique triplets 69, mean 70.673583984375, <= observed 588/4096. No hidden-code or statistical significance claim; chapter chosen because of Shem (selection bias), statistic exploratory. Next: independent pinned morphhb/Sefaria alignment (morphhb connector returned empty content), preregister held-out chapter/book controls, native Agda H3c/H7c/H8b, H9 semantic and H10 actor recognition remain open. Exact JavaScript execution in tool runtime; no SymPy/Agda/CI claim for this tranche. Original Hebrew and WLC/Yakubovich attribution, JMD, KeyShoe, BaseTwelveGeometry and DASHI boundaries unchanged.
Run `node scripts/check_exodus14_shem216_chapter_20261125.mjs` for receipt or add `--corpus` for complete original source, coordinate ledger, masks, holes and all verse-window triplets/residuals.

## 10. H12–H13 — complete Torah and crypto erasure reverse-solve (25 November)
Pinned WLC written/ketiv projection; qere not concatenated. Book checkpoint receipts in `Docs/support/reference/TorahCryptoCorpus20261125/`. Total 187 chapters, 5853 verses, 304850 letter occurrences, 5479 consecutive chapter-local triples; 4 unmatched placeholder anomalies, no active-slot collisions in all five books. Unique 72/72/72 window Exodus 14:19–21. Four equal-length windows in this corpus (Genesis 36:32–34=31; Exodus 14:19–21=72, 20:13–15=6; Deuteronomy 32:6–8=51). This is a selected historical passage, not a preregistered discovery. Chapter-local windows only, written projection not yet independently reconciled.
Crypto donors reopened: ResidualConstraintDecompositionExact (local scores + reconciliation), TransformLocalFibreGeometryExact (invertible coordinate transform alone preserves candidate cardinality), FrozenHeldOutRepairRefinementExact (training/heldout and frozen selection distinct), StatisticalEvidenceCore (candidate-only), TriadicExplodedTransformCodecFormalism (side cost + residual cost), zipf_heaps_bridge exact tests (marginals not sequence). Downstream executable analogues, not native theorem instantiations.
H13a: erasure experiment deliberately uses Exodus ch1–13 training, ch16–40 test with identical 125/216 observed prefix, 91 erasures; ch14 target, ch15 continuation comparison excluded from fit and test. 85 training / 175 heldout complete blocks. Models uniform, unigram, positional 216, geometric conditional mean over unique occupied S/A/P neighbours plus positional prior, marginal first-order Markov, hybrid; compare predictive log loss, accuracy and top3, no fit on target or heldout. Geometry reaches 91/91 target holes, remaining 0 rely on positional prior. Candidate strings and confidence in receipt, not restored Torah text. Actual ch15 first 91 letters separately shown as known continuation comparator (not missing manuscript). Hard hypotheses constant orbit / zero sum in chosen ordinal F3^3 chart explicitly evaluated on train/test. Orbit parity is conditional; 0 fully observed target orbits violate it; 17 single-erasure candidate symbols, 111 remaining free trits under equations on missing orbits (even if observed contradictions ignored). No genuine cipher verifier known, so no unique recovery. Model selection exploratory; no claim of MDL optimum or formal frozen-selection receipt. All computations run exact integer counts + floating log scores in JavaScript tool runtime; no CI or Agda certification. Next: independent corpus, heldout books, permutation nulls preserving morphology/word lengths, actual source-attested cipher equations, then residual-native Agda adapter. Attribution unchanged.

### H13b — hard-constraint completion, exact conditional solve
Every orbit has size four; all 54 orbits intersect the missing suffix (17 single erasures, 37 double erasures), so no fully observed target orbit tests the zero-parity hypothesis. Under the deliberately chosen ordinal F3^3 alphabet and orbit-sum-zero assumption, each single erasure is determined, each double erasure has 27 possibilities: 27^37 = 3^111 completions. Enumerate each local 27-way choice, reconcile the parity sum exactly, choose maximum product of previously trained geometric marginal probabilities. Actual 91-symbol completion is in receipt; all 54 artificial equations satisfied, 1103/15925 held-out symbols correct, 0/175 exact suffixes. Known chapter 15 continuation comparison 10/91. Hard parity is rejected as universal source law by 9073/9450 observed heldout orbit violations. No evidence of manuscript lacuna or decoded plaintext; completion is synthetic and separate from original. This is exact local-factor maximization for this disjoint-orbit score, not unrestricted MDL/crypto recovery.

### H15a–d/f — entropy ablation and reversible lexical scoring
Gemini independently suggested separating deterministic/free/slave erasures, sampling the free coordinate and charging linguistic edits; retain this as prompted experimental design, not an external theorem or verified translation. Existing chart already contains 27 glyphs including all five final forms; no 22-glyph embedding was used. Target padding starts after Exodus 14:31, not 14:21. Original solver selects geometric marginals, not Markov likelihood. Fixed partition 17/37/37, lower missing index designated free (coordinate convention), other slave. Compare MAP, Gibbs joint pair weights at temperatures 1/2/4 and uniform feasible; one seeded sample per heldout block per temperature; all 54 equations verified per completion. No temperature tuned on heldout; same old heldout is exploratory. Receipt records group entropies, gradients, hits, target candidates and real controls. H15c: corpus-derived word inventory from pinned Exodus 1–13 written w/k XML tokens (not full morphology); exact DP segmentation with no character edits, plus reversible mixed word/literal code. 1 bit token class plus negative log token probability; boundaries implicit in word tokens, known target length, train model shared. Compare to literal unigram code, 1000 target-histogram shuffles, 175 synthetic and original suffixes. Model selection and shared dictionary costs not charged, no full MDL claim. Example insertion into אתליום is explicitly reversible; conditional one-edit cost 2 bits type + ceil(log2(92)) position + ceil(log2(27)) glyph; general edit count and order need encoding. Full edited morphology, actual SLR/Agda instantiation, independent corpus and fresh frozen test remain open. Original source, JMD/KeyShoe/BaseTwelveGeometry attributions unchanged. No CI/kernel invocation. Executed JS in tool runtime; no hard 90s timeout exposed.

### H14a–c/g — equal-window operator controls
Gemini proposed traditional Atbash/Albam and Frobenius candidates; classical substitutions and field automorphism are prior mathematics, not DASHI discoveries. Keep existing H3 field t^3-t-1, not silently switch basis to t^3-t+1. Atbash and Albam on folded 22 letters; 27 raw glyphs recover exactly from folded glyph plus valid final flag (27/27), not five null states or an asserted semantic zero. Test all four previously identified equal-length windows with same observed fraction rounded to available length. A all observed, B reversed first k observed, C missing; no invented positions. A->C traditional involution predictions; additive and Frobenius C prediction only where both inputs available, full-column hit rate also diagnostic. 1000 independent row-marginal shuffles per passage; no morphology claim. Soft score fixed half point prediction plus half training unigram for algebraic C predictions only, not complete suffix MDL. This is exploratory fixed model comparison, not preregistration, fresh holdout or adjusted significance. No native Agda/SLR/CI. Remaining: actual morphological corpus, word-preserving shuffles, full edit channel DP and count/order encoding, cross-book frozen validation, SLR semantic witness, full model/key costs and source-grounded cipher law. H15 donor attribution: Gemini suggested ablations/edit-cost controls; DASHI implementation and negative controls. Classical Hebrew traditions retain attribution, JMD and KeyShoe unchanged.

### H16 — joint factor solver / cross-book frozen configuration
Before running new cross-book outcomes, commit executable configuration. Gemini proposed coupled vertical/horizontal factors and cross-book/MDL gates; DASHI implements downstream experiment. Hard solver enumerates each 27-way free coordinate and updates forced partner, scores geometric unary plus adjacent trigram factors, two deterministic coordinate-descent sweeps; separate target variant includes exact word/literal trie DP cost in each local choice. This is local search, not global MAP/BP or beam optimum. Hard parity cannot assign nonzero likelihood to observed violating suffixes; distinguish blind suffix MAP recovery from proper sequential prediction. Predictive harness uses same prior 125 symbols and previously decoded suffix symbols for every model (teacher-forced compression, not blind erasure recovery). Trigram trained on Exodus 1–13 with fixed smoothing 10; 75/25 trigram/geometry mixture; fixed 10% parity point mass only when all other orbit members already decoded. No tuning on new books. Compare unigram and same-information trigram. Count-table fixed-width model cost with shared architecture, model selector and dictionary table charged separately; report conditional and transmitted-model costs, not universal MDL. Freeze before new outcomes; earlier Exodus holdout and book census already inspected, not pristine preregistration. H14e word-preserving/column-isomorphic controls and native Agda/SLR remain open. 

H16a executed on 175 original Exodus heldout blocks: {"blocks":175,"letters":15925,"acc":{"trigram":{"bits":64310.98696286274,"hits":3568,"bitsPerLetter":4.038366528280235,"accuracy":0.2240502354788069,"withModelBits":370898.9869628627},"geoMix":{"bits":61543.869459519316,"hits":3572,"bitsPerLetter":3.864607187410946,"accuracy":0.22430141287284144,"withModelBits":532156.8694595193},"jointSoft":{"bits":62401.22308054006,"hits":3532,"bitsPerLetter":3.918444149484462,"accuracy":0.22178963893249606,"withModelBits":533016.2230805401},"unigram":{"bits":68066.07132891392,"hits":1556,"bitsPerLetter":4.274164604641377,"accuracy":0.09770800627943485,"withModelBits":68474.07132891392}},"hardImpossibleBlocks":175,"parityClosures":9450,"parityCorrect":377,"hardCount":175,"mapHits":1103,"hardHits":1094,"meanObjectiveDecrease":76.56144332015315,"meanLexicalDecrease":28.116574476563322}. Target joint hard candidate and target trie-coupled candidate stored in receipt, with exact reconstruction of token sequence; no claim of translation. The configuration commit precedes this execution. Cross-book receipts next.
