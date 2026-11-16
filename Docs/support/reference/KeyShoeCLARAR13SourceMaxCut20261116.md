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
