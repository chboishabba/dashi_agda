# OpenAI 28 October 2026 Yang--Mills released proof: DASHI source-precise intake

**14 November 2026**. **Canonical destination:** Agda Clay #1499, Lean Clay #108; source provenance donor Agda #1212 (the distinct **openai/math** corpus). This is a newly available public external proof, not the separate October 6 openai/math manuscript family. Original upstream source credited to **OpenAI**, licensed Apache-2.0, with third-party credits in its NOTICE. The independent 10 November validation is by **Douglas, Gross, Jaffe, Klebanov, Nekrasov** (shepherding group); source release 11 November. Do not rewrite first-implementation, submitted, reviewed and publication dates as one.

## Exact pinned artifacts

- Public source: https://github.com/yang-mills-group/OpenAI-YM-20261028 at `3456e5e75cf8d4cd558955a5c7638fba2d68f464`, Lean **4.32.0**, `ChallengeSpec.lean`, `Construction.lean`, `Solution.lean`, `PublicWilson.lean`. `YangMills.jointExistence` is the public challenge statement; the `Challenge.lean` reference intentionally contains `sorry`, but `Solution.lean` does **not** import it.
- Group assessment: https://github.com/yang-mills-group/YM at `55ba9fc36293b3f4d52c6b1f813169a0be76ee98`, `submissions/openai-20261028/checks/AcceptanceSpec.lean`, `CombinedAcceptance.lean`, `docs/checks.md`, `evidence/README.md`. Reviewer endpoint `YMReview.Acceptance.combined_acceptance`; the separate `YMReview.OPE.constructed` does **not** join its existential witness to the combined choice.
- Machine-readable pinned Git blob SHA manifest: `Docs/roadmaps/OpenAIYangMills2026ProofIngest20261114.json`.
- Existing independent corpus donor: Agda #1212 `DASHI/Research/OpenAIMath/OpenAIMathUpstreamReceiptExact.agda`, pinned **openai/math** commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` with Lean **4.34.1**. The two corpora are **not identical** and must never share source SHA or kernel receipt by inference.

External report: the review compiled 43 review modules, audited 13 review declarations and the submitted endpoint, and reported only ordinary Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) on those dependencies. This is **independent reported verification**. DASHI has **not** replayed those Lean 4.32.0 checks or completed any Agda import. Our Lean-world ingestion on #1495 is pinned to **Lean 4.28.0**, so it cannot treat a 4.32 elaborated proof as native without version-compatible export, validation and a separately trusted rechecker.

## A1--A8 donor-to-original source correspondence

| Review gate | Verified external claim scope | DASHI original owner | Unpaid before promotion |
|---|---|---|---|
| A1 | Selected centered scalar Schwinger OS, zero-diagonal Schwartz tests, phase mixture | `YMClayOriginalR445PublishedWilsonRPWordWeldExact`; original OS common core | Exact same scalar, test algebra, OS continuation and full-field boundary |
| A2 | Registered invariant operator dictionary, dense words, no extra nulls in submitted sector | original Wilson finite two-source carrier and stress word dictionary | Original operator dictionary and dense-domain identification |
| A3 | Exact finite `lgt` Wilson law after beta conversion; fixed-volume full UV and extracted volume subsequence | `YMClayOriginalWilsonPhysicalF19PartitionExact`; `YMClayE1A3OriginalR445CrossCutoffSourceExact` | Original SU(N) group embedding, plaquette normalizations, 1024-link/F19 block map, observables, continuum extraction order |
| A4 | Positive short-distance normalized trace coefficient | original stress/OS modules | Trace operator identification, no D2 inference |
| A5 | Common calibration and positive lattice probe | R445 three-moment, scale source | No intrinsic continuum reference mass and no mass gap |
| A6 | Translation Ward identity on reviewed field with integrability | `YangMillsStressWardCommonCoreGeneratorExact` | Same stress charge, semigroup domain and `Q=T00=H_OS` |
| A7 | Combined single Wilson family, extracted table and Final witness | YM Clay original F19/P0 common OS root | Same-object reconstruction; E1 original endpoint remains independent |
| A8 | Explicit OPE coefficients and remainder, separate witness | source family/stress dictionary | Not attached to A7's existential witness |

**PROMOTION RULE:** an external Lean theorem, external committee's Comparator check, cloned or content-addressed source, source statement resemblance, synthetic finite benchmark or copied bridge cannot imply an original DASHI Agda proof. Agda original E1 remains OPEN until an exact original-source theorem and golden trust audit; D1 physical connected decay and D2 the same-Hamiltonian gap remain OPEN, even if the upstream E1 existence statement is accepted at its **own** definitions. The independent group explicitly excludes *unique infinite-volume limit*, *mass gap*, *confinement*, *all-orders matching*.

## Maximum-cut application order

1. **Receipt first:** check exact repo commit and `git blob` identity. Run `python3 scripts/check_oai_ym_2026_ingest.py --self-test` to validate metadata and fail-closed controls. With both pinned source checkouts: `python3 scripts/check_oai_ym_2026_ingest.py --upstream /path/to/OpenAI-YM-20261028 --review /path/to/YM`. Metadata-only output has `source_bytes_verified=0`, never a proof receipt.
2. **Weld E1 source:** prove pointwise group, Wilson beta/Haar and F19/R445 coarse-map equality, source-local insertions, cylinder tests, volume/UV order. Explicit same family, no passage between arbitrary subsequences.
3. **OS/stress:** compare reviewed scalar zero-diagonal Schwartz OS domain with our all-word positive Wilson RP, and match `T00` and domain after reconstruction. An OAI scalar OS proof is not by itself an all-field D2 theorem.
4. **Independent research:** pursue Wilson physical R445/F19 connected polymer/irrelevant-direction uniform contraction, then same-H mass gap and N1/G1. Do **not** import paper-derived mass values or a universal Peierls bound: the review has neither.
5. **World ingestion:** once original 4.32 source proofs and exactly scoped axioms are replayed, export theorem/type dependency DAG with exact Lean Name, universe, binder and kernel receipts. Route through #1495's fail-closed JMD/world-builder contract with version-adapter evidence; no automatic `4.32→4.28` cast. Publish reviewed claims, original-source weld attempts and mathematical proof status as separately addressable nodes.

## False-positive quarantine for the attached 'Solved / Closed' ledgers

- `(a_k/L_k)^2 = 1/16` when `a_k/L_k=1/4`; there is **no** derived `16^{-k}` contraction. `C/k` is not summable. Likewise a fixed bare action penalty is not automatically a uniform physical connected-polymer probability.
- A dense cyclic domain alone does **not** imply spectral support bounded below away from zero. The external review explicitly excludes a positive mass gap.
- Pointwise `h^∨(G)>0` and one-loop asymptotic freedom do not prove continuum clustering for every group.
- Global Fourier sign variation of `W''` does not refute the **selected** A2 zeta-zero signed compensation. The claimed `FarExact≥ c log t` and `CompensationTarget≤0` are not source-established, and a generic spectral cumulant does not prove the original Route B.
- The proposed NS helical shear in the attachment has `div u=ε(K−1)sin x sin(Kz)` and is not incompressible for general K; the original R71/R853 real Galerkin trajectory has not been proved. A collar width chosen from the current `‖ω‖` is not a uniform global a priori estimate.
- The classical two-Selmer exact sequence ends in `Sha(E)[2]`, **not** `Sha(E)`. A generated 2-adic square root is not unique without a selected sign; the full CM curve still needs same-source cohomological and Rubin application proofs.
- Polynomial bounds for the N21 physical bit machine cannot exclude the parser, ledger, history, scratch, copies and every head movement; finite token fuel is not the original F2/F3/F4 acceptance.

## Acceptance

SOURCE REGISTERED is justified by this document and typed Agda source, provided the commit is present. **Upstream reported check** is not **DASHI exact-head kernel check**; **candidate same-object correspondence** is not **proved weld**; **existence** is not **mass gap**. No CI claim. Local pinned kernels and transitive axioms determine admission.
