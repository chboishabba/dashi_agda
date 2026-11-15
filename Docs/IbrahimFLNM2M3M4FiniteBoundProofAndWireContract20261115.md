# Ibrahim FLN — M2/M3 finite termination proofs, M4 wire-normal form, and exact Agda closure

## 15 November 2026 — operator 14-target acceptance and next source-written maximum cut

**New verified reference (supersedes the 13/13 and 40/40 paragraphs below):** operator locally ran `NO_TMUX=1 ./scripts/check_ibrahim_fln_maxcut.sh` at [`51dcb745ad6a9928ec8018c33be388d75bb1195d`](https://github.com/chboishabba/dashi_agda/commit/51dcb745ad6a9928ec8018c33be388d75bb1195d): **14/14 Agda 2.8.0.2** including fixed `IbrahimFinitePartialGlobalTrichotomyExact` and generated manuscript carrier; **44/44 Python**. The general constructive M3 `finitePartialFLNClassifiesOrTerminates` is now **KERNEL-ACCEPTED**, not open. Earlier historical acceptance references are retained below for provenance only.

**Further committed but not yet locally Agda-checked:** `IbrahimFiniteLoopErasureAndWireNormalFormExact.agda` adds actual-positive-gap `finitePathLoopErasure` (M2a), a first-repeat typed normal form with no earlier collisions and `verifiedNormalFormYieldsCheckedEdgePath` / `verifiedNormalFormYieldsEventualCycle` (M4a *typed proof model only*). The mandatory checker now contains **14 source Agda modules plus one generated target = 15 targets**. These new declarations must be separately checked on the latest head before claiming kernel acceptance. They do not solve M2b finite bound/M2c oracle elimination/M2d canonical choice, nor M4b/c CPython JSON refinement.

**P3 empirical source integration:** `scripts/ibrahim_original_revision_audit.py` accepts a SHA-pinned actual `formatversion=2` MediaWiki Action API original page/revid/main wikitext, runs the existing attributed author-parser behavioural port, records original pageid/oldid/raw text and exact first-qualified-link span/target, and explicitly retains source/QID/Zelph equivalence false. `tests/test_ibrahim_original_revision_audit.py` is included in Python acceptance. No author-original 2016 executable run or historical corpus completeness is implied.

**M5 aggregate diagnostic runner:** `bash scripts/check_ibrahim_wikimedia_aggregate.sh` executes `agda --safe ... DASHI/Wikimedia/Everything.agda` with operator-controlled time/memory and persists exact-head/log SHA receipt. It does not turn a resource timeout into a successful theorem. Use a fresh log directory.

**Operator run:** `NO_TMUX=1 ./scripts/check_ibrahim_fln_maxcut.sh`, then separately `IBRAHIM_M5_LOGDIR=/new/path bash scripts/check_ibrahim_wikimedia_aggregate.sh`. An unchanged 14/14 acceptance record does not cover the newly changed 15-target suite.

**Original-data/production cut:** ITIR #14 adds `acquire_pinned_source_bytes.py`, `build_zelph_native_live.sh`, `run_zelph_live_cohort.py`, and `verify_p854_document_bytes.py`. SLR #10 adds the opt-in same-existing-PostgreSQL candidate/review/reopen adapter with real connection readback; SensibLaw #514 adds the read-only NORA ITIR↔S29 source-coordinate crosswalk. They remain **new source requiring execution**. Original `.bin` identity, P854 substantive support, real S29 legacy consumer wiring and actual NORA-native export remain OPEN.

---


**Owner:** existing DASHI/Agda [PR #1505](https://github.com/chboishabba/dashi_agda/pull/1505), not a new PR. **Formal golden:** Agda. **Runtime/transport:** ITIR [#14](https://github.com/chboishabba/ITIR-suite/pull/14); SLR [#10](https://github.com/chboishabba/slr/pull/10); SensibLaw [#514](https://github.com/chboishabba/SensibLaw/pull/514). Zelph original-byte contracts remain independently owned by DASHI [#1506](https://github.com/chboishabba/dashi_agda/pull/1506).

## Source and acceptance boundary — 15 November 2026

Original First Link Network research: **Mark Ibrahim, Christopher M. Danforth and Peter Sheridan Dodds**, DOI 10.1016/j.jocs.2016.12.001. The finite bound argument, source adapters and executable checkers below are DASHI work. No Wiki page, multilingual QID or published Zelph edge is thereby authenticated.

**User-reported checked reference:** Agda 2.8.0.2 **14/14 focused modules and 44/44 Python** at exact #1505 commit `51dcb745ad081c7f53f93012ba11a51fb981f349`. This supersedes the 13/13 acceptance at `91dfccd`; it includes `IbrahimFinitePartialGlobalTrichotomyExact` alongside the 12 earlier modules and the manifest-generated literal `Trace.pathEdge refl` certificate. It kernel-certifies general constructive finite partial-FLN global classification (**M3** closed at `51dcb745ad`), while M2a–d and universal M4 remain open. The separate user-reported ITIR offline/native reference is **165/165 Python, gap-free packed partition audit, native two-pass mini-bin frontier route, four native packed sections, five negative controls, exit 0** at `fb61e629763b86c097f3f6a00a906575b02fe91d`; original immutable `.bin`/HF shard equality remains OPEN.

**New work after 91dfccd:** complete finite-bound algorithm in `scripts/ibrahim_fln_certificates.py`; all-labelled-total-graph and partial-graph exhaustive tests; strict, duplicate-free JSON wire decoder used by the reference runner and Agda exporter; Boolean `node_count` denial. Source-written only until the new branch head passes the full checker. Independently, a scratch finite model exhaustively covered **3,413** total graphs and **82,481** ordered source/target pairs (sizes 1–5), plus **1,440** partial graphs (sizes 1–4); this is **not** an Agda kernel receipt.

## M2 — complete finite reachability bound (mathematical proof)

**Input:** a finite complete carrier \(V\) of \(N\) listed positions (duplicates permissible), a total deterministic function \(f:V\to V\), and vertices \(a,b\in V\). Let \(f^k\) denote the original iterate.

**Exact claim:** \((\exists k\in\mathbb N,\ f^k(a)=b)\iff(\exists k<N,\ f^k(a)=b)\) for an inhabited carrier. The right-to-left implication is immediate. For the forward implication take the *least* qualifying \(k\), constructively available by well-founded search below an already supplied witness. If \(k\ge N\), the \(k+1\) vertices \(a,f(a),\ldots,f^k(a)\) contain a repeat \(f^i(a)=f^j(a)\) with \(i<j\le k\), because the carrier has at most \(N\) distinct vertices. Determinism gives

\[
 f^{k-\(j-i\)}(a)=f^k(a)=b.
\]

The index is a natural number strictly smaller than \(k\), contradicting minimality. The argument applies to both directions independently. Thus

\[
 a\leftrightarrow b\quad\Longleftrightarrow\quad
 \mathrm{ReachWithin}(f,b,N-1,a)\ \land\ \mathrm{ReachWithin}(f,a,N-1,b).
\]

Using fuel \(N\) instead of \(N-1\) is sound and slightly redundant, and simplifies the Agda interface. For the impossible empty-carrier/start combination, no vertex input exists.

**Current Agda reuse:** `finiteNodeEqualityFromCarrier`, `decideReachWithin`, `decideBoundedMutualRotation`, `boundedMutualRotationIsSound` (all in `IbrahimFiniteDecidableReachabilityExact`). **Exact missing kernel chain (M2a–M2d):**

1. `finitePathLoopErasure`: remove an earlier repeated vertex from a supplied `Rotation.ForwardRotation` without changing its endpoint; use `Orbit.iterateAppend` and (i+\(j-i\)=j).
2. `unboundedReachHasFiniteBound`: use pigeonhole over the complete `General.allNodes` to produce `ReachWithin next target (Pigeonhole.carrierSize (General.allNodes carrier)) start` from any `Rotation.ForwardRotation next start target`.
3. `finiteCycleMembershipDecidableFromFinEquality`: pair the complete finite-direction deciders and convert the `inj₂` branches by `unboundedReachHasFiniteBound`; output either an actual `Rotation.MutualOrbitRotation next a b` or its negation.
4. `canonicalCycleRootExistsWithoutMembershipOracle` and `canonicalCycleChoiceIndependentWithoutOracle`: instantiate existing `IbrahimFiniteCanonicalCycleRootExact` theorems with M2c. The total-order structure is still an **explicit** assumption; it cannot be inferred from an unordered carrier without specifying a canonical order.

**Status:** finite mathematics as argued above and executable algorithm available; **M2a–M2d Agda declaration/kernel acceptance OPEN**. Do not mark M2 formal closure based on tests or this prose proof.

## M3 — partial FLN complete finite trichotomy (mathematical proof)

**Input:** the same finite complete carrier of size \(N\), a deterministic `FirstLinkSelection Node Outside`, and a start node. `knownTarget` stays in the declared carrier; `explicitDeadEnd` retains the source node; `unresolvedTarget` retains its original outside token.

Run `advancePartial` for \(N\) transitions from `visiting start`. If the resulting state is `stoppedAt node`, an eligible-link dead-end was reached no later than depth \(N\) and persists forever by `partialDeadEndPersistsAfterDiscovery`. Likewise `missingTarget token` retains the exact token and persists forever by `partialUnresolvedPersistsAfterDiscovery`. If the state at time \(N\) is still `visiting node`, **every** earlier state was also visiting: either terminal state would have been absorbing. This gives \(N+1\) in-carrier visiting nodes at times \(0,\ldots,N\); by the finite pigeonhole theorem some \(0\le i<j\le N\) have the same original node. Determinism forces an eventual orbit cycle of positive period \(j-i\); since no earlier terminal state was visited, the repeated interval consists entirely of known-target edges.

These three cases are exhaustive and disjoint as observations; a repeated source is a cycle receipt **only if all intervening source edges are `knownTarget`**, never by casting a dead-end or an outside token to a self-loop.

**Existing kernel reuse:** `PartialAtDepth`, `partialAtEveryFiniteDepth`, `partialIterateAppend`, `partialDeadEndPersistsAfterDiscovery`, `partialUnresolvedPersistsAfterDiscovery` in `IbrahimPartialFirstLinkSemanticsExact`, and the finite-pigeonhole construction from `IbrahimFinitePigeonholeProducerExact`.

**Implemented Agda chain (M3):** `continuingMatchesTotal`, `continuingPrefix`, and `finitePartialFLNClassifiesOrTerminates` in `IbrahimFinitePartialGlobalTrichotomyExact.agda`, returning an explicit `FinitePartialOutcome`: stopped dead-end + depth, missing outside token + depth, or positive known-edge cycle + entry/period. The outside type remains unconstrained (need not be finite), and terminal observations are never coerced to self-loops.

**Status:** mathematical proof, Python `trace_start`/`check_trace` algorithms, exhaustive finite checks, and Agda formalization **kernel-accepted at commit `51dcb745ad`** (**M3 CLOSED**).

## M4 — the correct executable JSON ↔ Agda proof statement

The unconstrained theorem name `pythonCertificateCheckerSoundAndComplete` is **too broad** if interpreted as complete for every arbitrary `CheckedEdgePath`. Counterexample: on the one-node graph (f(a)=a), Agda has a two-step `CheckedEdgePath f 2 a a`, but Python correctly rejects a receipt with `trace=["a","a"]` because its wire format requires a *simple* prefix through the **first** repeat. Both semantics can be correct without a bijection between arbitrary paths and canonical first-repeat receipts.

**Executable normal form:** strict UTF-8 JSON with no repeated object keys, NaN/Infinity or unpaired surrogate; declared original graph digest, exact source count and one sorted trace per source; each source is in-carrier; `trace[0]=start`; all listed source vertices are pairwise distinct; each consecutive edge is an actual original `next` edge; a dead end has a genuine null edge, an unresolved target is missing from the source carrier (with exact token retained), or a cycle closes exactly from the last source to the first repeated `trace[entry_index]` with a non-Boolean integer index and canonical least-title rotation. No unknown ↔ dead-end coercion. `node_count=true` is **not** the integer 1.

**Correct M4 proof targets:**

- `jsonDecoderRejectsAmbiguousWireObjects`: parser-model rejection of duplicates and non-JSON numbers; a Python test is evidence of an implementation, not an Agda parser theorem.
- `verifiedNormalFormYieldsCheckedEdgePath`: from a **typed strict decoded normal-form receipt** and original next edges, build nested `Trace.pathEdge` equalities, then a typed `AcceptedCycleTrace` for cycles. The existing Agda generator already creates literal `pathEdge refl` for the finite Figure 2–4 fixture, checked at 91dfccd.
- `normalFormReceiptAcceptedByReferenceChecker`: completeness **restricted to the same canonical first-repeat format** plus source-count/hash predicates, never arbitrary `CheckedEdgePath`.
- `pythonJsonCertificateDecodesToCheckedEdgePath`: true global implementation theorem requires a formally specified byte decoder and an implementation-to-model refinement/verified extraction or equivalent verified interpreter. Neither generated `refl` nor randomized Python tests proves CPython globally.
- `sourceBoundJsonAgdaCertificateMatchesOriginalBytes`: separate source-manifest verification and kernel replay for *the same acquired bytes*, not fabricated source/provenance metadata.

**Status:** strict executable JSON acceptance strengthened and paired negative tests source-written; per-instance generated Agda kernel proofs accepted at prior 91dfccd; **universal source-language implementation and original-byte correspondence remain OPEN**.

## Acceptance and actual release cut

1. **DASHI #1505:** on the current new head run `python3 -m unittest discover -s tests -p 'test_ibrahim*.py' -v`, then `NO_TMUX=1 ./scripts/check_ibrahim_fln_maxcut.sh`. The 13-target checked baseline stays pinned at `91dfccd`; the new Python changes require their own receipt. Formal M2/M3 above close only when kernel-accepted *new* Agda declarations are included in the 13-target checker.
2. **ITIR #14:** retain the 120/120+native offline acceptance at `a22995e`. The next **physical** cut is exact original `.bin` ranges ↔ immutable HF shard bytes ↔ native decoded A1/A2 adjacency with `--source-bin`; do not conflate this with Wikipedia's article first link.
3. **SLR/SensibLaw:** native GUID/P14143/P854 and actual revision-pin source span, authorised consumer review, S29 persisted/reloaded receipts are distinct OPEN obligations.
4. **Historical/modern data:** original producer/dump reconstruction and modern multilingual census remain empirical OPEN, not consequences of finite graph theory.

**Gate policy:** SOURCE-WRITTEN, mathematical argument, executable finite test and actual Agda kernel-accepted theorem are four different statuses. A check only advances the exact source SHA actually run.
