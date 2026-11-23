# 23 November — Formal-first P0 theorem programme (CURRENT; supersedes execution-first priorities)

**Decision:** Deprioritise additional learner GPU microbenchmarks and fixed-horizon grokking reruns. Existing Leech PR #5 physical host acceptance: four-arm R4 FP64 20/20 matched training, differential VJP at most 4.68e-16 gradient difference, step-20 parameter difference 2.07e-11 at tolerance 1e-10; routing peak allocation -20.5%, routing backward -15.5%. These are scoped physical evidence, NOT kernel proofs or learned geometry. Original nine-point modular learner remains 3/8 training-fit after 200 updates and cannot be described as pre-grokking memorisation. Leech PR #5 currently 5a09681c. Original checkpoint/SLR fitted assets and F5 remain unopened.

## P0-F1 — new universal future-trace characterization (formal source written)

New Agda module `DASHI/Cognition/PNF/X369InputIndexedFutureConsumerExact.agda` extends existing autonomous `X369ConsumerSufficientCompressionNoGoExact.futureConsumerSufficiency` to a **family of original transitions indexed by arbitrary future activations/interventions**. The `trace` includes original observables before each transition.

For original state `h`, admissible input `u`, observable `O_u(h)` and transition `T_u(h)`, define

    h ≈ h'  iff  for EVERY finite input word w,
                     Trace(w,h) = Trace(w,h').

The new proof defines `TraceEquivalent` and establishes:
1. `inputIndexedTraceDescent`: if `E(h)=E(h')` implies `O_u(h)=O_u(h')` and `E(T_u(h))=E(T_u(h'))` for EVERY u, induction proves equal output traces for EVERY finite word.
2. `traceEquivalentObserves`: trace equivalence implies one-step output equality for each u (head of length-one trace).
3. `traceEquivalentTransitions`: trace equivalence is preserved after the transition at every u (tail of prefixed trace).
4. `everyStableCodecFibreIsTraceEquivalent`: any sound encoder fibre refines this full future-trace relation. This is the **maximally permissive behavioural equivalence** for deterministic original observations under all admissible inputs; NOT a claim of a finite-dimensional, computable or byte-minimal codec.
5. `futureSeparationRefutesCodec`: one source-valid future word distinguishing two states that share a code refutes its proposed all-future sufficiency.

The code is self-contained, uses primitive List/equality and ⊥, and **has not been checked by Agda 2.9 kernel**. No assumption of a learned task-phase action, actual HIP bit identity, full original R4 transition fidelity, checkpoint authentication or fitted generalization is made. Source-specific formal instantiation of `T_u`/`O_u` with original selected TopK, signed orientation, FFN, transition and inactive E histories is P0-F2, not an automatic consequence of the abstract theorem.

## P0-F2 — original R4 source-specific fibre intersection (OPEN)

Existing roadmap `X369R4HistoryObservabilityRankMaxCut20261117.md` proves `det(M_w)=d q(w)` and `M_w^T M_w=qI+(d²-q)J/3` with singular values |d|, sqrt(q), sqrt(q). Generic d≠0 and q>0 means **directed-score history rank 3**. Rank 2 only with d=0,q>0; rank 1 only when ws=wf=wr≠0. Do not confuse two directed FEATURE channels plus supplied DC with two-dimensional full recurrent STATE sufficiency.

Even rank-2 directed-score equivalence does not suffice for the source C2 baseline `v·abs(h)`. More strongly, existing signed pair `h+=t(1,1,1)`, `h-=-t(1,1,1)` for a zero-sum directed head has identical C3 and absolute C2 router scores, yet selectable FFN/GELU or transition can separate them. Reuse `X369R4SourceReceiptAndHistoryFibreMaxCut20261117.md` and `X369R4GELUParityChartHistoryMaxCut20261117.md`; no duplicate carrier. Required: prove intersection of route, output, orientation, transition, inactive-history and externally typed task consumers, then prove or refute fibre stability for each original input branch including ties/guards. Existing physical selected-only future [0,2] vs [0,3] witness in FP32/FP64 is a finite no-go control, not a general positive quotient.

## P0-F3 — exact relative-decision and error-transport theorem (OPEN)

Reuse `X369R4RelativeErrorMaxCut20261117.md`, `X369QuantizedRouterDecisionMarginExact.agda`, `LeechLayerErrorTransportExact.agda` and the *original* C2 q-gate/chart owners. Prove strict TopK membership **and internal selected-slot order**, shift-invariant selected softmax error via oscillation, signed GELU chart jump `2 E_F`, transition Lipschitz/error transport and Nat cell admission. Separate ideal-real polynomial identities from prospective hardware roundoff. No independent certified native error budgets exist; retrospective 6/6 TopK observations at 1/256 are not universal.

## P0-F4 — proved 369 learning explanation (OPEN)

Preserve distinct propositions: full-channel gauge rotation does not add capacity; centered two-coordinate C3 quotient is consumer-indexed; gradient sufficiency requires equality of relevant derivatives in a neighbourhood (the aggregate-DC point equality counterexample has reverse-weight gradient (-3,2)); future sufficiency requires indexed trace congruence; invariant-only encoders cannot preserve a moving C3 label. Prove a labelled task action intertwiner BEFORE claiming that neural geometry explains modular generalisation. For genuine grokking require observed training fit followed by delayed independently held-out correctness; no such result yet.

## P0-F5 — transitive Agda acceptance and owned fitted model (OPEN)

Kernel-check the new module with current original Agda 2.9 import graph, original finite G0/C0/N0/F0 donors, TOE imports; no unverified postulates and no CI substitution. Then recover *original* fitted R4 assets through the existing source-bound producer; never fabricate missing checkpoints, run F5, modify original fingerprint owners or relabel synthetic mathematical examples as fitted.

**Execution priority:** F1 kernel check → F2 source-specific positive/no-go proof → F3 guarded consumer error theorem → F4 learning-law explanation; use GPU only as a later independent witness. Original Leech-LILA attribution: Anatolii Kornienko.

---

## 20 November — R1 repository recovery update

Leech PR #5 now at `678b5e7dda932e56f10626ecc7ece6719f202494`. Detached `a77bf4d` was unavailable (GitHub 422); documented corrections reconstructed in commits 506680b8, 139fc645 and 678b5e7d. Original model blob verified `a2a250462ce8e663591cd8a8f784fad9bde1b15d`. R1 repository recovery complete for documented changes; exact detached-tree identity and fresh execution remain unverified. Original fitted artifacts not present in the inspected tracked Leech tree. R2 remains OPEN pending owned checkpoint, repair receipt, native R1 JSONL/summary, tokenizer, config and fitted delta. SLR C4.04a relation/mention integration is separate upstream work, not replacement input or semantic admission for R4. No F5 access or kernel claim.

---

## 20 November 2026 — CURRENT acceptance ledger (supersedes historical status below)

Source: supplied local execution report, lines 168–196; results reported by local operator, not independently rerun by this documentation update. DASHI base `5283e6db84eafb5bdabfd066c3ac422c15f67286`; LeechTransformer tested base `8d8f627f8bac4d7c7440fe23beea2d21d7818719`. Precision/doc fix reported committed on detached HEAD `a77bf4d`; PR #5 still on tested base when audited. Do not claim detached commit is landed.

| Gate | Current status |
|---|---|
| Exact full-load SymPy envelope | PASS 53/53 reported |
| Original-source native synthetic CPU fixture | PASS reported; 10/10 strict boundary probes and former tied-fixture rejection |
| Four-load reset / fixed-route control | PASS reported; native Nat [0,2,9,0], fixed route monotone |
| Same-clock two-prefix history probe | PASS reported; native Nat [0,9] |
| Both standalone synthetic checkpoint probe CLIs | PASS reported |
| Projected router score weld | PASS 6/6 reported after double().mean() precision fix |
| C2 quality max-cut and portable CPU source contracts | PASS reported, exit 0 |
| Actual repaired C2 + fitted R4 delta restoration and native SLR development replay | OPEN |
| Independently certified score/response floating error intervals and Nat margins | OPEN |
| Agda 2.9 transitive kernel/TOE acceptance | OPEN |
| Fitted-model response, heldout semantics and general on-policy hysteresis | OPEN |

Active source API: unchanged two-value `select_source_experts`, original blob `a2a250462ce8e663591cd8a8f784fad9bde1b15d`; scoped `TorchDispatchMode` observer only. Corrected synthetic expert 3 slope/bias = (11,-16); former (10,-13) is a negative control, not an accepted deterministic history witness. Collapse is for t > 14/5; at equality the cutoff tie is ambiguous. The crest is at 19/9. Fixed-route intervention establishes fixture-specific mechanism discrimination only, not a universal fitted-model causal theorem. The double-precision mean fix improves the audit computation; it is not a general proof of floating-point exactness.

Next cut: land/verify the detached Leech fix without overwriting branch work; recover the original owned input assets; execute the strict fitted-delta orchestrator and independent replay; certify numerical margins; kernel-check the actual Agda imports. Preserve Anatolii Kornienko attribution, development-only admission and F5 exclusion.

All dated sections below are historical evidence, not alternative active instructions. Earlier OPEN native-synthetic execution statuses are superseded by this ledger; fitted-source and kernel gates remain open.

---

## 17 November — one-entry fitted R4 original-source acceptance workflow

LeechTransformer PR #5 now has a single source
orchestrator `scripts/run_x369_r4_original_kink_observation.py`
and runbook `docs/x369_r4_native_kink_probe.md`.
It does NOT fabricate a complete R4 checkpoint
or an original source history. It checks the
repaired bounded guarded C2 checkpoint, original
repair receipt, exact native SLR JSONL, R1 summary,
SentencePiece tokenizer, and a saved original
R4 source-bound fitted delta with actual expected
SHA256 values BEFORE creating output.
Then it invokes ORIGINAL producers:

1. `verify_trained_federated_moe.checkpoint_parts`/
   `infer_config` and
   `x369_fair_c3_residual.restore_residual_delta`
   to reconstruct the original full R4 model,
   retaining the unchanged source geometry SHA;
2. the native DEVELOPMENT-only original
   `LeechGPT(student_only=True)` forward,
   observing a named original MoE layer's
   actual x and entire pre-step all-E history
   at a chosen document/token; this is admitted
   only when the independent reconstructed MoE
   `step` replay is BITWISE equal;
3. the original four-load route/FFN response and
   matched forced-pair counterfactual probe,
   using a scoped dispatcher topk observer
   rather than changing original source;
4. the same-clock two-prefix original
   recurrent history probe and fixed-pair ablation;
5. a final byte-bound summary reporting
   **positive OR negative** fitted-model response
   outcomes, with exact source module/probe/result
   SHA256 and explicitly false analytic/physical/
   semantic/hysteresis/Agda promotion flags.

Both original R4 probes verify the same restored
layer checkpoint/trace via the shared sidecar
`verify_x369_r4_source_probe_authority.py`.
The source trace four load multipliers must include
**1**—the actually observed original source
activation. Other chosen activation loads
are clearly COUNTERFACTUAL, not four naturally
measured SLR physiological or cognitive states.

Source code/fitted R4 geometry owner:
`models/history_orbit_moe.py` restored to its
original byte blob `a2a250462ce8e663591cd8a8f784fad9bde1b15d`.
A previous optional return_logits mutation is
reverted; exact R4 source fingerprint
preservation matters for existing saved deltas.

**Executed independently locally:** the full
corrected SymPy full-load checker 53/53;
scoped Torch topk observation 3/3;
native dtype JSON binary roundtrips 2/2.
Full source repo native CPU execution,
real model/restored-delta development
observation and new Agda imports have
NOT run in this environment because the
original owned files are unavailable.
Therefore the genuine model-shape/quality/
hysteresis and Agda golden gates remain OPEN.
No positive fitted result was invented.

---

## 17 November — latest source-integrity restoration, exact execution and fitted-source producer

**This section SUPERSEDES earlier proposed direct modification of the
original `HistoryOrbitMoE.select_source_experts` return signature.**
The original `models/history_orbit_moe.py` bytes are now restored to
Git blob `a2a250462ce8e663591cd8a8f784fad9bde1b15d`,
because the preexisting `r4_geometry_source_fingerprint()`
includes those exact bytes and already-issued original R4
trained residual delta payloads are source-hash-bound.
The transient opt-in three-value return interface would
have invalidated their producer identity. The ACTUAL original
two-value source API remains unchanged.

**Source observation without changing model or training assets:**
LeechTransformer PR #5 now owns
`scripts/observe_x369_r4_original_topk.py`.
A scoped `TorchDispatchMode` intercepts the existing
original `aten.topk` input and records its actual
full E learned logits while the unchanged original
`select_source_experts` executes. It does not compute
a replacement router. It rejects missing/duplicate
topk calls, mismatched native softmax, and opt-in
sort fallback. Local CPU PyTorch 2.10 isolated
observer positive/negative controls: **3/3 PASS**.

**Original fitted weights/source state route:**
`scripts/export_x369_r4_restored_moe_layer.py`
reuses existing original
`verify_trained_federated_moe.checkpoint_parts`/
`infer_config` and
`x369_fair_c3_residual.restore_residual_delta`
to bind the repaired R64 guarded C2 source checkpoint,
repair receipt, native R1/SLR JSONL hash, and saved
fitted R4 source-bound residual delta; then it exports
a strictly restored selected `HistoryOrbitMoE`
module and nonpersistent history-cap receipt.

Optional `scripts/capture_x369_r4_original_slr_state.py`
uses the ORIGINAL
`validated_r1_summary`, `load_docs`,
`validate_source_docs` and full `LeechGPT`
student-only forward on a chosen original
DEVELOPMENT document/token; it observes
the exact pre-step activation and entire
all-E history of one selected MoE layer,
without replacing the source computation.
An independently strictly reloaded
module must replay the original full-model
step BITWISE before the checkpoint +
probe-input JSON are emitted.
The activation input is actually observed
at multiplier `1`; other four-load
multipliers are controlled COUNTERFACTUAL
interventions, not corpus observations.

Both Leech source CPU probes now import
`verify_x369_r4_source_probe_authority.py`
to bind a genuine native source trace by
actual module checkpoint bytes, source probe
JSON bytes, original C2/delta/SLR identity,
selected document, model config/dtype,
nonpersistent history cap, and reconstituted
full all-E history SHA. A native R1/SLR
source trace without its matching exporter
receipt is REFUSED. The synthetic
architectural fixture is explicitly
unauthenticated, not silently promoted.

**Directly executed this round:** the
full source mathematical script
`check_x369_r4_full_load_kink_envelope_sympy.py`
failed when first attempted due to a
fragile premature `simplify(diff)` leading
to unsimplified cosh forms; fixed,
committed, independently rerun under
SymPy 1.14, **53/53 PASS**, with
`t_crest=19/9`, response
`0.969065029508046`,
source cutoff-tie `t=14/5`,
left response `0.354343693774205`,
right response 0.
The earlier partial **27-check** figure
must not be used as the executed file
total. Native source JSON float32/float64
roundtrips: **2/2 PASS**; isolated
original-shape TorchDispatch
observer: **3/3 CPU checks PASS**.

**Remaining separate OPEN proof gates:**
full original Leech native fixture execution
with exact source checkout; real source
repaired C2+R4 delta restoration and
development trace with owned bytes;
calibrated true original Torch floating
error intervals/Nat-cell stability;
real fitted-model shape and matched
counterfactual; nontrivial task-quality
and heldout semantic acceptance;
on-policy hysteresis and independent
original Agda kernel acceptance. These
have NOT been passed or inferred.

---

## 17 November — direct executable full-load SymPy acceptance correction

The exact committed `scripts/check_x369_r4_full_load_kink_envelope_sympy.py`
was independently reopened and reproduced **as a complete script**
under SymPy 1.14 and Python 3 in the local container this round.
The previous script FAILS at the first derivative assertion because
`simplify(diff(logistic))` rewrites the derivative to `cosh`
and a second `simplify` fails to prove an otherwise true
logistic equality. This is a proof-check implementation bug,
not evidence of a mathematical counterexample.

Repair committed on PR #1526: differentiate without
premature simplification and certify the exact logistic
derivative identities via
`cancel(together(diff(y,t)-a*y*(1-y))) == 0`.
The complete repaired file was rerun locally:

    X369_R4_FULL_LOAD_ENVELOPE_SYMPY_PASS 53
    CREST 19/9 response 0.969065029508046
    FINAL_TOPK_TIE 14/5 left 0.354343693774205 right 0

**53/53 checks PASS**, not the previous **27**-check
provisional figure. This counts all six strict routing
regions, selected-score comparisons, source response
formulas, derivatives, crest, tie cases, Nat sample
cells and fixed-route monotonicity.
The next cross-module source receipt and exact original
PyTorch fixture are separate gates. No Agda kernel
or fitted checkpoint execution is inferred.

---



## 17 Nov exact original full nonnegative-load routing envelope

The latest mathematical implementation moves beyond only four
test loads and closes the strict **ideal-real source-formula**
piecewise route/response map for the corrected e3=(11,-16)
synthetic fixture:
`scripts/check_x369_r4_full_load_kink_envelope_sympy.py`.

Original four learned affine logits:
`(8,3+4t,-11+9t,-16+11t)`.
Five positive exact rational critical loads:
`5/4,19/9,5/2,19/7,14/5`.
Across their six open intervals, the uniquely ordered
source top2 are:
`(0,1),(1,0),(1,2),(1,3),(3,1),(3,2)`.
Only expert1 emits a nonzero scalar, so the
exact source response is piecewise:

    sigmoid(4t-5), sigmoid(4t-5),
    sigmoid(14-5t),
    sigmoid(19-7t), sigmoid(19-7t), 0.

The first derivative is positive until the
continuous apex at t=19/9 with exact response
`sigmoid(31/9)≈0.969065`; strictly negative
until t=14/5. At t=14/5 the second-slot
original topk cutoff ties a positive-output
expert with a zero-output expert, so the
scalar selected output is genuinely
**source tie-ambiguous** at that exact
point. Left response ≈0.354344, right=0.
Do NOT infer a unique tie-time output.

A source-level matched fixed pair (0,1)
retains strictly increasing
`sigmoid(4t-5)` across the full ray,
providing a global architectural
negative control for overload decline
without expert replacement.
No ordinary scalar GELU nonmonotonicity,
new attenuation gate, learning-result or
biology is asserted by this fixture.

Independent local symbolic
endpoint/source-response audit:
**27 PASS**; 10 extra near-boundary
±10^-4 original affine-score checks PASS.
The original native Leech CPU fixture
now contains corresponding **ten**
source `torch.topk` strict-margin
probes, but their exact committed
native execution remains OPEN.
This exact all-load source-algebra
extension is NOT a continuous
Agda real analytic/cdf theorem.


## 17 Nov topk strict-margin remediation + matched history routing ablation

This section supersedes any earlier **second-step** claim made
with expert-3 history slope 10 and bias -13. That source
parameter pair led to a topk cutoff TIE and was NOT an
authenticated ordered selected pair at the common probe.
Current only repaired expert3: `(s3,b3)=(11,-16)`.
All six tested original score states (four independent
reset loads plus two distinct first-step prefixes at the
same second-step load) now have uniquely determined
ordered topk2 and strictly positive score margins.
Independent local six-case source-formula test: **6 PASS**.

There is also a NEW paired causal-discriminator
fixture, using the ORIGINAL source `execute_selected`
intervention at the common load/clock:
- Path A prefix load0 -> source selected (0,2),
  original selected output Nat0;
- Path B prefix load3 -> source selected (1,0),
  original selected output Nat9;
- Force the original second-step pair (0,2) in
  BOTH paths, with each path's original source
  logits, selected-history values, and softmax
  recomputed for that pair -> Nat (0,0).

Independent local same-source algebra checked the
two fixed-pair outcomes: **2 PASS**. This
identifies selected-set replacement as sufficient
for the discrepancy in the disclosed architecture
fixture, while making NO claim that all fitted
history dependence must be caused by topk or
that holding IDs fixed always removes FFN effects.

The EXISTING mathematical abstraction
`DASHI.Core.IntersectionalNonFactorability`
is reused in
`DASHI/Cognition/PNF/X369R4HistoryLoadNonFactorabilityExact.agda`:
`sourceFixtureResponseCannotFactorThroughLoad`
is the negative load-only theorem, while
`fixedProbePairDoesFactorThroughCurrentLoad`
is the positive forced-selection control.
Both are imported into the same two TOE entry
points. No duplicate non-factorability carrier
or new broad hysteresis theory is invented.

**Leech original source implementation:**
`scripts/probe_x369_r4_kink_checkpoint.py` now
owns the COMMON `strict_source_order_margin`
function for prefix/probe and reset four-load
checks; no source native claim is accepted
at ties. Its code is reused by
`scripts/probe_x369_r4_history_path_dependence.py`.
The latter now executes a fixed expert pair
at the SECOND step through the real
`HistoryOrbitMoE.execute_selected`, records
both original and forced scores and histories,
and labels the counterfactual as a source
intervention rather than fitted causal proof.
The native fixture:
1. reconstructs the OLD tied source configuration
   and REQUIRES rejection;
2. checks the new strict positive margins;
3. emits a source-valid synthetic checkpoint;
4. launches BOTH original CLI producers as
   subprocesses; and
5. reloads their JSON receipts, verifying
   SHA identity, original Nat0-2-9-0, same-clock
   native Nat0/9 and fixed-pair Nat0/0.

**Acceptance honesty:** independent local
exact source-formula checks PASS
(6 strict reset/history cases and
2 fixed-pair discriminators). The exact
native original PyTorch GitHub scripts,
the fitted checkpoint and all new Agda/TOE
kernel imports remain UNEXECUTED in this
container session. Consequently the
source-native execution acceptance
and real-model behavioral/hysteresis
gates are OPEN.


## 17 November strict-topk correction and executable closure route

**Mandatory correction to EARLIER historical paragraphs in this
roadmap:** the previous e3 configuration `s3=10, b3=-13`
produced a **TIE** at the second-step history probe after the
low-load prefix: `(8,3,7,7)`. Because the original source
uses `torch.topk`, expert 2 vs expert 3 could be chosen
for the second selected slot; source deterministic selection
was NOT established for that earlier fixture.
This is an actual logical error in the old history claim,
not a cosmetic numerical refinement.

**Repaired original source-shaped fixture** changes ONLY e3 to
`s3=11, b3=-16`. The corrected four original
reset-state score vectors at loads 0,1,2,3 are:

    (8,3,-11,-16), (8,7,-2,-5),
    (8,11,7,6), (8,15,16,17).

They retain the strict source topk sequence
`(0,1),(0,1),(1,0),(3,2)`, the same selected
scalar responses
`1/(1+e^5),1/(1+e),1/(1+e^-3),0`, and
canonical old `ResponseKink` Nat `(0,2,9,0)`.
The forced pair (0,1) still has the strictly
monotone source response `sigmoid(4t-5)`.

The corrected two original step histories share
probe load 2 and clock index 1:
- prefix load0 -> second-step logits `(8,3,7,6)`;
  unique top2 `(0,2)`, Nat0;
- prefix load3 -> second-step logits
  `(8,11,-11,-16)`; unique top2 `(1,0)`, Nat9.

An independent LOCAL six-case Python source-formula
audit checked all four reset-state and both
same-clock cases with strictly positive
selected-slot and selected/outside gaps:
**6/6 PASS**. The old tied witness must NOT
be promoted by relying on Python's sorting
order or CPU/GPU `torch.topk` tie behaviour.

**Executable implementation advances in original
LeechTransformer PR #5:**
- The existing reset-state checkpoint source producer
  now uses the shared `strict_source_order_margin`
  function to fail closed on source topk ties and
  record the minimum observed original score gaps.
- The same-clock history probe REUSES that same
  source margin helper at both prefix and
  probe steps, instead of duplicating the logic.
- The actual source-native synthetic regression
  now creates the repaired source-valid module
  weights, checks native `step`/
  `execute_selected` parity and source history,
  emits a genuine synthetic state_dict, then
  **runs BOTH original checkpoint and history CLI
  producers via subprocess**, reopens their
  JSON outputs and checks checkpoint SHA256,
  Nat `(0,2,9,0)`, same-clock Nat `(0,9)`,
  strict prefix/probe score margins and explicit
  non-certification of trained-model/float/
  general hysteresis conclusions.
- The previous JSON numeric-string parser fix,
  required original nonpersistent `history_cap`,
  controlled `dtype` and integer scale, and
  same-Nat forced-route comparison remain.

**Still-open acceptance:** these original
GitHub-native Torch scripts have been
source-written/committed but the complete
committed original source bundle has NOT
been run locally in this session because
the original repository checkout was
not accessible in this container.
The independent six-case exact-formula
audit is NOT a substitute for running
the actual source Torch model.
Agda kernel acceptance, real trained
checkpoint/source-history provenance,
independent numeric source error margins,
heldout semantic tests and general
hysteresis remain OPEN.
# X369 P0 — C3 gauge versus consumer-sufficient compression (17 Nov 2026)

**Owner:** DASHI finite formalism. **Companion:** LeechTransformer PR #5.
**Proof file:** `DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda`.
**Status:** Agda source committed; no Agda executable/kernel runner available in
the present environment. These are *proof terms proposed for kernel checking*,
not a claim of Agda 2.9 acceptance. Do not merge into Golden TOE imports
before checking. No Python implementation or new GPU experiment was added.

## Correction to the research claim

A full three-channel C3 action `T(Rx,h)=P T(x,h)` with an
unrestricted full-channel head has a change-of-basis gauge:
`head'(Pt)=head(t)`. Therefore **fixed rotation by itself adds no
unrestricted-head expressivity**. This says NOTHING about:

1. a smaller or quantised source code `E : X -> Q`;
2. preservation of a particular consumer `C : X -> Y`;
3. preservation of a future consumer after original state transition;
4. actual description length, bit width, runtime, bandwidth or energy;
5. restricted/structured heads with fewer independent weights;
6. independent semantic action and original trained model refinement.

The exact consumer-relative acceptance gate is already in
`DASHI/Core/ConsumerDescentMinimalObserverExact.agda`:

    E(x) = E(y)  ->  C(x) = C(y).

This is distinct from lossless reconstruction `decode(E(x))=x`.
With a section, fibre constancy gives explicit factorisation; the
canonical consumer itself is the least informative sufficient observer
in the existing observer refinement order.

## New proof targets and source bodies

### G0: full-channel gauge equivalence
A `Triple A` with explicit `rotate`/`unrotate`, two inverse laws,
`rotateCubed` and bidirectional **all-head** transport.
Every full-channel linear head is included; the result does not
say a constrained, low-rank, quantised or cheap head is unchanged.

### C0: exact non-injective C3 compression witness
`TaggedPhase=(phase in Z3, tag in Bool)`. `phaseCodec` retains only
the phase, discarding the tag. `codecSufficientForPhase` proves
that the phase consumer is exactly preserved. `rawWitnessesNotEqual`
shows that two different original states really collide in the code.
`phaseCodecIntertwinesC3` proves that this *non-injective* code still
retains the nontrivial phase action. It is a finite cardinality witness
(6 explicit fine combinations versus 3 coarse phase labels), NOT
a real packet byte count or universal 2:1 physical compression gain.

### N0: invariant-only no-go, correctly scoped
For any actual witness state `x`, an encoding invariant under an
action is not sufficient for a consumer whose output advances
by a fixed-point-free C3 permutation. The generic
`invariantCodecNotSufficientForChangingConsumer` is specialised
to the EXISTING grokking nine-pair task with
`modularGrokkingInvariantCodeNoGo`.

This does not contradict C0: the phase codec **transforms
equivariantly**, it is not invariant. A lossless phase in a
small carrier can be sufficient. Discarding the phase while
requiring the consumer to distinguish the three phases cannot.

### F0: current and future consumer exactness
`fullReconstructionImpliesConsumerSufficiency` proves full raw
round-trip sufficient for every consumer, while C0 proves it is
not necessary for a *specified present* consumer.

`futureConsumerSufficiency` proves an exact induction:
if the encoding is consumer-sufficient now AND the encoding
fibres are stable under the original transition, the encoding
is sufficient for the consumer after every finite number
of transitions. This does not pretend that one-time readout
equivalence implies transition stability.

`encodedTransitionWeldImpliesFibreStability` and
`compressedTransitionPreservesEveryFutureConsumer`
close the POSITIVE same-state diagram:
`E(step(x)) = stepCode(E(x))` together with current
consumer-sufficiency implies sufficiency after every
finite iterate. The exact source Leech/FFN/History MoE
transition-to-code weld is still an independent obligation.

`tagSensitiveStepBreaksPhaseFibre` and
`presentConsumerSufficientFutureConsumerNot` construct a
counterexample: the dropped tag changes the next phase,
so the currently lossless phase quotient is now insufficient
for the future phase consumer. The correct repair is a retained
history/tag residual, a state-dependent transition codec,
or a proof the chosen consumer never observes the lost fibre.

## P0 fixed-width quantization is now an exact finite theorem target

The new module also defines `oneBitCannotPreserveThreePhaseConsumer`
using an exhaustive Agda distinction of all three independently
observable phases: an encoder into ONE Bool bit must collide on two
different required output labels and therefore cannot be
consumer-sufficient. In contrast, `phaseToTwoBits` and
`twoBitsToPhase` give an exact zero-error roundtrip for all
three values using TWO Bool bits; `twoBitsSufficientForPhase`
retains consumer sufficiency on the full six tagged input states
while `twoBitsDiscardTheIrrelevantTag` demonstrates real
non-injectivity on the raw carrier. Hence the MINIMUM FIXED
ZERO-ERROR BIT WIDTH of this finite three-label consumer is 2.
This is not a universal Shannon-rate theorem, source-bit codec,
model quantisation benchmark, or 2:1 measured Leech compression.

## Existing owners to reuse rather than duplicate

- `DASHI/Core/ConsumerDescentMinimalObserverExact.agda`:
  fibre constancy, factorisation, least consumer-sufficient observer.
- `DASHI/Core/SectionedProjectionProvenanceBridgeExact.agda`:
  section and residual reopening, consumer vs full reconstruction.
- `DASHI/Core/ConsumerQuotientBaseChangeExact.agda`:
  consumer preservation under context/restriction changes.
- `DASHI/Reasoning/LeechJointStateConsumerQuotientExact.agda`:
  selected expert/history sufficient consumer, inactive-state boundary.
- `DASHI/Reasoning/FibreRoutingCompressionLadderExact.agda`:
  admission before MDL/Pareto comparisons, local relation-fibre repair.
- `DASHI/Core/ConsumerRelativeApproximateFidelityBridgeExact.agda`:
  approximation margins; do not equate approximate state error
  with classification safety.
- `DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda` and
  `GrokkingEquivarianceDefectGeometryExact.agda`: action 0-vs-2
  rule/memorizer exact finite regression.
- `DASHI/Reasoning/TrialecticBoundaryFaceNonfactorabilityExact.agda`:
  missing triadic face cannot be reconstructed from three edge labels.
- `DASHI/Cognition/PNF/X369OriginalDirectedTriadC3PolynomialCandidate.agda`:
  source directed 2q(x)q(h), mixed mask identities (candidate,
  separate selected-leaf Agda kernel receipt still needed).

## Operational proof check (NOT executed in this context)

From the existing repo clone with its pinned Agda 2.9 toolchain:

```sh
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda
```

Check imported original Agda modules and all referenced declarations
with the exact repository toolchain; fix any elaboration errors in
this original branch, then record exact SHA, checker version, logs
and selected import closure before golden promotion.

## Highest-alpha remaining proof obligations

1. **Costed minimal sufficient codec:** instantiate existing
   consumer-MDL and Pareto owners with a *real original LILA*
   codec/precision/capacity cost, rather than synthetic tag count.
2. **Restricted-head rank:** prove conditions under which a
   compressed/equivariant readout retains *specific consumer*
   decisions while reducing parameter/bit cost; unrestricted
   gauge is an insufficient comparator.
3. **Finite-precision margin:** instantiate existing approximate
   fidelity theorem on the selected source top-k and output
   decision margins with actual roundoff/quantization bounds.
4. **Future recurrent state:** weld the abstract transition
   stability premise to selected expert histories, routing
   ties, source reactivation and inactive-history owner; provide
   counterexample where a discarded fibre is future relevant.
5. **Grokking/semantic phase:** independent learned input/label
   action and heldout composition; the finite task no-go alone
   is not a trained model theorem.
6. **Proof acceptance:** run the pinned checker; no kernel
   result is fabricated here.

**Research decision:** preserve consumer-relevant invariant amplitude,
equivariant phase and necessary face/history residuals. Minimise
the *entire admitted code+decoder+state-transition cost*, not raw
activation dimension or a formally equivalent change of basis.
No original LILA performance, codec ratio or semantic steering is
claimed before source-backed evidence.


## P0 original Leech router: a *conditional* 3-to-2 directed-channel code

New proposed proof module:
`DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda`.

It uses the ORIGINAL source owner
`X369OriginalDirectedTriadC3PolynomialCandidate` for
`originalSelf`, `originalCyclic`, `originalAnticyclic`.
The three directed channels of x=(a,b,c), h=(A,B,C) obey

    self + forward + reverse
      = (a+b+c)(A+B+C).

A 6-variable `Data.Integer.Solver` proof is supplied;
the inverse reconstruction is a 3-variable solver proof.
Consequently **if the consumer already knows the sourceDC
product**, two directed scalars plus THAT externally
supplied side information exactly reconstruct all three.
The code `encodeDirectedTwo` and decoder
`decodeDirectedWithKnownDC` form a constructive
full-channel recovery under that precondition.

The essential counterexample is ALSO ORIGINAL SOURCE, not
a synthetic arbitrary triple: x=(1,0,0) with h=(0,0,0)
vs h=(0,0,1) produces directed (0,0,0) vs (0,0,1).
The retained first two scalars collide, while an original
consumer observing reverse distinguishes them. The
`twoDirectedWithoutDCNotSufficient` proof prohibits an
unqualified 3→2 data-loss claim. Conversely, every
consumer that factors through the two kept channels is
exactly sufficient.

This exhibits the real research boundary:
an already-available shared DC/summary enables a
relative-channel reduction; paying to COMPUTE or STORE
one extra side scalar per expert could erase the savings.
It does NOT certify an original memory/compute/latency
benefit. Compare exact source tensor reuse, per-expert
history availability, quantizer precision, provenance,
decoding arithmetic and future-state admission.

Check this additional new head with pinned Agda:

```sh
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda
```

Both new files are unverified proof-source proposals in
this environment, not kernel-accepted theorems.


## 17 Nov continuation: executable SymPy CI stand-in and original-source score/MDL cuts

`scripts/check_x369_p0_sympy_standin.sh` now verifies the
**actual integer polynomial identities**, original-source
counterexamples and finite quotient properties under SymPy
1.14.0. The only Python introduced is this symbolic/finite
validation harness: the proof owners and source semantics remain
Agda, not a Python model implementation. CI owner:
`.github/workflows/x369-p0-sympy-standin.yml`.
The local identical symbolic suite returned
`X369_SYMPY_STANDIN_PASS 27 symbolic/finite checks`;
the GitHub workflow's own execution remains independent and must
be observed before reporting cloud CI green.

The source-directed codec now also supplies:
- `originalFeatureRealizesEveryDirectedTriple`:
  the actual feature (T((1,0,0),(A,B,C))=(A,B,C))
  reaches all integer triples; a universal arbitrary-source
  three-to-two **coordinate-drop** theorem is false.
- `rawWeightedScoreFactorization` /
  `originalWeightedScoreTwoPlusSourceDC`:
  the ACTUAL learned linear head with weights
  `ws,wf,wr` can be evaluated as
  `(ws-wr)*self+(wf-wr)*forward+wr*sourceDC`.
  No third directed feature needs to be materialised if
  source DC is already admitted.
- `zeroDCWeightedScoreNeedsOnlyTwo`:
  with an independently certified sourceDC=0,
  a two-channel weighted original head is exact.
- `rawTwoChannelQuantizationError`: for quantization
  residuals `es,ef,eD`, the exact score error is
  `(ws-wr)*es+(wf-wr)*ef+wr*eD`.
  This is NOT a magnitude/decision bound until actual
  quantizer tolerances and top-k margins are supplied.

A new finite **costed consumer-MDL** source adapter is
`DASHI/Cognition/PNF/X369CenteredDirectedConsumerMDLExact.agda`.
It reuses `AdmissibleConsumerMDLHyperfabricExact` rather
than creating a new MDL algebra. It restricts the original
source to certified zero-DC triads, and compares ONLY
the explicitly declared portfolio of original-coordinate
projections: first alone (cost=1), first+forward (cost=2),
full three channels (cost=3). The first-only candidate
has an actual centered-source collision:
`x=(1,0,0)`, `h0=(0,0,0)`,
`h1=(0,1,-1)`; reverse differs.
The two-channel decoder reconstructs reverse exactly
for all certified zero-DC states. The resulting
`centeredTwoIsMinimalInDeclaredPortfolio` theorem
is *portfolio-relative*, in number of retained original
fixed-width feature scalars. It is NOT minimum storage
bits over arbitrary nonlinear encodings, total runtime
or full recurrent future-state sufficiency.

**Important further no-go:** for the unrestricted original
feature map, two-channel coding without the DC
or a source restriction cannot reconstruct every
reverse-sensitive consumer, even though all three
integer channels are attainable. Do not promote centered
subspace results to unconstrained original checkpoint data.

### Next proof/release gates, ordered

1. **Agda kernel:** validate the THREE new Agda modules
   and their selected import closures with pinned Agda 2.9,
   inspect actual errors and preserve exact head logs.
   A static parentheses audit fixed two provisional
   `Data.Integer.Solver` lambda-grouping errors; only
   the Agda kernel can certify elaboration.
2. **Quantizer-to-router margin:** reuse the existing
   `ConsumerRelativeApproximateFidelityBridgeExact`
   and source top-k proof gate; instantiate certified
   `|delta s_e| <= |ws-wr|*eps_s + |wf-wr|*eps_f +
   |wr|*eps_D` with real original precision/readout
   and a strict gap certificate. The existing source
   contribution is only an EXACT error identity.
3. **Source DC availability:** audit whether DC(x) and
   DC(h_e) are available/reusable before scoring, the
   cost of recomputation/transport and whether input
   or expert histories are *actually* centered.
4. **Future-state:** obtain a source-bound commuting
   compressed-history transition (or exhibit collision)
   for all selected and reactivated histories.
5. **Scientific release:** only compare actual
   total code+metadata+decoder+transition cost against
   an equally admitted full feature implementation,
   with independently held-out task and semantic consumers.
6. **TOE:** avoid injecting unverified candidate import
   dependencies into Golden `Unifier`/`EverythingTOE`.
   New-head Agda acceptance is still OPEN.

Reproducible symbolic stand-in:
```bash
bash scripts/check_x369_p0_sympy_standin.sh
```
Agda proof gates (NOT run here):
```bash
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369CenteredDirectedConsumerMDLExact.agda
```


### P0 refinement: exact 2D C3 action survives compression

The original three directed channels satisfy the rotation
`(s,f,r) -> (r,s,f)`. On certified `s+f+r=0`, the compact
two-channel code `(s,f)` has the **exact** action

    M(s,f) = (-s-f, s),
    M = [[-1,-1],[1,0]],
    M^3 = I.

This is not an invariant-only phase erasure: the small code
retains the FULL nontrivial C3 transformation. Agda now
supplies `rotateCenteredTwoSquared`,
`rotateCenteredTwoCubed`,
`sourceCenteredC3TwoChannelIntertwines`, and
`centeredTwoCodeIntertwinesOriginalC3` on the typed
certified-zero-DC original-source domain. The source
full-three action, costed two-coordinate model, and
C3 action form a commuting square.

SymPy 1.14.0 local stand-in now returns
`X369_SYMPY_STANDIN_PASS 29 symbolic/finite checks`,
including matrix-cubed identity and source algebraic
semiconjugacy. It checks the POLYNOMIALS and finite
fixtures only, not the Agda proof terms or actual
source checkpoint centeredness.

This advances the original research interpretation:
**we are seeking a smaller consumer-sufficient
EQUIVARIANT realization**, not an expanded unrestricted
three-channel hypothesis class. The phase action
survives exactly on the admitted subspace; whether
the trained model's histories live there remains open.
No bit/compute savings or neural-semantic C3 theorem
is implied by this structural result.


## 17 Nov second P0 cut: quantized top-k margin and common-DC router quotient

**New finite decision proof file:**
`DASHI/Cognition/PNF/X369QuantizedRouterDecisionMarginExact.agda`.

It reuses the source weighted-score/quantization-error owner
and the existing approximate consumer-fidelity owner.
For every finite expert index `e : Fin E`, a score
certificate explicitly supplies its admitted original
source score, quantized score and enclosing interval
`[lowerEnvelope(e),upperEnvelope(e)]`.
It also supplies the original admitted TopK selection mask.
If, for every selected `i` and unselected `j`,

    upperEnvelope(j) < lowerEnvelope(i),

then the quantized score of `i` remains STRICTLY above
that of `j`. The same certificate also protects the
original scores' cross-boundary ordering. This is
an interval/sort theorem only: its sufficient inequality
does not imply identical mixture weights, intermediate
expert outputs, retained histories, future semantics
or the availability of an actual quantizer bound.
Finite witness (original scores 1,0, quantized 0,1)
shows ranking can reverse without strict margins.

The original source weight-error law already proved
symbolically is

    error_e = (ws-wr)*es_e + (wf-wr)*ef_e + wr*eD_e.

For admitted scalar absolute errors, the triangle
envelope is

    B_e = |ws-wr| eps_s_e + |wf-wr| eps_f_e
          + |wr| eps_D_e.

The current Agda interval theorem expects an actual
checked envelope as input. Supplying this bound for
the source model (floating point, rounding, and all
real expert candidates) remains OPEN; it must not
be inferred from the algebraic identity alone.

**Stronger exact consumer-relative compression.**
The original shared-head router score factors as
`L_e=(ws-wr)*s_e+(wf-wr)*f_e+wr*D_e`.
When `D_i=D_j` across candidates, their relative
score equals

    L_i - L_j = (ws-wr)*(s_i-s_j)
                + (wf-wr)*(f_i-f_j).

This holds for nonzero DC too: the *shared* DC term
cancels. Hence the two-channel code can suffice for
ranking/softmax relative scores without reconstructing
each full triple; the encoder still must prove equal DC
across original experts. Different DC is a decisive
original-source counterexample: two identical retained
(s,f)=(0,0) may have r=0 versus r=1, and a DC-sensitive
head distinguishes them. Shared learned weights
alone do NOT imply shared expert-history DC.

The new exact Agda declarations in
`X369DirectedRouterConditionalCodecExact` are
`twoChannelRelativeScore`,
`rawCommonDCCancels`, and
`originalSameDCRelativeScoreFactors`.
No change to the original Leech/PyTorch model was made.

**SymPy stand-in continuation.**
`scripts/check_x369_p0_sympy_standin.sh` adds exhaustive
finite checking of 2- and 3-expert strict score envelopes,
coefficient-weighted quantization-error triangle bounds,
and source common-DC score cancellation plus negative
control. Independent local SymPy validation in this
session checked 141 strict 2-expert cases, 207 strict
three-expert top-1 cases, 3375 coefficient/error cases,
plus exact original DC-score polynomial identities.
The complete updated GitHub shell/workflow remains
pending an actual current-head CI run; those smaller
local checks are not an Agda kernel receipt.

**Remaining P0:** typed source quantizer error-to-Nat
interval weld, all top-k (not just top1) source tie/slot
semantics, softmax/retained-history consumer discrepancy,
and actual source-history DC admission. Reuse existing
`ConsumerRelativeApproximateFidelityBridgeExact`,
`LeechJointStateConsumerQuotientExact` and
`FibreRoutingCompressionLadderExact`, rather than
recreating their generic carriers. Remain blocked on
Agda 2.9 kernel until external proof runner available.


### P0 third cut: what actually suffices for shared expert DC

The `sourceDCEqualForAnyTwoHistoriesWhenActivationCentered`
theorem makes a useful SOURCE-BASED sufficient condition
explicit: when a shared triad has `a+b+c=0`, all original
per-expert products
`D_e=(a+b+c)(A_e+B_e+C_e)` are equal to zero,
no matter how the independent histories differ.
`sourceDCZeroFromCenteredHistory` is the alternative
per-expert condition. `zeroLeftProduct` and
`zeroRightProduct` are separately supplied typed
integer solver proofs, not floating-point assumptions.

Combined with `originalSameDCRelativeScoreFactors`,
this shows that a centred shared activation admits
an exact **two-directed-coordinate score difference**
for EVERY original expert candidate under the one
shared trained head. A weaker nonzero common-DC
condition also suffices for relative score preservation.
The latter is useful even if reconstructing the
entire original directed triple remains impossible
from the two channels alone.

**Critical implementation guard:** layer-normalisation
over all `d_model` coordinates does NOT certify each
of the individual 3-coordinate triads has zero mean.
The exact source-specific centering / equal-DC
admission must be checked, or a correction/residual
DC value retained. Neither a global-layer mean
nor the word `invariant` supplies this premise.

Symbolic stand-in now also checks the original
activation-centering identity, equality across
independent expert histories, and a counterexample
for noncentred x. Only original-source reference
identities and local SymPy are admitted; no new
PyTorch model implementation was introduced.

Source P0 is now blocked mainly on actual original
floating-point activations/weights, explicit scalar
quantizer error budgets, Agda kernel checking,
and future expert reactivation. Do not label
new sympy checks as accepted kernel theorems.


## 17 Nov fourth P0 cut: arbitrary-source SHARED-HEAD FUSED SCORE

**New strongest source-to-consumer formal owner:**
`DASHI/Cognition/PNF/X369SharedHeadFusedScoreExact.agda`.

The earlier 3→2 directed-coordinate quotient is conditional
on a zero DC, an equally shared expert DC, or a suitable
consumer restriction. This NEW reduction is strictly more
general for the **original learned scalar router-score
consumer**: it requires NO centering, NO equal DC and NO
inference that a trialectic face can be discarded.

For every original triad x=(a,b,c), expert history
h=(A,B,C), and shared learned original directed head
w=(ws,wf,wr),

    score = ws*(aA+bB+cC)
          + wf*(aB+bC+cA)
          + wr*(aC+bA+cB)
          = <K_w x,h>,

    K_w x = (ws*a+wf*c+wr*b,
             ws*b+wf*a+wr*c,
             ws*c+wf*b+wr*a).

`rawOriginalScoreFuses` supplies a nine-variable typed
integer ring-solver proof on the ACTUAL original
three-channel construction. `sourceScoreEqualsFusedConsumer`
factors the existing original weighted-score owner
through `precomputeSharedSource` and `fusedExpertDot`.
`allExpertScoresExactlyPreserved` structurally lifts this
to an arbitrary list of independent expert histories with
ONE precomputed K_w x. `allSourceTriadBlocksExactlyPreserved`
structurally lifts it to an arbitrary list of triad blocks
with their independently shared source/head values.
`everyScoreListConsumerExactlyPreserved` then transports
ANY deterministic consumer of that full ordered score
list, encompassing a fixed source sorting/tie policy,
but NOT an observer needing the discarded internal
T coordinates or inactive history.

This is a **computation/intermediate consumer** reduction
valid on every source integer triad; it is NOT a
reconstruction codec for T itself. All full original
source weights and expert histories remain available
to the fused score path.

An explicit cost model counting scalar MULTIPLICATIONS
in the stated arithmetic plans gives per triad:

    baseline unfused  = 12 * experts
    shared-head fused = 9 + 3 * experts

For E=1 both count 12; for E=4 the elementary
plan counts 48 versus 21 (27 fewer). Actual memory,
additions, register pressure, kernel launches, float
rounding/reassociation, autograd, routing, GPU compiler
fusion, wall time and energy remain unmeasured. This
arithmetical comparison is NOT a physical speedup.

**SymPy 1.14 symbolic stand-in** independently reduced
the source nine-variable polynomial to exactly zero
and matched four heterogeneous expert histories each
spanning three different triads. The repository
stand-in script also contains those exact checks,
scalar-multiply counting controls, all recent
DC/margin/quantizer controls. The current-head full
GitHub workflow has not reported a pass and is NOT
a substitute for Agda 2.9 elaboration.

**Highest-alpha next binding:** replace the temporary
candidate full-T computation in the original Leech
source with a deliberately opt-in *fused scoring path*
only after proof of torch/float approximate consumer
bounds and the source-specific sorting/gradient
contract. Model changes need a separate original
physical run and a full E=number-of-experts cost
benchmark. This no-run branch therefore updates
formal proof sources and SymPy CI only, not Leech
PyTorch itself.

### Revised source hierarchy

- P0 exact full-3-channel gauge: a fixed rotation is
  a change of coordinates, not an expressivity gain
- P0 exact conditional 3→2 state code: only with
  admitted DC side info or centered source domain
- P0 exact common-DC relative score code: two channels
  can preserve relative logits even without full T
- **P0 exact arbitrary-state fused score**: no DC
  condition when the consumer is the original scalar
  learned shared router score; project x through
  a circulant learned linear operator once, then dot
  with each expert h
- P0 quantizer margin: finite formal envelope source
  written, source floating/error admission still OPEN
- P1 future history/selected consumer: existing
  generic owner, original step-to-code weld OPEN
- P1 original task/Sophontic/dialectic/trialectic
  semantic action: OPEN independently of score fusion
- P1 costed physical precision/latency/energy: OPEN
- Agda 2.9 kernel and Golden TOE import acceptance:
  OPEN until pinned actual checker receipt

To check new sources on the actual Agda host:

```bash
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369QuantizedRouterDecisionMarginExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369SharedHeadFusedScoreExact.agda
```


## 17 Nov Round 2 — four-gate source-specific SymPy maximum cut

**User instruction:** continue formal/symbolic work without needing Agda
or CI execution. Do not confuse a source algebra theorem with
bitwise torch parity, trained behaviour or device benchmark.

**Source inspection:** `LeechTransformer/models/history_orbit_moe.py`
at branch `experiment/x369-r4-fair-c2c3-residual-20261115`;
`models/trialectic_wave_prior.py`.
`select_source_experts` forms `features=(x,h_e)`,
the C2 residual base route is `abs(features)`, while C3 residual
features are
`cat(trialectic_router_invariants(phase_x),
 directed_trialectic_invariants(phase_x,routed_h))`
with one shared residual head and `expert_bias[e]`.
The source selects via `torch.topk` (or explicitly opted-in
`torch.sort`) and uses softmax over the selected ordered values.
`step` loops over selected expert IDs and changes only selected
histories. `execute_selected` receives authenticated-by-caller
`x`, ordered selected IDs, selected histories, and selected
weights; it does NOT independently re-route or own inactive state.
The actual implementation does not have an arbitrary quantizer
whose error tolerance can be asserted without its encoding contract.

### Gate 2: Quantizer-to-top-k with source-bound envelopes

For the fused **DIRECTED** residual, let
`u=K_w x`, with a, b, c from the shared (possibly q-gated)
activation and `h_e` from expert history. For elementwise
quantization errors `|dw_i|<=epsw_i`,
`|dx_i|<=epsx_i`, `|dh_ei|<=epsh_ei`,
define each coefficient bound

    U0 = Σ_(widx,xidx)=(0,0),(1,2),(2,1)
       (|widx| epsx_xidx + epsw_widx |x_xidx|
        + epsw_widx epsx_xidx).
    U1 = same cyclic source pairs (0,1),(1,0),(2,2).
    U2 = same cyclic source pairs (0,2),(1,1),(2,0).

In exact real/rational arithmetic,

    |quantized_dot(u+du,h_e+dh_e)-dot(u,h_e)|
      <= B_e
       = Σ_i [U_i |h_ei| + (|u_i|+U_i) epsh_ei].

Add separately calibrated rounding/accumulation and any
source C2 history-feature, expert-bias or nonlinear unary
error budgets for the FULL R4 score. The formula alone
does NOT enclose float32, BF16, FP16 or any hardware kernel:
it needs a quantizer error certificate and a separately
bounded floating-point evaluation order, including underflow,
overflow and subnormals as applicable.

For source selected set S, exact order/membership is
preserved under this interval budget if

    min_(i in S) (score_i - B_i)
      > max_(j notin S) (score_j + B_j).

This certifies a TOP-K **SET**, not ranked selected
slots. To certify ordered IDs as returned by the
original source, also require every adjacent chosen
score gap (or all relevant internal chosen pairs)
to strictly exceed their error-budget sum. At an
actual TIE, `torch.topk` and opt-in `torch.sort`
are not assumed to use identical tie policies.
If exact logits differ by a shared real constant,
ideal top-k and selected softmax are equal; neither
floating-point bitwise parity nor identical
tie-ordering across different kernels follows.

The local SymPy/rational demonstration used
`w=(2,-1,1)`, `x=(1,2,-1)`,
`epsw=1/64`, `epsx=1/32`,
`epsh=1/16` per coordinate, and four expert
histories `(1,0,1),(-1,2,0),(0,1,-1),(3,0,0)`.
Exact original scores were `[2,-1,5,15]`.
Quantized scores were
`[62109,-31027,170749,497389]/32768`;
certified absolute rational error budgets
`[34025,40217,34025,40217]/32768`.
These prove both ordered selected IDs `[3,2]`
and top-2 membership for THAT fixture under the
declared deterministic numeric comparison.
No claim that those tolerances came from the
original checkpoint.

### Gate 3: One-step selected sufficiency versus future routing

In `HistoryOrbitMoE.step`, routing depends on
**all E current histories**. The remote
`execute_selected` consumer can evaluate one
admitted selected route with only:
(a) shared raw activation x,
(b) authenticated ordered selected IDs,
(c) exact source-selected weights,
(d) selected histories,
(e) the correct expert/orientation/transition parameters
and history-cap settings.

Unselected histories remain *unchanged at their
source owner*. They are not globally redundant.
A two-expert finite source-model witness is:
at `x0=(0,0,0)`, both h configurations
`[(0,0,0),(0,0,0)]` and
`[(0,0,0),(2,0,0)]` have equal current
directed logits and admit selected expert 0 under
a declared lowest-ID deterministic tie rule.
At the NEXT `x1=(1,0,0)`, with a self-channel
routing head, their selected experts differ:
one ties and chooses 0; the other chooses expert 1.
This is a *counterexample to deleting inactive
histories on the basis of selected-packet equality*;
it is not a claim about torch's internal tie policy.
The correct positive future theorem is a
time-indexed commuting reduced transition, or
reopening/retention of inactive histories with
the original owner and consistency receipts.

### Gate 4: Original R4 effective rank and arithmetic costs

**New research-critical source observation.**
The R4 `c3_residual_weight` has nominal 2d
entries, but its first d entries multiply
`trialectic_router_invariants(phase_x)`, a unary
function of the same shared x for every expert.
Their contribution is a common scalar to
all expert logits and cancels in exact
ranking and softmax. The C2 base router's first
d x-half and C2 residual control's first d
x-half also have this shared-unary null direction.
Thus `2d nominal` is not `2d effective
routing degrees`: only up to d directed/history
coordinates of the added R4 residual can
change the routing consumer through this path.
This is not a complete effective-rank theorem,
because directed features may have additional
dependencies and tasks/auxiliary losses may
observe different variables.

The **unconditional** original directed
bilinear score fusion remains correct for every
triad and all expert histories:
`K_w x` once per source x and shared head,
then a 3-term dot product per expert.
For N=d/3 triads and E experts, the transparent
multiplication-site plans count
`N*12E` versus `N*(9+3E)`:
at d=384 (128 triads), E=4:
`6,144` vs `2,688`, saving
`3,456` scalar multiplication sites for
the **directed score calculation only**.
At float32, a materialized directed channel
buffer `[batch,E,d]` has `B*E*d*4`
bytes (6 KiB per sample for E=4,d=384);
a materialized shared K vector `[B,d]`
is `B*d*4` bytes (1.5 KiB per sample).
These are upper-level illustrative buffer
sizes, not observed GPU peak-memory savings.
R4 also has C2 features, expert histories,
orientation scores, FFNs, transitions, caches,
other intermediates and possible kernel fusion.
There is NO measured runtime/energy/speedup.

**Backward algebra:** because the full directed
weighted score and fused bilinear score are the
SAME polynomial, derivatives with respect to
all nine source/history/head input coordinates
are symbolically identical wherever the route
is differentiable. This does not certify
bitwise autograd equivalence for different
floating-point operation orders, discrete
top-k selection or q-gate threshold surfaces.

### Gate 5: Semantic consumers remain independently typed

The exact score-list equality proves only
consumer sufficiency for a function of the
SAME logits. The original
`GrokkingEquivarianceDefectGeometryExact`
compares a task action (algorithm defect 0;
held-out memorizer defect 2). It does not
identify trained Leech logits with task labels.
The original
`TrialecticBoundaryFaceNonfactorabilityExact`
constructs identical three-edge boundaries
with DIFFERENT reciprocal/coercive face labels:
no boundary-only or router-score-only
factorisation of that face consumer is warranted.
Sophontic argument-response opposites are
independently typed and must not be silently
identified with C2 sign or geometric C3 rotation.

### Source-of-truth outcome and follow-up

**Reusable executable SymPy stand-in:**
`scripts/check_x369_source_four_gates_sympy.py`.
The tool is algebraic/finite source validation,
not a model simulation, physical proof or
Agda kernel acceptance. An independent local
SymPy check of the same underlying polynomials
returned 14 grouped passes and exhaustive
8,484 finite four-expert top2 margin
certificates (6,588 preserved *ordered* slots);
the latter distinction proves why set parity
does not entail slot parity. The complete
new committed script has not received a
reported GitHub run. Do not label it green CI.

**Next highest alpha:** formal error budget for
the R4 C2 `abs(h_e)` head and residual fused
directed score simultaneously; full original
`topk`/selected softmax acceptance using
ordered score intervals; explicit future
transition-fibre preservation theorem on the
actual model parameters; and proof that
`c3_residual_weight[:d]` has identically
zero decision loss gradient under
the admitted score-only consumer.
All must preserve the difference between
source exact reals and floating-point kernel
reassociation. No hardware runs requested.


### Round 2b: mixed-null q-gate and one-step history independence

Source `LeechTransformer/models/trialectic_wave_prior.py`
defines `q_gated_mixed_c3_mask` as
`flip_j = q(x_j) > mean_j(q(x_j))`, XORed with
the fixed seed-owned sign mask. This is **piecewise
constant** as a function of x, not a single fixed
rotation and not a smooth global input operator.

For q(a,b,c)=1/2[(a-b)^2+(b-c)^2+(c-a)^2] and
input errors (ea,eb,ec), its exact perturbation is

    delta_q = (a-b)(ea-eb)+(b-c)(eb-ec)+(c-a)(ec-ea)
            +1/2[(ea-eb)^2+(eb-ec)^2+(ec-ea)^2].

Given coordinate envelopes `|ea|<=eps_a`, etc.,
an admitted q-error envelope is

    Q_j = Σ_(pairs i,k)
          |x_i-x_k|(eps_i+eps_k)
          + (1/2)Σ_(pairs i,k)(eps_i+eps_k)^2.

Since the threshold is the sample mean of all triadic
q values, its own possible error is bounded by
`mean(Q)`. A sufficient **gate stability**
certificate per triad is

    |q_j - mean(q)| > Q_j + mean(Q).

Only after this gate certificate can one reuse
the fixed-rotation input quantization budget
for the mixed-null score; otherwise infinitesimal
perturbations near a q mean tie can flip the
+120/-120 branch. The local exact rational
negative control uses two equal-q=1 triads;
perturbing one coordinate by 1/4096 flips
`q > mean(q)`. With a suitable expert
history and self-channel head, the changed
phase branch changes its directed score
by order-one even as the input error tends
to zero. Thus **Lipschitz quantization in x
alone is NOT a source-valid mixed-null
certificate across gate boundaries.**

The positive fixture has triads
`(2,0,0)` and `(0,0,0)` with each input
coordinate error <=1/100; it satisfies
the strict q-margin bound, and all 64
sign-corner rational perturbations keep the
same gate. The stand-in script checks both
positive and adversarial cases, not only
anecdotal examples.

**One-step history/mixture refinement.**
Source `HistoryOrbitMoE.step` computes each
selected expert's `y_c` and next history
from x, old selected h and its expert/orientation
parameters, *before* multiplying y by the
selected softmax weight. Consequently under
an identical selected EXPERT SET, identical
x/current selected histories/parameters,
the original per-expert **one-step history
updates** do not depend on changed mixture
weights, even when the emitted mixture
output differs. The returned `signs` and
`weights` arrays remain indexed by selected
SLOTS, and their order still matters for
packet/API parity. The weighted mixture
output is softmax-dependent, so its change
can change the NEXT layer's shared activation
and downstream future histories; do not
infer global recurrence parity from
one-step selected-history parity.

The refined source consumer ladder is:
(1) TopK SET,
(2) ordered selected IDs,
(3) selected weights/mixture output,
(4) selected expert history updates,
(5) all inactive source histories,
(6) future full-model traces, and separately
(7) typed semantic task/argument/face consumers.
Proving one level does not silently close
the others.

For the full original R4 SCORE, the
quantizer budget must ADD the C2
expert-history `abs(h_e)` path and
`expert_bias[e]` to the fused directed
budget. For v_h the learned C2 history
weights and eps_v the admitted weight
errors, use `||h+dh|-|h||<=eps_h`:

    B_e^(C2-history) <= Σ_i [
        |v_hi| eps_hi
        + eps_vhi (|h_i|+eps_hi)
    ].

Then
`B_e^(total) <= B_e^(C2-history)+
 B_e^(directed-fused)+eps_bias_e+
 B_e^(actual-floating-evaluation)`.
Shared unary x terms may be omitted from
*relative ideal logits* if evaluated identically
for every candidate. The q gate requires
its independent stability premise. No
actual source dtype/rounding calibration or
kernel reassociation receipt has been
supplied in this no-run phase.

The conditional real-weight softmax bound
`||softmax(s+delta)-softmax(s)||_1 <=
 ||delta||_infinity` for a fixed selected
set (and corresponding slot order) can
bound one-step mixture outputs via bounded
expert-output norms. This DOES NOT show
bitwise equal output weights or any
finite-precision source contract; it is
a downstream analytical theorem contingent
on the admitted envelopes.


### Round 2c: exact declared arithmetic plan and model-level cost firewall

At d=384, there are N=128 original 3-coordinate
triads per hidden activation. For E candidate experts
the source directed-channel scalar expression uses
per triad 12E multiplications and 8E additions
(3 bilinear 3-product/2-add channels, followed by
3-product/2-add weighted head).
The shared-head fused direct score uses
9+3E multiplications and 6+2E additions
(three 3-product/2-add shared K coefficients,
then one 3-product/2-add history dot per expert).
At the **default E=4** source configuration:

- Original expression: 6,144 scalar multiplications,
  4,096 additions; total 10,240 elementary operations
  per d=384 token under the disclosed plan.
- Fused expression: 2,688 multiplications,
  1,792 additions; total 4,480 operations.
- Plan savings: 3,456 scalar multiplications,
  2,304 additions; 5,760 elementary operations.
- Directed correlation buffer if materialized:
  `[B,E,d]` float32 = 6,144 bytes per batch item.
  Shared K coefficient vector `[B,d]`
  float32 = 1,536 bytes per batch item.
  This is 4.5 KiB less *in this one hypothetical
  pair of materialized intermediates*, not a
  measured device peak-memory improvement.

For an honest runtime model, the fused path only
wins when total source costs, compilation,
kernel launches, memory traffic, gradient
recomputation and native device utilization
make

    T_fused = T_precompute + T_expert_dots + T_overheads
          < T_original_directed.

It may lose for E=1 or when the original framework
already combines directed channels and head weights
into an equivalent kernel. No timing observation
or source scalar instruction trace was obtained.

The R4 router still evaluates the baseline
C2 expert-history `abs(h_e)`, expert-specific
biases, selected softmax, C2 orientation,
expert FFNs, history transitions, cap and
full next-layer state. Source independent
`phase_x` q-gate (mixed-null) can itself
be computed once from the shared activation
per sample, but its threshold stability under
quantization is an independent prerequisite.

**Gradient/learning interpretation:** the
shared unary x contributions of C2 source
and every R4 residual are exact null
directions for the *selection/softmax
consumer* in real arithmetic. That is
distinct from the separately retained
expert-history features, which can change
which expert is selected, and from
learned coherent/mixed C3 directed features.
Only the latter provide immediate
x–history conditional interaction in
this selected route. Effective routing
rank can be below d if features are
further dependent; d is an upper
bound on the effective active first-order
linear coefficients, not a confirmed
rank or a measured training result.


## 17 November — R4 full decision-envelope maximum cut (SymPy stand-in)

**Implementation:** `scripts/check_x369_r4_end_to_end_envelope_sympy.py`.
Read against authoritative source
`LeechTransformer/models/history_orbit_moe.py` and
`models/trialectic_wave_prior.py` on the existing R4 branch.
This audit does NOT substitute SymPy for a Torch/Agda/ROCm runtime,
and does not implement a new surrogate model.

### Exact routing-source decomposition

On source `c2_c3_residual` or
`c2_c3_mixed_null_residual`, per expert

    logit_e = U(x) + sum_i v_i |h_ei|
              + sum_j <K_(w_j) phase_j(x), h_ej>
              + expert_bias_e.

Here U(x) includes the source baseline x-half,
the source learned router bias, and the C3 unary
residual `trialectic_router_invariants(phase_x)`.
These are SHARED across all candidate experts and
cancel from exact score comparisons/ideal selected
softmax (NOT necessarily from different floating-point
evaluation paths). The weights v on abs(h)
are the pre-existing original C2 router h-half,
and the directed w are the original C3 residual h-half;
the expert_bias is an independent learned vector.
Do not drop v, expert_bias, or the original
source route-probe/geometry branch.

The C2 control `c2_c2_residual` has a distinct
expert-dependent term `sum_i (v_i+z_i)|h_ei|`
plus expert_bias: no directed bilinear K.

### Joint source quantization envelope

Take admitted coordinate bounds

    |delta x_i|<=epsx_i, |delta h_ei|<=epsh_ei,
    |delta v_i|<=epsv_i, |delta w_i|<=epsw_i,
    |delta expert_bias_e|<=epsbias_e.

For a fixed coherent/mixed C3 branch,
`phase_x` is a coordinate permutation.
Permute the x-error envelope in the SAME branch.
For each source triad j, K contains three
weighted linear combinations; define

    Uk = sum_(i,l in K_k)
         [|w_i| epsx_phase_l
           + epsw_i |phase_x_l|
           + epsw_i epsx_phase_l].

This encloses every coefficient perturbation
under independent x/head coordinate errors.
Then

    B_e^directed =
       sum_k [ Uk |h_e,k|
              + (|K_k|+Uk) epsh_e,k ].

For the unquantized C2 history route,

    B_e^C2 =
       sum_i [ |v_i| epsh_ei
             + epsv_i (|h_ei|+epsh_ei) ].

The per-expert total relative-logit budget is

    B_e = B_e^C2 + B_e^directed
          + epsbias_e + B_e^floating_evaluation.

The last term is an independently needed
source/hardware computation envelope; no
hardware value has been invented. The common
unary x contribution is excluded only from
the *ideal* differences. If fused/unfused
floating arithmetic has expert-dependent
rounding around that common contribution,
it is covered by the extra evaluation error
budget, not silently treated as exact.

For the matched C2 residual control, use
v+z and combined epsilon_v+epsilon_z in
the abs(h) formula, plus expert_bias.
The coherent and mixed R4 arms use the
same base history and bias model but
distinct phase_x, so their topk scores
and margins differ even with the same
residual numeric weight vector.

### Separate mixed-null q gate certificate

The original mixed route computes
`q_j>.mean(q)`, XORed with seed-owned
base mask. For each triad error bound
`Q_j` from the existing pair-difference
perturbation identity, require

    |q_j - mean(q)| > Q_j + mean(Q).

This conservative strict certificate ensures
the source's `>` branch and hence
the rotation permutation is unchanged.
Without it, arbitrarily small input
perturbation may produce a different
C3 orientation and invalidates the
fixed-branch score envelope.
A more permissive one-sided interval
acceptance is possible: positive branch
requires a strictly positive lower
bound on q_j-mean(q); false branch
can accept an upper bound <= 0, respecting
the source strict `>` semantics.

### Decision and downstream consumer ladder

Given the actual unquantized ordered
selected `S`, certify

    min_(i in S)(logit_i-B_i)
      > max_(j not in S)(logit_j+B_j)

for the selected SET. Additionally
certify adjacent within-S ordering
`logit_(slot k)-B_(slot k) >
 logit_(slot k+1)+B_(slot k+1)`
for identical original ordered slot IDs.
This bypasses unspecified source
`torch.topk` tie behaviour only by
certifying **no relevant ties**.
Weights can differ despite identical IDs:
with each selected real logit perturbation
at most `B=max_(i in S) B_i`,

    ||softmax(s')-softmax(s)||_1 <= B.

Proof: along interpolation, softmax
Jacobian applied to perturbation v has
L1 norm `E_p |v-E_p v|` at most
`sqrt(Var_p(v))<=||v||inf`.
If source expert outputs satisfy
`||y_e||<=M` and changed outputs
`||y'_e-y_e||<=Y`, the one-step
mixture discrepancy is bounded by

    ||o'-o|| <= M*B+Y

conditional on the same selected set and
aligned expert IDs. For score-only
intervention with unchanged selected
expert computations, Y=0. The inequality
is real arithmetic; finite-precision
softmax and output accumulation need
a separate execution budget. Slot
parity is necessary if comparing the
returned slot-aligned arrays verbatim.

**Orientation/history gate:** the source
selected expert sign uses
`2*F.linear(cat(x,h),orientation.weight,None)`
with first-nonzero-component fallback
when its score is exactly zero.
For z=(x,h), parameter v_ori and
absolute envelopes eps_z, eps_ori,
certify

    O = 2*sum_i v_ori_i z_i
    B_ori = 2*sum_i [
              |v_ori_i| eps_z_i
              + eps_ori_i (|z_i|+eps_z_i) ].
    |O|>B_ori.

Only then is the selected orientation
sign guaranteed unchanged under
the perturbation. At O=0, source's
fallback is nontrivial and requires
a separate exact tie/fibre law:
do not presume continuity through
the sign boundary.

With the same selected set, source
`step` uses expert FFN output and
the history transition independent
of the selected mixture weight;
changing only softmax weights
leaves the *one-step selected history
update* exact, while changing
mixture o. If x/h themselves change,
require a separately admitted
selected expert transition
Lipschitz/error certificate, including
orientation and cap branches.
For a combined state discrepancy
`D_(t+1)<=L_t D_t + eta_t`,
future errors can be bounded by
the unrolled product/sum if all
router and orientation margins are
re-certified along the trace.
For a uniform L, eta and D0=0:

    D_t <= eta * sum_(j=0)^(t-1) L^j.

When L=1 this is t*eta.
This is a **conditional recurrence**,
not an original learned-Leech future
guarantee: the source has discontinuous
topk and orientation gates.

### Exact rational witnesses (source formulas, not fitted tolerances)

The executable audit instantiates
d=6 (two original triads), E=4,
topk=2; shared x=(2,0,0,0,0,0),
C2 history coefficients
v=(0,1,1,0,0,0), directed weights
w=(2,-1,1,1,0,2), original expert
biases (0,1,5,10), and the four
independently owned histories
(0,1,0,0,0,0), (1,0,1,0,0,0),
(0,1,1,0,0,0), (1,1,0,0,0,0).
Input/history/baseline-head/C3-head
errors are independently bounded by
1/256 per coordinate, and expert
bias errors by 1/256.

- **Coherent:** original scores
  (3,4,13,11); exact score-error budgets
  (594441,824201,824201,824201)/8388608;
  both top2 membership AND ordered slots
  are certified as (2,3).
- **Mixed q gate:** original scores
  (5,2,9,17); same certified budgets;
  top2 membership/order is (3,2);
  independently certified q gate
  stays in the same original branch.
- **Matched C2 residual:** original scores
  (0,5,8,11) with independent
  residual weights z=(1,-1,2,0,1,-2);
  C2-specific coordinate intervals
  certify ordered top2 (3,2).

SymPy checks the exact perturbed scores
against those enclosing budgets, exact
ordered/membership separation, selected
softmax/mixed-output numerical inequalities,
joint input/head/history error polynomial,
orientation signed-score margin and its
adversarial sign-tie witness, and finite
recurrent geometric-series algebra.
All source-numeric budgets here are
*rational examples*, NOT independently
measured training or hardware tolerances.

**Status/next:** End-to-end **conditional**
mathematical R4 envelope is specified
and encoded in SymPy stand-in. The
highest-alpha remaining weld is to
establish interval/error provenance
from an actual precision/quantizer
for the original weights and activation
histories, including floating-point
fusion versus unfused evaluation,
then instantiate layer-wise source
transition/FFN Lipschitz bounds
and recheck margins along full traces.
Independent Sophontic/grokking/
trialectic semantic consumers remain
outside a router-output-only proof.


### R4 completed conditional envelope — formal consumer refinement (17 Nov)

New Agda **proof-source** weld
`DASHI/Cognition/PNF/X369R4SharedScoreConsumerWeldExact.agda`
imports the existing fused score formalism rather than
defining a new original directed feature owner. It
represents the source's common unary logit term,
the separately supplied exact C2 absolute-history
head contribution, each independent expert bias,
and the existing original directed residual score.
`originalR4ScoreFactorsThroughFusedHead` and
`everyExpertScorePreserved` give exact integer
factorisation per expert and over arbitrary expert
lists; `everyOrderedScoreListConsumerPreserved`
transports arbitrary deterministic consumers of
the full ordered score list. The separate
`commonUnaryCancelsRelativeScores` is an
integer ring-solver proof. **No Agda kernel receipt
is claimed**, and the actual source float/c2
history calculation must be admitted separately.

The revised `scripts/check_x369_r4_end_to_end_envelope_sympy.py`
now includes source-dependent rational examples for
ALL THREE R4 arms:
`c2_c3_residual`, `c2_c3_mixed_null_residual`,
and `c2_c2_residual`; the two C3 arms certify
softmax and mixture output discrepancies given
fixed expert output values. A separate strict
orientation score interval confirms that
`sign(2*orientation(z))` does not cross zero.
A near-zero witness refutes unconditional sign
stability; a q-mean tie witness refutes
unconditional mixed-mask stability. The
source's fallback orientation sign at exactly
zero is left as a separate equality case, not
mislabelled continuous.

**Exact GELU/source recurrence structure.**
The source uses `nn.GELU()` in each expert FFN.
For exact Gaussian GELU,

    GELU'(t) = Phi(t) + t*phi(t),

with a valid global (loose) Lipschitz bound
`Lg = 1 + 1/sqrt(2*pi*e)`. The script checks the
derivative identity and Gaussian extremum by
SymPy; the global bound follows analytically
from 0<=Phi<=1 and
`|t*phi(t)|<=1/sqrt(2*pi*e)`.
It is NOT a numerical Torch/GELU evaluation
error certificate. For admitted spectral norms
of original checkpoint FFN matrices W1/W2
and expert transition matrix T, after
certifying unchanged selected IDs, q branches
and orientation signs:

    Y_e <= ||W2||2 * Lg * ||W1||2
          * sqrt(Dx^2+Dh_e^2) + eta_FFN_e,

    H_e' <= ||T||2
          * sqrt(Dx^2+Dh_e^2+Y_e^2)
          + eta_transition_e.

The source `cap_history` is a radial Euclidean
projection; its exact mathematical operation
is nonexpansive in the Euclidean norm. Actual
float64 norm evaluation and later dtype cast
remain additional evaluation-error terms.
For low-rank transition, replace ||T|| by
the product of the two transition matrix
spectral norms (or a verified composite
operator norm). Where `train_sign=True`,
the straight-through tanh gradient is a
DIFFERENT contract: this analysis covers
hard-sign forward/inference, not training
optimizer parity.

For identical ordered selected experts,
the script now symbolically checks the
softmax Jacobian `J=diag(p)-pp^T`, its
common-shift null, variance expansion,
and the exact output decomposition

    o'-o = Σ_e (p'_e-p_e)y_e
           + Σ_e p'_e (y'_e-y_e).

This supports the conditional
`||o'-o||<=M*B+Y` formula for certified
source score/error and expert-output
envelopes. The same source transition is
independent of p_e within the *current*
selected-expert update, but altered o can
change the next layer's activation.

For an admitted uniform step Lipschitz
coefficient L and step noise eta,
`D_t <= eta Σ_(j=0)^(t-1) L^j`
when initial divergence is zero. The
updated script verifies the symbolic
geometric sum and a 4-step **variable
L_t/eta_t** expansion. Such a recurrence
does NOT prove a source trace unless
topk, mixed q mask and orientation
certificates are valid on EVERY required
step and the actual network parameter
norms/precision budgets are supplied.

**Source-specific next high-alpha:**
establish actual original dtype, tensor
quantizer, elementwise error provenance
and runtime evaluation slack; compute
spectral-norm receipts from the original
checkpoint (when run capacity returns);
certify topk, orientation and q thresholds
for every targeted activation/history
trace; retain source inactive histories
for future reactivation. Grokking,
Sophontic and trialectic face outcomes
remain separate typed consumer gates.

No user GPU, CI or Agda run is asserted
for this continuation. The local
independent SymPy reproduction verified
coherent (3,4,13,11)->[2,3],
mixed (5,2,9,17)->[3,2], and matched
C2 (0,5,8,11)->[3,2] rational fixture
margin conditions; coherent/mixed
selected softmax L1 discrepancies and
mixture discrepancies were within
the certified score envelopes. The
additional softmax/recurrence polynomial
identities were also checked locally.
The complete committed script's direct
execution is not independently
recorded in this environment.


## 17 Nov follow-on: correlated R4 pairwise error max-cut (source score, no run gate)

See detailed standalone owner:
`Docs/roadmaps/X369R4RelativeErrorMaxCut20261117.md`.
New SymPy-only source checks:
`scripts/check_x369_r4_relative_certificate_sympy.py`,
`scripts/check_x369_r4_pairwise_sympy.py`,
`scripts/check_x369_r4_alltriad_pairwise_sympy.py`.

**Now source-written and locally independently exercised:**

- Exact shared activation / directed-head / C2-history
  pairwise error formula. For original learned head
  `u=K_w phase(x)`, the *shared* quantizer
  perturbation contributes `Delta u·(h_i-h_j)`,
  not independent `Delta u·h_i` and
  `Delta u·h_j` terms.
- Direct strict score-difference margin tests
  preserve TopK membership and ordered slots.
- Sharper one-sided q gate interval using correlated
  source sample mean, with exact tie refusal.
- Selected softmax error controlled by half
  the maximal certified selected-pair score
  difference error, not the full absolute
  per-expert logit uncertainty. This correctly
  quotients the shared unary R4 direction.
- Original two-triad, E=4 coherent/mixed source
  fixtures both pass rational pairwise intervals
  and conditional selected output-mixture bounds;
  no hardware data are inferred.
- A nonautonomous recurrence coefficient identity
  is checked symbolically. Actual checkpoint
  spectral norms and guard admission across a
  full source trace remain OPEN.

The coherent first-triad selected-pair interval
tightens by 28.1% relative to independent-logit
error addition in the same admitted rational
precision fixture. This improvement belongs to
the proven error budget, not a measured decrease
in hardware quantisation error.

**Remaining high-alpha:** actual source precision
and evaluation receipts; maintain per-step TopK/
q/orientation strict guards; authoritative inactive
history reactivation and typed semantic consumers;
original performance and runtime calibration.
CI and kernel acceptance are explicitly deferred
by user instruction, not silently marked passed.


## 17 Nov final structural max-cut: original recurrent-history observability rank

New owner:
`Docs/roadmaps/X369R4HistoryObservabilityRankMaxCut20261117.md`.
SymPy source:
`scripts/check_x369_r4_circulant_history_sufficiency_sympy.py`.

The original shared directed head has a C3-circulant
3×3 history-observation matrix `M_w`, with exact
factorization

    det(M_w) = (ws+wf+wr) * q(ws,wf,wr)

and squared singular spectrum

    (ws+wf+wr)^2, q(w), q(w).

For an arbitrary future-activation consumer, the
history observation rank is generically 3,
drops to 2 for a nonzero zero-sum head, to 1
for equal nonzero head weights, and 0 only
for a zero head. This is the precise original
directed-score compression/no-go boundary.
The mixed q-gated source action remains
bijective in exact arithmetic because its
mask depends only on C3-invariant q energies,
so it does not evade generic-rank observability.

The original C2 history `abs(h)`, orientation
scorer, FFN and learned transition may still
distinguish the directed-null DC history
component. Full recurrent state sufficiency
requires the joint consumer and transition
fibres, not just the directed score's rank.
A source-compatible finite counterexample
is documented in the new owner.

Local SymPy exact-rank/Gram checks passed;
no actual trained checkpoint singular-value
receipt, model precision or hardware runtime
was supplied. This is the next high-alpha
MAX-CUT link between the user's original
compression/sufficiency conjecture and
future inactive-history correctness.


## 17 November continuation: original joint history fibres + precision-receipt handoff

See the new focused owner:
`Docs/roadmaps/X369R4SourceReceiptAndHistoryFibreMaxCut20261117.md`.

The source `HistoryOrbitMoE.step` uses original
signed expert h in orientation, FFN and
transition, even when the C2 + directed
routing logit cannot distinguish those h.
A source-compatible exact counterexample
now demonstrates same **entire** ideal R4
routing consumer for `h+=(1,1,1)` versus
`h-=(-1,-1,-1)` under a rank2
zero-sum directed head, yet chosen
orientation score strictly positive for
both, and a licensed FFN first layer
separates their GELU outputs by exactly 1.
A licensed transition can also retain
the differing signed h coordinate.
This is an architecture-existence witness,
NOT a claim about the original fitted
checkpoint's actual FFN weights.

The positive condition is sharper than
'two channels are enough': a history codec
E must simultaneously factor EVERY
admitted execution observer and make
the transition quotient well-defined:

    E(h1)=E(h2) -> O(h1)=O(h2),
    E(h1)=E(h2) -> E(T(h1))=E(T(h2)).

For linear E=P, the exact tests are
rowspace(O) subset rowspace(P),
and `ker(P)` transition-invariant.
SymPy proves an arbitrary-symbolic
2D example `P T^n=Tbar^n P`
for n=1..6, and gives both a
rank3 FFN history observer obstruction
and a positive rank2 restricted
source-compatible observer. The current
fitted model's actual operator rank is
not known. Local independent SymPy
source-fibre tests: **25 checks PASS**
(including the observer-rank augmentation).

**Source receipt gate implemented:**
`scripts/check_x369_r4_source_receipt.py`.
It is read-only, exact-rational, and requires
explicit original model SHA, externally
verified source/export/float-error
provenance fields, original activation,
ALL expert histories, C2 head weights,
C3 directed head weights, expert biases,
q mask, original selected IDs, selected
orientation head, and coordinate-wise/
per-pair error budgets. Under these
admitted numerical inputs it certifies
source pairwise TopK and slot margins,
stable mixed q branches, selected
orientation chart, and a selected
softmax-L1 upper bound. It explicitly
reports `source_checkpoint_authenticated_by_this_script=false`
and `full_recurrent_state_certified=false`.
The provenance flags themselves are
untrusted declarations unless a real
source owner separately authenticates
the original checkpoint and numerical
receipt.

**Synthetic fail-closed regression:**
`scripts/check_x369_r4_source_receipt_selftest.py`.
Independent local analogous script tests:
**13/13 PASS** (2 coherent/mixed accepted,
6 missing-provenance rejections,
2 selected-ID order rejections,
2 zero-orientation refusals,
1 mixed-q mean-tie refusal).
A standalone source-adapter test with
the same fixture returned rational
softmax budget `594441/8388608`.
These are explicitly SYNTHETIC receipts,
not actual trained-Leech evidence.
The precise committed adapter version
has not separately received a
GitHub/CI execution receipt.

**Existing original Leech source owners
recovered and preferred:**
`scripts/audit_x369_projected_router_score_weld.py`
and
`scripts/run_x369_r4_three_arm_source_maxcut.py`,
both in `chboishabba/LeechTransformer` PR #5.
The former's float32 comparison
`atol=2e-4,rtol=3e-5` is a
test tolerance, NOT an independently
certified original quantizer error
guarantee. The latter requires repaired
C2 source checkpoint hash and native
R1/SLR development split provenance.
Do not re-implement these original
source producers in DASHI; consume
their receipts when available.

**Current decisive remaining gates:**
real checkpoint + source export
authentication, source-independent
precision/rounding evidence,
actual learned W1/transition rank or
consumer-fibre compatibility, repeated
per-step strict q/topk/orientation
certification, and independent
grokking/Sophontic/trialectic semantic
consumers. No CI/Agda or physical
GPU run requested or asserted.


### 17 November original precision-plan follow-up

New SymPy stand-in:
`scripts/check_x369_r4_conditional_roundoff_sympy.py`
and detailed explanation in
`Docs/roadmaps/X369R4SourceReceiptAndHistoryFibreMaxCut20261117.md`.

A conditional ideal normal binary32
arithmetic contract with unit roundoff
2^-24 was encoded by exact Fraction
outward intervals, retaining original
C2 abs-history head and expert bias.
The disclosed unfused directed correlation
and shared-head fused scoring plans
both preserve the synthetic 4-expert
coherent and mixed selected top2
under those admitted assumptions.

The precision tradeoff is adversarial:
the **fused** plan has a *slightly wider*
conservative selected-pair roundoff
interval on both fixtures, despite
fewer scalar arithmetic operations.
Coherent ~5.96e-6 vs original ~5.84e-6;
mixed ~7.51e-6 vs original ~7.39e-6.
Independent local 15-check rational
interval test PASS. It is NOT an
actual original Torch/ROCm floating
kernel receipt: execution graph,
FMA, subnormals and TF32 mode
must be authenticated separately.

The next proper source step remains
precision provenance from Leech's
existing original scorer/checkpoint
producer. Do not substitute that
producer's comparison test tolerances
for rigorous uniform error bounds.


## 17 November GELU parity source-donor reuse and recurrent chart max-cut

**Priority owner:** `Docs/roadmaps/X369R4GELUParityChartHistoryMaxCut20261117.md`.
**Executable SymPy:** `scripts/check_x369_r4_gelu_parity_history_sympy.py`;
its source-specific bounds are also welded into
`scripts/check_x369_r4_end_to_end_envelope_sympy.py`.

Recovered and **reused**, not cloned, the early 31 October
`Docs/LeechGELUParityHistoricalSafetySteelman20261031.md`,
`LeechSignedHistoryExpertBidiExact.agda`,
`LeechOddOnlyApproximationObstructionExact.agda` (F02a),
`LeechLayerErrorTransportExact.agda` (F07),
`PhysicalInvolutionParityExact.agda`, and existing
`QuantisedSearchBoundsExact.agda`. The early scalar real
GELU `g(-z)=g(z)-z`, odd half `z/2` and even
`z erf(z/sqrt2)/2` were ALREADY documented;
the new proof-development specialises them to the
ORIGINAL learned signed expert with biases and history.

For the real source FFN
`F(z)=W2 GELU(W1z+b1)+b2`, let
`O_F=(F(z)-F(-z))/2` and
`E_F=(F(z)+F(-z))/2`. Then for
original **nonzero** oriented charts ±,

    y_sigma(z) = sigma F(sigma z)
               = O_F(z) + sigma E_F(z),

and the exact chart jump is
`y_+(z)-y_-(z)=2E_F(z)`.
The source affine signed history transition
has pre-cap chart jump
`H_+-H_- = 2(T_y E_F(z)+b_T)`;
the real radial history cap is nonexpansive.
This does not assert learned `F` is odd and
does not omit original `b1,b2,b_T` biases.

A **new guarded approximate consumer** is available:
with identical selected expert set and admitted q
branch, an orientation sign flip need NOT be rejected
when the consumer only requires a bounded numeric
mixture/history discrepancy. It contributes an
explicit `2||E_F||` selected-output residual and
`2||T_yE_F+b_T||` pre-cap history residual, which
can feed the existing F07 layer-error transport.
To preserve the actual returned `signs` metadata,
strict chart parity remains necessary.
The source's `sigma=0` unique fixed point is
handled separately: its output/history are zero
even with internal learned biases.

**Sharp real GELU Lipschitz constant:** exactly

    Lg = (1+erf(1))/2 + exp(-1)/sqrt(pi)
       = 1.128904145185...,

improving the older loose bound
`1+1/sqrt(2*pi*e)=1.2419707245...`.
The biased FFN even component has centred
Lipschitz coefficient `Lg-1/2` and
a **quadratic curvature** majorant
`||E_F(z)-F(0)|| <=
 ||W2||*||W1 z||²/sqrt(2*pi)`.
This means small preactivations have a small
chart-even residual ONLY if the learned
`F(0)=W2 GELU(b1)+b2` is also small.

**Early F02a quantitative cross-pollination:**
for real Euclidean mirrored output pair `F+,F-`,
an odd student S obeys the exact identity

    (||F+-S||²+||F-+S||²)/2
      = ||E_F||²+||O_F-S||².

The minimum odd-only pair MSE floor is
`||E_F||²`; the exact output chart-jump
squared is `4||E_F||²`. The scalar/finite
Euclidean proof is checked with SymPy
(1,2,3,4 output coordinates), NOT falsely
promoted to an Agda-kernel accepted
inner-product F02b theorem.

**Gate status:** Source math / SymPy parity identities
and real bounds advanced; original fitted
`W1,b1,W2,b2,T_y,b_T` spectral norms, original
float GELU rounding, source chart/softmax precision,
and full future-history/semantic acceptance remain OPEN.
No model timing, GPU, Agda or CI run claimed.


## 17 November: corrected *early* GELU/kink prior-art attribution

The actual **facilitation-before-suppression** owner is
`DASHI/Cognition/ResponseKink.agda`, whose
`RecruitmentSuppressionProfile` and `profile-shape`
check a four-level rise–rise–overload-decline shape.
The pasted attribution to
`DASHI/Cognition/Utterance/AdmissibilityGate.agda`
is incorrect on the inspected default branch:
that module governs literal vs symbolic
utterance admission, not this profile.

The original cognitive computation owner
`DASHI/Cognition/AnesthesiaLanguagePhaseDynamics.agda`
has the distinct exact cubic margin
`10+4t-t³`, giving margins
`(+10,+13,+10,-5)` and hysteresis/stack
rebuilding. The separate HPA owner
`DASHI/Governance/SituatedHPARegimeFlexibilityExact.agda`
**reuses the canonical ResponseKink** as a
hypothetical ordinal stress-response
profile and explicitly prohibits inferring
an actual clinical condition or deterministic
high-load adrenal-exhaustion claim.

New source-written reuse bridge:
`DASHI/Cognition/PNF/X369R4EarlyKinkSourceWeldExact.agda`.
The bridge needs an explicit equality between
an actual original R4 observable and the
existing canonical profile's response,
before transporting the profile inequalities.
No verified R4 response/source record is
supplied, and no kernel run is asserted.

Exact SymPy candidate:
`scripts/check_x369_r4_early_kink_sympy.py`;
independent local execution: **14 grouped checks
passed**. A rational load-attenuated candidate
has profile values `(1,80/17,6,208/43)`;
a separate standard GELU-times-cubic-attenuation
example has values approximately
`(0,0.791853879,1.302999824,1.114772207)`.
Neither is claimed to be implemented or
fitted by the original R4. Unattenuated
positive-input GELU is an explicit negative
control: its increasing response cannot
establish the overload decline. A radial
history cap gives saturation, not necessarily
suppression of a selected expert's output.

The source-facing *conditional* evidence
checker `scripts/check_x369_r4_kink_source_receipt.py`
accepts only four source-provenance-bound
ordered loads and strict response intervals
for the SAME observable, checkpoint and
history revision. Companion
`scripts/check_x369_r4_kink_source_receipt_selftest.py`
adds 14 synthetic positive/negative fixtures.
Claims of source authentication or fitted
overload mechanism remain OPEN.

**Next actual maximum cut:** define and
measure an R4 original response observable
(e.g. selected contribution norm, fixed-expert
quality, router margin) as a function of
controlled increasing load with fixed
source checkpoint/history provenance.
Discharge the three original order
comparisons with response interval bounds,
then distinguish source mechanism by
independently tested attenuation,
topk competition, signed FFN dynamics,
history cap or hysteresis. Do not
derive shape from the earlier GELU
parity or correlated logit equivalence.


**Critical Nat refinement of original early Kink owner:**
`ResponseKink.response` is `Input → Nat`,
not a real-valued activity. The candidate rational
envelope admits an integer-coded four-stage witness
`floor(r(t))=(1,4,6,4)`. The attenuated exact
Gaussian GELU candidate has
`floor(10*g(t)*A(t))=(0,7,13,11)`;
unscaled floor loses strict shape. This shows
why numerical source-to-Nat admission must
preserve strict margins AFTER quantization.
Local independent SymPy reconstruction now
passes 19 grouped checks. The source receipt
adapter now fails closed without explicit
Nat codomain, integer response, claimed
external observation-projection verification,
and an interval enclosing that response.
Its 18-case synthetic selftest is source
written but not directly run as the exact
committed file. No real trained Leech
overload-shape source evidence exists here.


## 17 Nov highest-alpha early-kink continuation: ORIGINAL R4 topk competition witness

New source-shaped SymPy work:
`scripts/check_x369_r4_topk_kink_sympy.py`
and `scripts/check_x369_r4_topk_kink_source_gate_sympy.py`.
Full construction and limitations:
`Docs/roadmaps/X369R4EarlyRecruitmentSuppressionWeld20261117.md`.

Unlike the earlier proposed GELU-times-attenuation
example, this uses the ACTUAL
`HistoryOrbitMoE.select_source_experts`
coherent C2+C3 residual score family,
learned expert biases, topk and
selected-score softmax. The learned
baseline C2 head is zero for the
explicit fixture, as permitted by
the original parameter space.
Activation varies as `x=t*x0`,
all four expert histories are held
at the SAME authoritative reset
state per counterfactual, and
the source-compatible orientation
score is strictly positive
for every selected expert.
The selected FFN output can be
made constant by W2=0 and
an appropriate output bias.
No new numerical gate or
learned attenuation is inserted.

With expert relative logits

    L(t)=(8, 3+4t, -11+9t, -13+10t),

topk2 produces at t=0,1,2,3:
`(0,1),(0,1),(1,0),(3,2)`.
The selected output of only expert 1
is respectively

    1/(1+e^5), 1/(1+e), 1/(1+e^-3), 0.

The original canonical Nat response
after floor(scale10) is `(0,2,9,0)`,
strictly satisfying the original
`ResponseKink.profile-shape`.
All selected/outside and
within-selected routing margins
are strictly positive; minimum
cross-margin 1.

**Matched causal/structural ablation:**
fix the selected pair at (0,1)
with the same logits and source
softmax. The response is then
`sigmoid(4t-5)`, strictly increasing
and has NO overload fall.
This isolates selected-set
replacement as a sufficient
architectural mechanism for the
early four-stage kink on the
disclosed R4 parameter family.
It does NOT infer actual trained
Leech mechanism, FFN/GELU
overload suppression or on-policy
recurrent behavior.

The joint script composes the
existing source-relative pairwise
quantization/mixed-q/orientation
receipt gate rather than inventing
another proof. Under synthetic
rational 1/65536 input/parameter/
history bounds, it checks
original coherent selected IDs
and strict chart margins at every
load, and certifies a Nat cell
via rational exponential brackets
plus the selected-softmax error
envelope. It explicitly refuses
forcing the overload source IDs
to the fixed-route control and
refuses to promote the coherent
zero-load fixture to the mixed
q arm whose gate is undecidable
under positive error. All
SHA/provenance/precision flags in
this fixture are declarations,
not original checkpoint receipts.

**Core new mathematical boundary:**
on any fixed selected pair and
fixed history input ray, affine
source relative logits combined
with constant scalar expert
outputs produce a monotonic
two-point logistic interpolation.
The overload limb needs a selected
set change or a genuinely changing
expert output/other consumer.
This is the correct separation
between the early cognition
shape contract, the source
router, and arbitrary GELU
parity or biology.


## 17 November source-execution max-cut — historical (SUPERSEDED API and execution status)

> **SUPERSEDED:** The optional three-value `return_logits` API below was reverted. Use the unchanged original two-value API and scoped dispatcher observer. Native synthetic execution status is superseded by the current ledger.

Original repository: `chboishabba/LeechTransformer`, existing PR #5,
branch `experiment/x369-r4-fair-c2c3-residual-20261115`.

**No surrogate router was introduced.** Existing
`models/history_orbit_moe.py` now accepts optional
`select_source_experts(x,history,return_logits=True)`,
returning `(ids,weights,logits)` from the SAME original
route/score computation. Its default
`return_logits=False` preserves the original
2-tuple API and ordinary training/inference semantics.

New original-source consumers:
- `scripts/check_x369_r4_native_topk_kink.py`:
  CPU smoke test of the ACTUAL HistoryOrbitMoE class
  with source-valid synthetic d=6 coherent R4
  weights and histories. Checks source logits,
  native topk slots, signed expert FFN output,
  source `step` versus `execute_selected`
  replay and full selected histories;
  asserts the strict Nat response `0,2,9,0`.
  The *matched* fixed pair [0,1] has
  strictly increasing response and
  no overload limb.
  Optional `--emit-probe-dir` creates a
  genuine native **synthetic** state_dict
  and matching four-load JSON for
  the checkpoint probe.
- `scripts/probe_x369_r4_kink_checkpoint.py`:
  exact original-source same-checkpoint
  CPU probe. Uses weights_only
  `torch.load` and `strict=True` state
  dictionary admission (an explicit
  `--state-prefix` handles module
  embedding), computes real checkpoint
  byte SHA256, source input and history
  byte SHA256, retains original all-E
  inactive histories, and independently
  resets the SAME history for four
  increasing activation loads.
  Evaluates original `select_source_experts`,
  `step`, and `execute_selected`,
  rejects same-source selected/sign/history
  replay mismatch, and computes an
  actual-source-logit/softmax-based
  forced-route selected-only ablation.
  Its response type is explicit
  coordinate or L2 norm; Nat
  projection uses an explicit scale.
  The return JSON separates native
  `nat_kink_observed` from
  `fixed_route_continuous_kink_observed`,
  and **explicitly** marks
  `certified_float_error_intervals=false`,
  `recurrent_hysteresis_certified=false`
  and heldout quality uncertified.
- `docs/x369_r4_native_kink_probe.md`:
  usage instructions and source
  promotion/non-promotion boundaries.

To run from the original Leech
repository root with installed
source dependencies:

```bash
python scripts/check_x369_r4_native_topk_kink.py \
  --emit-probe-dir .leech-r4-kink
python scripts/probe_x369_r4_kink_checkpoint.py \
  --checkpoint .leech-r4-kink/synthetic_history_orbit_moe_state_dict.pt \
  --input .leech-r4-kink/synthetic_original_load_input.json \
  --output .leech-r4-kink/synthetic_probe_result.json
```

**Independent LOCAL exact-rational verification COMPLETED**
in this conversation of the source formula and its
correlated paired-error/response Nat cells,
for each load t=0,1,2,3:
- logits `(8,3,-11,-13)`,
  `(8,7,-2,-3)`, `(8,11,7,7)`,
  `(8,15,16,17)`;
- strict ordered top2 `(0,1)`,
  `(0,1)`, `(1,0)`, `(3,2)`;
- exact Nat `(0,2,9,0)`;
- synthetic pairwise score errors and source
  Nat interval margins remain admitted.

That local rational audit reproduced
the corresponding symbolic mathematics.
**The exact committed original Torch scripts,
the fitted checkpoint and the new Agda
modules have NOT been executed or kernel
accepted** in this chat.

Both TOE entry points now import the
canonical finite R4 kink witness with
the unique `r4FiniteKinkSourceShape`
public projection:
`DASHI/EverythingTOESymmetryResolved369.agda`
and `DASHI/Unified/Everything.agda`.
No change to the core early
`ResponseKink.agda` owner or ESD modules.

**Remaining decisive physical/source gates:**
real owned R4 source checkpoint + actual
history revision, four-load choice with
measured source response, actual counterfactual
replay, independently certified floating
interval/Nat-cell errors, original R1/SLR
development/heldout provenance, and true
on-policy recurrent hysteresis (not a
reset-history comparison). No
clinical/endocrine claims.


## 17 Nov continuation — historical (SUPERSEDED API, tied fixture and execution status)

> **SUPERSEDED:** The optional logits API and old expert-3 parameters (10,-13) below are not active. The old (8,3,7,7) cutoff is tied and cannot certify a selected pair; use (11,-16) and the corrected strict fixture. See current acceptance ledger.

Original Leech PR #5 updated, with:
- `models/history_orbit_moe.py`: default original
  `select_source_experts(x,h)` tuple unchanged; explicit
  opt-in `return_logits=True` returns SAME
  calculated original source logits (not a
  separately computed router).
- `scripts/probe_x369_r4_kink_checkpoint.py`:
  original checkpoint-byte-hashed same-reset
  four-load source execution and matched
  source-logit forced selection.
  **Repaired actual runnable blocker:** its
  JSON input uses numeric strings, which
  `torch.tensor(["1","0"],dtype=...)`
  rejects. The original producer now
  recursively parses only finite
  numeric scalar strings/integers/floats
  into the requested exact source tensor
  shape and rejects NaN, Inf, Bool and
  invalid shapes, plus disallows
  implicit dtype or coerced Nat scale.
  Added original repo-root source
  package path handling for
  `python scripts/...py`.
  The forced-route comparator now
  checks its **same Nat projection**
  separately from continuous shape;
  the result explicitly marks that a
  fitted causal mechanism is NOT
  certified.
- `scripts/check_x369_r4_native_topk_kink.py`:
  synthetic native model/FFN/topk test
  now verifies default API and opt-in
  logits agree, emits source state_dict,
  reloads the exact bytes with
  `strict=True`, replays source step
  and selected-only execution, and
  rejects malformed JSON arrays.
- `scripts/probe_x369_r4_history_path_dependence.py`:
  NEW same-checkpoint, same initial
  full history, same second-step load
  and clock, different one-step
  *prefix interventions* followed by
  the original source `step`.
  Unlike a four-load RESET curve,
  this tests a genuinely updated
  ORIGINAL recurrent history state.
  It records full-history hashes and
  selected scores/IDs/weights/signs.

**SUPERSEDED tied-fixture history (retained solely for provenance; not a valid deterministic witness):**
the previous source-legal d=6,
E=4 synthetic parameter fixture
has original coherent routing

    L_e(t)=b_e+s_e*t,
    b=(8,3,-11,-13),
    s=(0,4,9,10).

After a prefix load 0, original
topk selects (0,1) and ZERO source
transitions replace their histories
with zero; at the common second-step
load t=2 the logits are
`(8,3,7,7)`, selected (0,2),
output Nat 0.
After a prefix load 3, topk
selects (3,2), whose histories
are replaced with zero; at the
SAME second-step t=2 and same
clock index 1 the logits are
`(8,11,-11,-13)`, selected (1,0),
output Nat 9.
An independent exact-source-formula
local run checked **4/4** finite
history-path facts. This is a
counterexample to inferring a
same-load source response from the
load scalar ALONE when the active
retained histories may differ.

**Existing mathematical reuse:**
new `DASHI/Cognition/PNF/X369R4HistoryLoadNonFactorabilityExact.agda`
imports `DASHI.Core.IntersectionalNonFactorability`
(not a duplicate quotient constructor).
It defines a two-prefix same-load
finite witness and exposes the
already-proved generic
`witnessRulesOutEveryFlatFactorisation`
and recharting no-recovery laws:
the declared Nat response 0 vs 9
does not factor through the common
second-step load. This source-written
Agda result is exposed from BOTH
`DASHI/EverythingTOESymmetryResolved369.agda`
and `DASHI/Unified/Everything.agda`.

**Local verification performed this round:**
- exact rational/symbolic source
  four-load scores, selected experts,
  native-response Nat 0,2,9,0,
  frozen-route monotonic response:
  **17 independent source-formula checks PASS**;
- original PyTorch numeric-string
  deserialization defect reproduced
  with installed CPU Torch; corrected
  parsing function independently
  reproduced and passed **7 CPU checks**;
- exact same-clock path dependence:
  **4 independent source-formula checks PASS**.

**Still open:** executing exact GitHub
native Torch fixture/probe scripts,
kernel-checking new Agda/TOE imports,
same-source actual R4 checkpoint/history
provenance, independent true
source floating-error bounds across
Nat observation thresholds,
experimentally selected four-load
family, heldout generalisation,
and genuine on-policy recurrent
hysteresis. The current same-clock
two-prefix inequality is
history-dependence, not proof of a
hysteresis loop or biological
allostatic mechanism.
