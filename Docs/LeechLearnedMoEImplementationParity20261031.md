# Learned history-orbit MoE implementation/formalism parity audit

Date: 2026-10-31. Linked implementation:
[chboishabba/LeechTransformer PR #4](https://github.com/chboishabba/LeechTransformer/pull/4),
`models/history_orbit_moe.py`. Formal branch:
[chboishabba/dashi_agda PR #1442](https://github.com/chboishabba/dashi_agda/pull/1442).

## Honest answer: formalism is not as complete as implementation yet

The original `LeechLearnedOrbitMixtureBidiExact.agda` had only two
indexed expert function slots and a single selected dispatch. It
**did not model a weighted mixture**. The new
`LeechWeightedHistoryMoEBidiExact.agda` closes specific structural gaps:

| Python behaviour | Agda formal counterpart | Status |
| --- | --- | --- |
| Multiple distinct learnable expert modules | Two separately indexed arbitrary expert functions plus transitions | Finite 2-slot skeleton, no optimizer |
| Learned expert-history-dependent router | Per-expert state-dependent score functions | Structural |
| Top-k sparse identities | Deterministic top-1 or top-2 of two scores, fixed tie to expert 0 | Finite theorem/program, not torch.topk generality |
| Weighted selected expert outputs | Natural-number weighted sums | Structural, not normalized real softmax |
| Histories only updated for selected expert IDs | Conditional state updates | Structural |
| Consumer-visible route/state trace | Exact encode/decode Receipt for selected route, result and both memories | Finite exact BIDI |
| Full-token vs chunked replay | `segmentReplay` | Finite state-only theorem |
| Sign-conjugate orientation with state | `LeechSignedHistoryExpertBidiExact` | Separate finite theorem; NOT yet welded to weighted top-k |
| Float16/float32 actual tensor transport | None | OPEN |
| Softmax weights and straight-through sign router gradients | None | OPEN |
| Learned training dynamics, quality, safety, and expert balance | None | OPEN |
| Full Leech automorphism and trained consumer equivariance | None | OPEN |
| Agda kernel verification of current branch | Not run | UNVERIFIED |

Do not promote a named generic parameter slot or source-defined
`learnedFamily` into a proof of gradient learning. Do not call
finite weighted natural sums an exact representation of float
softmax. The exact-producer/consumer receipt is an algebraic finite
trace, not the actual bytes of the Leech activation codec.

## Next prioritized cut

1. Run Agda with `--safe` on the new owner and fix elaboration errors.
2. Compose the finite signed involution with the top-k selection
   and an explicit route permutation or corrective witness.
3. Specify general E and k with finite vectors and dependent
   selected indices, together with exact normalized rational or
   abstract semiring weights and a companion converse relation.
4. Formalize the time-indexed full *output trace*, not only final
   memory; prove segment replay of outputs and memory together.
5. Verify the Python model tests, integrate the sparse adapter
   behind a default-disabled flag, then compare held-out task
   quality and lossless transport costs on the real checkpoint.

Provenance: original Leech-LILA architecture (Anatolii Kornienko);
DASHI in-repo sign/orbit, BIDI and parity authorship retained.
Original email observations are experiment motivation, **not** proof
that sign orientation indicates harmlessness. No ESD surface touched.


## Revised implementation counterpart after source integration

LeechTransformer PR #4 now changes the actual `LeechGPT`
forward path under an explicit default-off `moe_experts>=2`
configuration. The `LeechBlock` MoE variant retains real
attention/resonance, replaces FFN, returns updated expert histories
on explicit opt-in, and rejects KV-cache continuation that omits
the required expert histories. Dense mode preserves its original
4-tuple and strict checkpoint parameter structure.
`tests/test_leech_moe_integration.py` was committed to verify
dense checkpoint compatibility, loss/backprop, cache/sequence
equivalence, and history-presence checks but is not yet executed.

The Agda source is still weaker: it has an exact finite
state replay theorem but no multi-layer KV+expert-memory
bisimulation; it also lacks a formal train/eval flag, dropout,
real softmax and optimizer state. The new
`IEEEOrbitSignWitnessBidiExact.agda` proves arbitrary symbolic
payload/sign-bit roundtrip but is NOT the canonical block code
implemented by `scripts/ieee_sign_orbit_codec.py`.
This parity ledger is intentionally fail-closed until executable
tests and Agda kernel checks are completed.
