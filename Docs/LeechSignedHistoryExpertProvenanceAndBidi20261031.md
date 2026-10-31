# Signed-history experts: formal bridge and provenance, 2026-10-31

## Original observation versus hypothesis

On 9 March 2026, Anatolii Kornienko described qualitative differences
between early E8 and Leech-LILA generated stories in
[SPUTNIKAI/sovereign-lila-e8 issue #3, comment 4029035489](https://github.com/SPUTNIKAI/sovereign-lila-e8/issues/3#issuecomment-4029035489).
He reported that an E8 model generated disturbing stories during its
first ~50k training steps and more ordinary/kind stories by ~100k,
whereas Leech-LILA reportedly lacked this early phase. He proposed that
the frozen geometric prior might suppress unwanted semantic modes.
This is a dated, attributed exploratory observation **not** a
controlled safety result or a proof that positive and negative
activation directions correspond to good and evil.

The same discussion records proposed comparisons of geometric-loss
weight `lambda_geo`, stepwise grokking and stable-rank curves. These
are appropriate preregistration axes: hold prompts/training data,
tokenizer, model size, optimiser and sampling constant across
multiple seeds and compare safety behaviours, general language quality
and expert-state/orientation traces. Use independent behavioural
annotations, including refusal errors, not merely a list of
disturbing words, as safety measurement.

## Kernel-checked mathematical target

DASHI Agda PR branch
`feat/leech-history-signed-orbit-bidi-20261031` adds
`DASHI/Reasoning/LeechSignedHistoryExpertBidiExact.agda`.

The finite type `HistoryState` contains trit-valued activation and
trit-valued memory, the global sign is a two-element involution, and
an arbitrary transition `F : HistoryState -> HistoryState` can be
conjugated by the sign action:

    F_minus(z) = I(F(I(z))),  I(I(z)) = z.

This models an expert whose input and historical state are jointly
reoriented; it proves exact finite restore/roundtrip without assuming
`F` itself is odd. The representation has a zero fixed centre
and records that orientation need not be uniquely identifiable there.

This finite algebra is NOT a proof that `models/signed_history_expert.py`
satisfies a Leech lattice automorphism theorem, nor that
`LeechGPT` preserves the same sign through Q/K, softmax and GELU.
A formal model-to-code correspondence still requires a specified float
semantics, signed history version, fixed-locus/tie semantics, and
precise consumer interface.

## Joint empirical BIDI max-cut

1. **History**: compare KV-only, recurrent expert history and history
   ablation. Test full unroll versus split transport/replay, including
   stale decoder state and chart-version mismatch.
2. **Geometry**: compare learned sign-router on raw hidden features
   with admitted 24D basis features, and signed 5/9 & 14/27 routing
   charts with full orientation witness and zero fixed class.
3. **Safety hypothesis**: compare E8, QR-Leech baseline and actual
   lattice-derived kernels (only if implemented), geometric-loss
   ablations, matched training runs and independently evaluated
   behavioural outcomes. No one sign is assigned 'evil'.
4. **Compression**: measure whether the same action witness reduces
   stored expert parameters or network bits per activation, after
   charging orientation, residual, version, decoder state and routing
   bytes. Always reconstruct actual IEEE tensor bits for the original
   consumer unless a stronger end-to-end equivariance proof exists.

The current Leech prototype is experimental, hard ±1 forward routing
with straight-through training gradient, not a demonstrated
safety classifier or completed distributed MoE.
