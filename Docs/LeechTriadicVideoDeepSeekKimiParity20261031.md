# Triadic video codec / external sparse MoE parity ledger (2026-10-31)

Linked LeechTransformer branch: `experiment/consumer-preserving-multiscale-codec-20261031`.
Primary sources explicitly inspected:
- `chboishabba/dashitest/video_bench_reuse.py` implements global
  signed-trit block canonicalization `min(signature, signFlip(signature))`.
- `chboishabba/dashitest/scripts/gen_codec_E_seq.py` computes
  *magnitude only* mean-absolute-trit band energies. This has
  no signed inversion receipt and must not be promoted to exact codec.
- `DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda` already
  requires orientation, deterministic decoder, correction, and
  charged side information.
- `DASHI/Physics/Closure/LightTransportFibreClosure.agda` is an abstract
  proof/receipt interface, not the source of a verified 600-frame
  0.032-bpp numerical codec result in the inspected lines.

External engineering comparators, attributed to original authors:
- DeepSeek-V3: arXiv:2412.19437; 1 always-active shared expert,
  256 routed experts, 8 selected, node-limited routing and
  load-balanced specialization.
- Moonshot AI Kimi K3: https://www.kimi.com/en/blog/kimi-k3 ;
  896 experts, 16 selected, Stable LatentMoE, Kimi Delta Attention,
  and Attention Residuals. Do not confuse with Kimi K2 (384/8).
- Their sizes are reference architectures, NOT an empirically
  determined optimum for our 384-width Leech-LILA.

New implementation `scripts/ieee_sign_orbit_codec.py`
implements the sign action as exact IEEE little-endian sign-bit XOR,
not numeric negation, per 24-element block. It emits the canonical
block, a packed one-bit orientation witness per block, and a full
layout/count header plus DEFLATE payload. `decode_orbit` reverses it.
`tests/test_ieee_sign_orbit_codec.py` tests bytes with arbitrary
NaN payloads, signed zero and random values.

Existing finite Agda `LeechSignedHistoryExpertBidiExact.agda` proves
involutive sign/restore but on balanced trits rather than IEEE bytes.
**Do not equate these carrier operations** without a bridge.
The next exact mathematical correspondence requires:
  (1) finite byte vector bit-XOR sign action,
  (2) packed witness bit retrieval,
  (3) canonicalization/witness inversion,
  (4) entire frame reconstruction, and
  (5) actual model consumer preserving the decoded bytes.
And the real performance discriminator charges orientation headers
and compares `sign-orbit` to `byte shuffle` on typed Q/K and
per-expert history arrays, not raw image video rates.

Verification: GitHub files written and regression tests added.
No new actual Leech capture measurement or Agda kernel execution
is claimed. No ESD surfaces edited.
