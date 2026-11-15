# Constructive learned-MoE/federated proof cut — 2026-10-31

This iteration pursues missing obligations rather than declaring the representation layer sufficient.

## New concrete work

1. `DASHI/Reasoning/LeechGenericHistoryActionTransportExact.agda` proves, conditionally and **pointwise for arbitrary E**, that selected-only history transitions commute with an expert-index action when selected status, old history and the expert-specific advance results commute. This includes inactive histories. Its input assumptions are NOT discharged for the real learned router; this is a reusable theorem, not an asserted trained-model symmetry.
2. Existing `LeechGenericTopKActionTransportExact.agda` proves finite weighted total and route-count transport; `LeechFullOutputHistoryTraceBidiExact.agda` supplies the existing two-expert causal replay. To promote all three to real PyTorch, still require exact route permutation/bijection, finite selection uniqueness, normalized floating weights, actual GELU FFN and numeric state-transition refinement.
3. LeechTransformer `scripts/federated_authenticated_session.py` adds explicit HMAC-SHA256 authentication of session + history revision + sequence + payload, and a monotone receiver. `tests/test_federated_authenticated_session.py` covers authentic sequential messages, tampering, cross-session, stale history, replay, gaps and short keys. A local independent source-equivalent Python run reported 3/3 tests passing. This is MAC-only (no encryption) and non-durable (not exactly-once).

## Actual mathematical maximal obstruction

For state z=(x,H), selected set S(z) and positive normalized weights w_e(z), full action equivariance requires:
  S(gz)=pi(S(z)), w_{pi(e)}(gz)=w_e(z);
  F_{pi(e)}(gz)=g_Y F_e(z);
  U_{pi(e)}(gz)=g_H U_e(z);
with unselected histories transported and complete causal trace preserved. Current generic Fin-E proofs discharge the additive aggregation and conditional history-index transport, not these hypotheses for independently trained model parameters.

When learned parameters do NOT satisfy these equations, one must either train/fit an action-compatible family with a measured loss and held-out validation, or encode exact differences and pay their real network/compute cost. Semantic counterarguments and ethical assessments must not be identified with the action. Existing Sophontic PRs #1094/#1095 and non-antipode core remain the owner.

## Security authority boundary

The authenticated envelope assumes a pre-shared secret, exact session and trusted current revision. It is not confidentiality/AEAD, resilient session persistence, a remote-worker scheduler, a distributed transaction log, or a verified end-to-end crypto protocol. Real state-transition acceptance must use atomic (verified message, execution, durable result, next revision) commits and anti-replay recovery after crash. HMAC length leakage does not address codec compression side-channels.

## Reuse and remaining work

Existing canonical 3/9/27, 5/9 and 14/27 antipodal carrier, S3 push/pop, C2/C3 369, consumer quotient base-change, exact surface+residual, time-indexed fibres, GELU parity, triadic codecs and federated authority owners must be imported and reconciled before duplicate abstraction. No ESD edits. Never claim an action fingerprint proves a same-object Monster/Leech representation.

Kernel status: Agda not run. Python session local smoke passed; full LeechTransformer and remote-worker integration tests not executed. Still OPEN: joint real-valued model proof, trained action fit, nontrivial exact residual codec, remote execution, AEAD with crash-safe ledger, loss/RTT sweeps and quality/safety trials. They are objectives to solve rather than reasons to stop.
