# OpenAI Math Corpus Integration Design

This branch mirrors the approved cross-repository architecture used by `dashi_lean4`.

## Goal

Record the pinned OpenAI mathematics corpus as an external formal-source authority in Agda without treating Lean proofs as Agda proofs.

## Immutable upstream pin

- repository: `openai/math`
- commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- license: Apache-2.0
- Lean toolchain: `leanprover/lean4:v4.34.1`
- formalization catalogue: `lean/formalization.yaml`

## Authority firewall

```text
OpenAI manuscript claim
!= formalization catalogue entry
!= upstream Lean declaration
!= upstream Lean kernel receipt
!= DASHI Lean same-object port
!= Agda imported-formal-source receipt
!= Agda theorem
```

The Agda layer may record exact upstream identities and formal theorem sources, but theorem promotion inside Agda requires an Agda proof or a separately declared trusted cross-kernel mechanism.

## Initial max-cut

- exact upstream pin and toolchain receipt;
- explicit cross-prover promotion states;
- routing-only atlas for live DASHI mathematical programmes;
- focused `Everything.agda` rollup;
- regression owner created before production owners;
- no kernel-green claim without execution evidence.
