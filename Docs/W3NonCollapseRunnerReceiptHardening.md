# W3 Non-Collapse Runner Receipt Hardening

Date: `2026-05-13`
Status: `runner-side complete; provider-grade external receipt absent`
Owner: `Noether-W3`

This surface hardens the current W3 non-collapse boundary without promoting W3.
The runner-side evidence is the frozen t43 comparison artifact:

```text
logs/research/w3_frozen_3205d74_t43_comparison_20260513.json
```

The Agda receipt is:

```text
DASHI/Physics/Closure/HEPDataW3NonCollapseWitnessReceipt.agda
```

## Required Runner Check

The checker must verify that the frozen comparison artifact:

- has SHA-256
  `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238`;
- has `comparison.status = candidate-pass-no-authority-token`;
- has `comparison.chi2PerDof = 2.1565191176275618`;
- contains exactly `18` per-bin rows;
- records a runner-only non-collapse witness at bin `12`;
- records prediction `0.0486590199823977`, data `0.049758`,
  uncertainty `0.00048197510309143566`, and pull `-2.280159308132989`;
- records `witnessPullNonZero = true` and `witnessPredDataDistinct = true`;
- records `providerGradePayloadPresent = false`; and
- records `externalNonCollapseWitnessReceiptConstructed = false`.

The checker must also verify that these literals match the canonical Agda
receipt fields in `canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt`.

## Provider Boundary

This hardening is not a substitute for
`W3AcceptedEvidenceAuthorityToken`. Provider-grade external non-collapse remains
absent until an accepted provider supplies the constructorless
`HEPDataExternalNonCollapseWitnessReceipt` and the W3 authority response supplies
or rejects the exact token. Local runner evidence can be checked and packaged,
but it cannot self-issue W3 authority.
