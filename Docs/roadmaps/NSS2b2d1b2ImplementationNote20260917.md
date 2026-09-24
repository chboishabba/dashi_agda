# NS periodic-B S2b2d1b2 implementation note — 2026-09-17

This branch normalizes the existing periodic-B quantitative min-cut. It does not claim to solve the open estimate and does not promote A/C/D.

## Exact same-object spine

1. `NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact` retains the signed division-free coherent-covariance pair-difference identity on the literal physical fixed-output fibre.
2. `NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact` owns the finite second-moment compiler; `NSTriadKNR571GateAEnvelopeCrosswalkExact` still leaves the transported-state derivative envelope open.
3. `NSTriadKNFourSignInnerFibreGramBoundaryRound577Exact` -> `NSTriadKNFixedOutputFourSignFibreMajorantRound578Exact` -> `NSTriadKNLiteralPhysicalOutputFourSignGramRound579Exact` reaches the literal four-helicity fixed-output Gram carrier, while the signed residual remains unpaid.
4. `NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact` is the live cutoff-uniform commutator consumer. `NSTriadKNModernNestedSchurToCommutatorBidiRound577Exact` already compiles into that consumer given its signed-majorization and cutoff-uniform-envelope receipts.

The new `NSTriadKNS2b2d1b2QuantitativePaymentExact` packages those facts as:

- an inhabited `S2b2d1b2SameObjectSpine`;
- an uninhabited `S2b2d1b2QuantitativePayment` whose four fields are the actual remaining mathematical leaves.

## Remaining payment

The branch intentionally keeps these source-status coordinates false:

- R571 transported-state derivative envelope;
- literal R579 signed four-sign Gram residual;
- signed response majorization into the R568 Schur output;
- cutoff-uniform R568 envelope.

Only an actual same-object inhabitant may promote the quantitative status.

## Proof-search constraints

- Preserve the signed covariance/four-sign Gram structure; do not take absolute values before the signed recombination has been exposed.
- Do not replace the R577--R579 route by a fibre-cardinality loss that reintroduces cutoff dependence.
- Any quantitative constant must be explicit and independent of the Galerkin cutoff.
- The theorem and downstream adapter must remain on the same literal physical fixed-output fibre unless an explicit typed adapter is provided.
- Do not infer A from B. Forced C/D constructions are provenance/donor lanes unless a typed forcing-independent adapter is supplied.

## Regression semantics

The focused regression is authority-correct rather than theorem-forcing:

- already-owned structural attachments are required to be `true`;
- genuinely unpaid analytic coordinates are required to remain `false`.

A regression that simply requires the open mathematical theorem to become `true` would turn bookkeeping into proof authority and is therefore not the contract used here.

## Validation boundary

A recovered Agda 2.8 run reached the pre-existing covariance owner and reported a parse error at its `rewrite decayMeaning | selfMeaning` clause before reaching the new #1002 owner. This branch includes a parse-only layout normalization of that clause, matching working repository syntax. No fresh post-fix Agda kernel receipt is available in this chat, so the exact head remains source-constructed / not currently kernel-revalidated.
