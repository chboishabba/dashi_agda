# P versus NP: RSA / Shor / recoverable-quotient cross-pollination

## Purpose

This tranche updates the older P-versus-NP boundary with the repository's later
RSA, Shor, recoverable-quotient, consumer-reduction and hyperfabric machinery.

It does **not** claim P = NP or P != NP.

The central separation is:

```text
same mathematical consumer
!= same computational model
!= same execution path
!= same cost coordinate
```

## Exact finite witness

The existing factor-producer receipts for 15 and 21 expose identical
`FactorEvidence` at the arithmetic consumer while retaining distinct producer
classes:

```text
classical order-finding producer
quantum Shor producer
```

Thus equality of a verified factor does not identify the producer or its
resource profile.

The existing Shor comparison already records:

```text
common order consumer                         true
same order implies same execution path        false
classical transitions = quantum gate count    false
```

## Structural-search template

The Shor/RSA symmetry owner supplies a genuine positive template:

```text
exact action / hidden period
  -> Fourier transform
  -> recover period
  -> classical split
  -> verified factor
```

The later generic infrastructure gives reusable shapes for:

```text
consumer-relative reduction
recoverable quotient / reopening
selected compatible hyperfabric sections
explicit seam/interface compatibility
```

These structures can organize a search reduction only after the relevant
consumer invariance, recovery and cost obligations are paid.

## Classical P-vs-NP boundary

The standard compiler remains unchanged:

```text
NP-complete target in deterministic classical P
  -> P = NP
```

A quantum factoring producer is not an inhabitant of that classical `InP`
premise, and factoring is not promoted to NP-complete.

The research frontier is therefore split explicitly:

```text
generic Cook-Levin / CNF polynomiality                  open
uniform deterministic-classical recovery for NP-complete witnesses   open
genuine classical super-polynomial obstruction          open
classical P-versus-NP resolution                        open
```

The old `genericCookLevinCNFPolynomiality` authority boundary remains a real
formalisation residual, but no longer exhausts the research frontier.

## Files

- `DASHI/Mathematics/Complexity/RSAQuantumShorPvsNPCrossPollinationExact.agda`
- `DASHI/Mathematics/Complexity/RSAQuantumShorPvsNPCrossPollinationValidation.agda`

The validation module is imported by
`DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationValidation`.

## Certification boundary

This connector-authored tranche is source-written.  No local Agda executable or
fresh kernel receipt was available in the authoring session, so no kernel-green
claim is made until the exact branch head is checked.
