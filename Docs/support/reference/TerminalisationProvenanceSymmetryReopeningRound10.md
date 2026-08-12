# Terminalisation, Provenance, Symmetry, and Reopening — Round 10

This tranche stacks on the canonical reopenable-evidence / PNF branch and adds the missing exact core identified by the terminalisation, Calabi–Yau symmetry, P-vs-NP, and cryptographic-reopening discussions.

## 1. Terminalisation is stronger than idempotence

`DASHI.Core.SelfSealingTerminalisationExact` separates:

1. idempotence of a classifier;
2. a constructive non-injectivity / distinction-loss witness;
3. closure of a declared terminal region under counterevidence.

A separate `CorrectiveReopeningWitness` proves the opposite property: some correcting evidence exits the terminal region. The theorem

`selfSealingContradictsCorrectiveReopening`

shows these cannot coexist.

This is deliberately generic. No political, legal, clinical, or psychological label is built into the type.

## 2. Memory is not command

`DASHI.Core.TerminalisationArchitectureExact` factors event/history from classification/action and introduces exact finite future-cone accounting. The finite core uses `optionCount`; the Shannon effective count `exp(H)` is left to a later real/transcendental layer rather than smuggled into Nat arithmetic.

`DASHI.Cognition.PNF.MemoryCommandSeparationExact` then instantiates the existing `MemoryFibre` and proves for the repository's literal extinction operation:

- remembered EventPNF is preserved;
- memory provenance is preserved;
- action weight becomes zero.

So the current repo now has a machine-checkable instance of:

`memory preserved + command changed`.

## 3. Classification edge is not identity

`TerminalisationArchitectureExact` carries classification as a record edge `(subject, class, evidence, revision)`. `PropositionIndependenceExact` additionally keeps proposition assessments local and process/diagnosis-style state on a separate typed axis. There is deliberately no constructor allowing one local proposition assessment to settle all other propositions.

## 4. Recall/projection drift is a constructive witness

`RecallProjectionNoncommutationWitness` does not assert that every lossy memory system drifts. It records the exact witness needed to establish drift for a particular projection and prior-conditioned reconstruction:

- original fine state;
- prior;
- reconstructed state;
- proof that reconstruction is the chosen pseudo-inverse result;
- proof that it differs from the original.

This is the correct fail-closed formulation of `Recall ∘ projection != history`.

## 5. Protected-provenance recovery replaces global inversion

`ProtectedProvenanceRecovery` asks only that an application-selected critical projection survive reopening. It therefore models the stronger rule:

> compression is permitted; destruction of responsibility-relevant provenance is not.

This composes naturally with the existing exact `ProvenanceBearingQuotient` / `DynamicConsumerSafety` stack.

## 6. Honest finite symmetry stratification

`DASHI.Core.FiniteC3OrbitStabilizerExact` introduces an explicit C3 group action and proves the group laws by finite exhaustion.

It contains two strata:

- regular orbit: orbit size 3, stabilizer size 1;
- fixed point: orbit size 1, stabilizer size 3.

Both exact orbit–stabilizer cardinality identities are proved. This gives a literal finite witness of the principle:

`enhanced stabilizer -> smaller orbit`.

`DASHI.Core.C3OrbitProvenanceQuotientExact` then turns the regular orbit into a genuine provenance-bearing quotient: all three points project to one orbit label, while a retained point receipt reopens the exact fine state.

This is the finite, non-numerological bridge to the Calabi–Yau discussion. It does **not** formalise Calabi–Yau geometry, Greene–Plesser resolution, Hodge theory, or homological mirror symmetry.

Reference: John D. Dixon and Brian Mortimer, *Permutation Groups*, GTM 163, Springer (1996), DOI `10.1007/978-1-4612-0731-3`.

## 7. P-vs-NP-adjacent object: efficient recoverable quotient

`DASHI.Core.EfficientRecoverableQuotientExact` separates:

- decision projection;
- witness-recoverable quotient;
- receipt construction;
- reopening;
- receipt length;
- model-relative reopening cost.

A concrete `PolynomialBound` is represented by an exponent and coefficient proving

`cost(n) <= c * (n+1)^k`.

An `EfficientRecoverableFamily` therefore requires polynomial certificates for quotient cost, receipt construction, reopening cost, and receipt length separately.

This formalises the useful research question:

> when does a small/easy quotient retain a polynomial-size receipt with polynomial-time witness reopening?

It does not prove `P = NP`, `P != NP`, NP-hardness, or any lower bound for SAT.

Reference: Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, CUP (2009), DOI `10.1017/CBO9780511804090`.

## 8. Cryptographic reopening is model-relative

`DASHI.Crypto.ReopeningArchitectureExact` separates:

- secret reversible encryption/decryption;
- KEM-style encapsulation/decapsulation interfaces;
- model-relative reopening cost;
- information-theoretic, secret-coordinate, algebraic-trapdoor, and noisy-module modes;
- candidate verification from secret-section construction.

This is the exact shared architecture behind the thread's comparison of RSA, symmetric cryptography, ML-KEM, QKD, and NP search. The module intentionally does not implement those algorithms or assert their security assumptions.

Reference: Peter W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*, SIAM J. Comput. 26(5), DOI `10.1137/S0097539795293172`.

NIST FIPS 203 (*Module-Lattice-Based Key-Encapsulation Mechanism Standard*, 2024) is named as a standards reference; no DOI is asserted.

## 9. Claim boundaries

This tranche proves finite/type-theoretic architecture only. It does not claim:

- a diagnosis or clinical theory of trauma;
- an empirical theorem about institutions or politics;
- a Calabi–Yau or mirror-symmetry theorem;
- P-vs-NP progress beyond an exact reusable accounting object;
- RSA/ML-KEM security;
- a quantum-computing complexity separation;
- Shannon effective-option counts over a real probability simplex.

The high-alpha result is the unification itself: **terminalisation, symmetry quotienting, witness recovery, memory/action separation, and cryptographic reopening are now instances of typed projection + retained receipt + dynamics, with claim boundaries kept explicit.**
