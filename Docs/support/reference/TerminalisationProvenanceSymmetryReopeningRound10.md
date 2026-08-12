# Terminalisation, Provenance, Symmetry, and Reopening — Round 10

This tranche stacks on the canonical reopenable-evidence / PNF branch and adds the missing exact core identified by the terminalisation, Calabi–Yau symmetry, P-vs-NP, cryptographic-reopening, depth-wheel, and FRACTRAN provenance discussions.

## 1. Terminalisation is stronger than idempotence

`DASHI.Core.SelfSealingTerminalisationExact` separates idempotence, a constructive distinction-loss witness, and closure of a declared terminal region under counterevidence. A separate `CorrectiveReopeningWitness` proves the opposite property: some correcting evidence exits the terminal region. `selfSealingContradictsCorrectiveReopening` proves these cannot coexist.

The stronger `TerminalisationMasterArchitectureExact` packages the four-part architecture: causal-projection defect, proposition-local/non-promoting classification, protected provenance, and corrective reopening.

## 2. Memory is not command

`DASHI.Cognition.PNF.MemoryCommandSeparationExact` instantiates the repository's existing `MemoryFibre`. The literal extinction update preserves remembered `EventPNF` and provenance while setting action weight to zero. Thus `memory preserved + command changed` is an exact repository theorem, not merely prose.

Finite future-cone diversity is represented by live-option cardinality. The Shannon effective count `exp(H)` remains intentionally outside this finite Nat layer.

## 3. Classification edge is not identity

`PropositionIndependenceExact` keeps proposition assessments local and process/diagnosis-style state on a separate typed axis. There is no constructor allowing one local proposition assessment to settle all propositions.

`RecallProjectionNoncommutationWitness` records a concrete failure of prior-conditioned reconstruction: original fine state, prior, reconstructed state, and proof that reconstruction differs.

`ProtectedProvenanceRecovery` requires only application-selected critical provenance to survive reopening, rather than demanding a global inverse history map.

## 4. Honest finite symmetry stratification

`DASHI.Core.FiniteC3OrbitStabilizerExact` introduces an explicit C3 group action and proves the group/action laws by finite exhaustion. It contains a regular stratum with orbit/stabilizer cardinalities `3/1` and a fixed stratum with `1/3`, proving both finite orbit–stabilizer identities.

`DASHI.Core.C3OrbitProvenanceQuotientExact` then turns the regular orbit into a genuine provenance-bearing quotient: all three points project to one orbit label while a retained point receipt reopens the exact fine state.

Reference: John D. Dixon and Brian Mortimer, *Permutation Groups*, GTM 163, Springer (1996), DOI `10.1007/978-1-4612-0731-3`.

## 5. Graded provenance dynamics: observable equality is not dynamical equivalence

`DASHI.Core.GradedProvenanceDynamicalSystemExact` packs the existing heterogeneous C3 depth-wheel carrier into a single typed transition state. Elementary evolution shifts grade while a three-step macro update returns to the same grade.

A `DynamicallySufficientObservation` requires an actual coarse transition `coarseStep` satisfying

`observe(step x) = coarseStep(observe x)`.

From this the module proves that equal current observations imply equal next observations. `DynamicInsufficiencyWitness` is the exact counter-witness, and `dynamicInsufficiencyContradictsSufficiency` closes the contradiction.

`DASHI.Core.HiddenPhaseDynamicInsufficiencyExact` supplies a concrete example. Two states expose the same Boolean content but occupy different depth phases; the phase-specific next updates produce different visible states. Therefore no phase-erasing coarse step can be dynamically sufficient for that system.

This machine-oriented example formalises the supplied criterion:

> if forgetting a coordinate changes admissible future evolution, that coordinate is provenance-relevant.

## 6. Coupled phase frustration and macro branching

`DASHI.Cognition.PNF.CoupledDepthPhaseFrustrationExact` defines an exact finite C3 disagreement cost and a weighted three-fibre frustration. Every synchronized phase configuration has cost zero and attains the global Nat lower bound. A persistent nonzero local minimum therefore requires a restricted reachability/update graph; the bare energy function alone does not manufacture an attractor.

`DASHI.Foundations.DepthWheelMacroBranchingExact` keeps two different uses of the numbers separate:

- local carrier: `2*3=6`, `3*3=9`;
- one complete wheel branching: `2^3=8`, `3^3=27`.

The distinction is now typed by separate functions rather than merely documented.

## 7. P-vs-NP-adjacent object: efficient recoverable quotient

`DASHI.Core.EfficientRecoverableQuotientExact` separates decision projection, witness recovery, receipt construction, reopening, receipt length, and model-relative reopening cost. `PolynomialBound` proves bounds of the form

`cost(n) <= c * (n+1)^k`.

`C3EfficientReopeningExampleExact` supplies a complete finite witness: a one-point coarse quotient plus C3 receipt reopens the exact verifying witness, and quotient/receipt/reopening/receipt-length costs all have constant polynomial certificates.

This formalises the research question: when does an aggressive quotient retain a polynomial-size receipt with polynomial-time witness reopening? It does not prove `P = NP`, `P != NP`, NP-hardness, or a SAT lower bound.

Reference: Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, CUP (2009), DOI `10.1017/CBO9780511804090`.

## 8. ML-KEM: noisy public fibre plus privileged reopening

`DASHI.Crypto.ReopeningArchitectureExact` keeps information-theoretic hiding, secret-coordinate transforms, algebraic trapdoors, and noisy-module geometry as distinct reopening modes.

`DASHI.Crypto.MLKEMNoisyReopeningExact` now gives the ML-KEM discussion a concrete finite core. `NoisyStructuredObservation` factors public state into a structured signal plus residual. `PublicFibreCollision` is an exact witness that two distinct hidden signal/residual decompositions can expose the same public state. The toy arithmetic instance `y = 2*s + e` proves this with `(s,e)=(0,2)` and `(1,0)`.

The same toy is wrapped as an exact `ProvenanceBearingQuotient`: the public value is coarse while the private receipt reopens the fine `(secret,error)` state exactly. This is intentionally a structural witness, not an ML-KEM security proof.

`CorrectKEM` separately states the KEM correctness shape: encapsulation under the derived public key and authorised decapsulation under the secret key recover the same shared secret.

Primary standard: National Institute of Standards and Technology; Gorjan Alagic, Quynh Dang, Dustin Moody, Angela Robinson, Hamilton Silberg, Daniel Smith-Tone, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

Foundational LWE reference: Oded Regev, *On lattices, learning with errors, random linear codes, and cryptography*, STOC 2005, DOI `10.1145/1060590.1060603`.

Shor reference retained for the computational-model comparison: Peter W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*, SIAM J. Comput. 26(5), DOI `10.1137/S0097539795293172`.

## 9. 1729 -> 196883 as provenance-bearing prime-support transport

`DASHI.Arithmetic.PrimeSupportTransportTaxiMoonshineExact` formalises the exact arithmetic trace without promoting it into representation theory:

- `7*13*19 = 1729`;
- `1^3+12^3 = 1729`;
- `9^3+10^3 = 1729`;
- `1729 --47/7--> 11609`;
- `11609 --59/13--> 52687`;
- `52687 --71/19--> 196883`;
- `47*59*71 = 196883`.

Each replacement step carries an explicit multiplicative applicability witness `before = denominator*rest` and `after = numerator*rest`; no integer division primitive is hidden in the theorem.

The same file proves the exact combinatorial identity `C(12,3)=220` using a recursive binomial function. It deliberately does not guess the concrete twelve-element denominator set from the external Lean theorem; that enumeration can be imported separately and checked against this cardinality theorem.

A typed authority boundary proves that arithmetic landing at 196883 cannot by itself construct a moonshine promotion.

References: J. H. Conway and S. P. Norton, *Monstrous Moonshine*, BLMS 11 (1979), DOI `10.1112/blms/11.3.308`; Robert L. Griess Jr. and Stephen D. Smith, *Minimal dimensions for modular representations of the monster*, Communications in Algebra 22 (1994), DOI `10.1080/00927879408825189`.

## 10. Claim boundaries

This tranche proves finite/type-theoretic architecture and concrete finite arithmetic only. It does not claim a clinical theory of trauma; an empirical theorem about institutions or politics; a Calabi–Yau/mirror-symmetry theorem; P-vs-NP progress beyond a reusable accounting object; RSA/ML-KEM security; a quantum complexity separation; a Shannon-entropy theorem; or a Ramanujan-to-Monster representation-theoretic bridge merely from the integer endpoint.

The unifying invariant is now sharper:

**observable equality does not imply dynamical equivalence, and safe compression requires a consumer-valid reopening/congruence theorem rather than merely a small quotient.**
