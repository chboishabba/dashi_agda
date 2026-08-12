# Blue-Team Adversary Closure — Round 16

This tranche closes the defensive candidate-test → observation → fibre → search → protected-label → finite-game chain. It is cryptanalytic infrastructure, not a claim that ML-KEM or another standardized primitive is broken.

## 1. Canonical observation model

`DASHI.Crypto.BlueTeamAdversaryObservationExact` defines a hidden state, public projection, adversarial query, and observation. `PublicFactored` proves that if an observation factors entirely through already-public state, then two hidden states in the same public fibre receive the same observation for every query. `HiddenDependentSplit` is the opposite constructive witness. `publicFactoredCannotSplitSamePublicFibre` proves the two cannot coexist.

This unifies passive ciphertexts, accept/reject state, timing, protocol outcomes, and physical observations under one rule: a new observation matters only if it separates states that the prior public surface identified.

## 2. Exact finite fibre cardinality

`FiniteCandidateFibreCardinalityExact` represents one finite hidden enumeration by a Boolean survival mask. `Refines before after` permits only keep/delete transitions and machine-proves

`liveCount after <= liveCount before`.

The explicit two-to-one witness gives strict finite shrinkage without importing Shannon entropy.

## 3. Protected-label recovery is the real break criterion

`TranscriptProtectedLabelExact` separates full-state inversion from protected-output recovery. A transcript factorisation through any intermediate quotient is already enough to recover the protected label. Conversely, if one transcript fibre contains two states with different protected labels, exact deterministic recovery and exact public factorisation are impossible.

`FiniteSecurityGameBoundaryExact` turns exact protected-label recovery into a perfect binary distinguisher. The finite success numerator is 2/2, while the represented random-guess baseline is 1/2. Absence of such a witness has no constructor into a security proof.

## 4. Search accounting

`IndexedSearchCostExact` extends the existing local/reconciliation machinery to indexed cost accounting.

Generic survivor reconciliation costs

`sum(local costs) + product(survivor counts) * reconcile-per-tuple`,

while a supplied functional/direct reconciliation path costs

`sum(local costs) + reconciliation cost`.

The explicit regression uses two local enumerators with survivor counts 3 and 5: the Cartesian accounting is 48 work units versus 20 for a functional reconciliation route. These are exact accounting formulas, not claims about a concrete cryptosystem until its search procedures instantiate them.

## 5. Concrete finite MLWE regression laboratory

`FiniteMLWEVectorLabExact` uses a real two-equation modular system over Z/5Z:

`A = [[1,2],[2,1]]`, `t = A s + e`,

with two-bit secrets and coordinate errors restricted by the lab smallness predicate.

For public `t=(2,2)`, both

`(s,e)=((0,1),(0,1))`

and

`(s,e)=((1,0),(1,0))`

produce the same public value. Candidate residual testing leaves exactly two of the four candidate secrets; both have residual score zero. A hidden-dependent first-secret-bit observation eliminates one of the two and leaves exactly one candidate. Both residual rows depend on the same secret coordinates, so the lab also records a genuine coupling edge rather than pretending row tests are independent.

`FiniteMLWEGameRegressionExact` composes this lab with the finite game: public `(2,2)` cannot exactly recover or perfectly distinguish the protected first-secret-bit label, while the explicit hidden-dependent observation shrinks the candidate fibre from two to one.

This lab is deliberately not ML-KEM. It is the smallest non-scalar executable regression for the blue-team reasoning surface.

## 6. FIPS 203 source-faithful surface

`MLKEMFIPS203SourceExact` is grounded directly in NIST FIPS 203:

National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203, published 13 August 2024, DOI `10.6028/NIST.FIPS.203`.

It records the exact global constants `n=256`, `q=3329`, approved parameter tuples, required RBG strengths, key/ciphertext byte sizes, Table-1 decapsulation-failure exponents, Algorithms 13–18 identities, and the Algorithm-18 candidate/fallback implicit-rejection selection law.

The boundary also records source requirements: K-PKE is not approved stand-alone; internal derandomized interfaces are not application-facing; the implicit-rejection flag may not be returned; every decapsulation ciphertext is checked; the encapsulation key may be public; the decapsulation key remains private; and FIPS conformance alone does not prove a secure implementation.

## 7. Defensive cryptanalysis frontier

The remaining research question is now sharply typed:

`cheap candidate verifier + observations + local decomposition`

is not yet

`cheap protected-label recovery`.

A concrete advance must therefore supply at least one of:

- a same-public-fibre hidden-dependent observation split;
- a public quotient that factors the protected output;
- a local residual decomposition with cheap candidate enumeration **and** cheap reconciliation;
- a model-relative search improvement that changes the actual work bound.

Conversely, blue-team evidence can refute whole attack families by proving observations public-factored, protected labels nonconstant on observation fibres, or reconciliation costs that restore the full search bottleneck.

## Validation boundary

`scripts/check_crypto_blue_team_adversary_closure_round16.sh` cascades the existing Round-15 crypto checker, rejects holes/postulates/trust escapes, checks the theorem markers above, and typechecks the cumulative aggregate if a local Agda binary exists. No GitHub Actions workflow is added or invoked. No Agda kernel-clean claim is made without an observed typecheck.
