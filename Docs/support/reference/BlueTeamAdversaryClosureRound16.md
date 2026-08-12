# Blue-Team Adversary Closure — Round 16

This tranche closes the defensive candidate-test → observation → fibre → search → protected-label → finite-game chain. It is cryptanalytic infrastructure, not a claim that ML-KEM or another standardized primitive is broken.

## 1. Canonical threat/observation model

`DASHI.Crypto.BlueTeamAdversaryObservationExact` defines a hidden state, public projection, adversarial query, and observation. `PublicFactored` proves that if an observation factors entirely through already-public state, then two hidden states in the same public fibre receive the same observation for every query. `HiddenDependentSplit` is the opposite constructive witness. `publicFactoredCannotSplitSamePublicFibre` proves the two cannot coexist.

`BlueTeamThreatModelExact` composes public state, hidden state, query, observation, protected output, per-query cost, and a finite candidate mask in one object. Its adapters reuse the observation and protected-label cores. It proves that public protected-label splits refute exact public recovery, public-factored observations cannot be hidden-dependent split witnesses, and candidate refinement cannot increase finite candidate count.

`PublicFactoredObservationTraceInvariantExact` strengthens the one-query theorem to arbitrary finite query traces and to a two-round adaptive policy whose next query is chosen only from public state and prior public observations. Same-public hidden states still produce the same complete transcript. Repeated public derivations therefore add no hidden-state resolution.

`ComputationalCandidateFibreExact` keeps exact preimage fibres, verifier-induced plausible-candidate fibres, actual inversion algorithms, and model-relative inversion cost separate. Injectivity proves exact-fibre uniqueness, not efficient inversion; residual plausibility proves candidate admission, not exact key recovery.

## 2. Exact finite fibre cardinality

`FiniteCandidateFibreCardinalityExact` represents one finite hidden enumeration by a Boolean survival mask. `Refines before after` permits only keep/delete transitions and proves `liveCount after <= liveCount before`. The explicit two-to-one witness gives strict finite shrinkage without importing Shannon entropy.

## 3. Protected-label recovery and finite advantage

`TranscriptProtectedLabelExact` separates full-state inversion from protected-output recovery. A transcript factorisation through any intermediate quotient is already enough to recover the protected label. Conversely, if one transcript fibre contains two states with different protected labels, exact deterministic recovery and exact public factorisation are impossible.

`FiniteSecurityGameBoundaryExact` turns exact protected-label recovery into a perfect binary distinguisher. `FiniteAdvantageAccountingExact` generalizes the count bookkeeping: a finite experiment records trials, successes and a baseline, and a `PositiveAdvantage` records the exact success excess. The canonical balanced two-trial experiment has baseline `1/2`, perfect success `2/2`, and exact gain numerator `1`. No finite-count record is promoted into computational security by itself.

## 4. Prior factorisation, score factorisation and search factorisation are different

`PriorScoreSearchFactorisationExact` makes three layers separately typed:

- prior factorisation: local prior predicates plus a coupling/reconciliation relation;
- score factorisation: local scores plus a coupling score;
- search factorisation: actual local enumerators, compatibility and assembly.

A concrete Bool-pair regression has individually admissible local coordinates and an exact local-score decomposition, yet a crossed pair cannot reconcile. Therefore neither prior nor score decomposition alone constructs cheap global search.

`InvertibleTransformPriorCouplingRegressionExact` sharpens the NTT warning with a genuine finite bijection. Two independent source bits are mixed according to the Z/5-shaped pattern `(x,y) -> (x+y,x-y)`. The global four-state transform has exact encode/decode inverses, but its target-coordinate marginal supports admit a crossed pair `(u0,v1)` that is not in the joint image. Thus an invertible mixing transform can create target-coordinate coupling even when the source coordinates were independently selectable.

## 5. Search accounting and algorithm-relative information

`IndexedSearchCostExact` separates generic Cartesian reconciliation

`sum(local costs) + product(survivor counts) * reconcile-per-tuple`

from supplied functional/direct reconciliation

`sum(local costs) + reconciliation cost`.

The explicit `3 × 5` regression is `48` work units versus `20`.

`AlgorithmRelativeRecoveryCostExact` then proves by exact examples that candidate shrinkage and computational improvement are distinct statements. In one architecture a `2 -> 1` shrink saves exactly `7` work units. In another, the same `2 -> 1` shrink coincides with reconciliation growth and total cost rises from `2` to `11`. The blue-team information quantity is therefore an actual proved search-cost drop, not merely a leaked-bit count or `log |F|`.

## 6. Concrete finite MLWE regression laboratory

`FiniteMLWEVectorLabExact` uses a real two-equation modular system over Z/5Z:

`A = [[1,2],[2,1]]`, `t = A s + e`,

with two-bit secrets and coordinate errors restricted by the lab smallness predicate. For public `t=(2,2)`, both `((0,1),(0,1))` and `((1,0),(1,0))` are valid hidden states. Candidate residual testing leaves exactly two of four candidate secrets and a hidden-dependent first-secret-bit observation leaves one.

`FiniteMLWEPriorScoreSearchRegressionExact` exposes the dual-programme synthesis on that same object. The residual score decomposes exactly by rows, yet two distinct secrets both have score zero, so score factorisation does not identify a unique secret. Under a declared recovery architecture, the real hidden-dependent observation changes total search cost from `13` to `8`, an exact cost drop of `5`.

## 7. FIPS 203 source-faithful surface

`MLKEMFIPS203SourceExact` is grounded directly in:

National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203, published 13 August 2024, DOI `10.6028/NIST.FIPS.203`.

It records `n=256`, `q=3329`, approved parameter tuples, RBG strengths, key/ciphertext sizes, Table-1 decapsulation-failure exponents, Algorithms 13–18 identities, and the Algorithm-18 candidate/fallback implicit-rejection selection law. The source boundary records that K-PKE is not approved stand-alone, internal derandomized interfaces are not application-facing, the implicit-rejection flag may not be returned, every decapsulation ciphertext is checked, the encapsulation key may be public, the decapsulation key remains private, and conformance alone is not a security proof.

`MLKEMFIPS203SearchGeometryExact` extracts finite carrier dimensions without turning them into fake security estimates: secret/error coefficient counts `512/768/1024`, coefficient support widths `7/5/5`, matrix polynomial counts `4/9/16`, and ciphertext bit counts `6144/8704/12544`.

## 8. NTT local algebra versus transported prior

FIPS 203 factors `X^256+1` into 128 quadratic factors, and multiplication in `T_q` is local across those 128 degree-one residue coordinates. `MLKEMNTTLocalPriorCouplingExact` records the missing cryptanalytic theorem: K-PKE samples the small-coefficient secret/noise prior in `R_q` before NTT, so locality of NTT multiplication does not prove that the transported prior factors into independent search lanes.

The finite invertible-mixing regression above demonstrates why this distinction can be real rather than terminological: exact representation changes can preserve all information while turning a simple source carrier into target coordinates whose marginal supports require nontrivial reconciliation.

## 9. Defensive frontier after this tranche

The two programmes now meet at one quantity:

`T_recover(t) = T_local(F_t) + T_reconcile(F_t)`.

A fundamental-search advance must prove exploitable prior/score decomposition **and** cheap reconciliation. An observation-side advance must provide a genuinely hidden-dependent split and then show that the resulting fibre change materially reduces protected-label recovery cost. A leaked predicate that does not reduce the relevant recovery cost is not automatically a useful attack.

Conversely, blue-team evidence can close attack families by proving public-factored trace invariance, nonconstant protected labels on observation fibres, exact-vs-plausible fibre separation, transform-induced reconciliation bottlenecks, or algorithm-relative cost non-improvement.

## Validation boundary

`scripts/check_crypto_blue_team_adversary_closure_round16.sh` cascades the existing Round-15 crypto checker, rejects holes/postulates/trust escapes, checks the theorem markers above, and typechecks the cumulative aggregate if a local Agda binary exists. No GitHub Actions workflow is added or invoked. No Agda kernel-clean claim is made without an observed typecheck.
