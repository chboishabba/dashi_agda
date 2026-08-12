# Blue-Team Adversary Closure — Round 16

This tranche closes the defensive candidate-test → observation → fibre → search → protected-label → finite-game chain. It is cryptanalytic infrastructure, not a claim that ML-KEM or another standardized primitive is broken.

## Canonical observation and trace invariance

`BlueTeamAdversaryObservationExact` and `BlueTeamThreatModelExact` separate hidden state, public projection, query, observation, protected output and candidate mask. Public-factored observations cannot split a prior public fibre. `PublicFactoredObservationTraceInvariantExact` strengthens that result to arbitrary finite query traces and a two-round adaptive public policy: if every next query and answer is derived only from already-public information, same-public hidden states still generate identical complete transcripts.

`ComputationalCandidateFibreExact` separately distinguishes exact preimages, verifier-induced plausible candidates, inversion algorithms and model-relative inversion cost. Injectivity gives uniqueness, not an efficient inverse.

## Candidate cardinality, protected labels and finite games

`FiniteCandidateFibreCardinalityExact` proves finite survival-mask refinement cannot increase live candidate count and supplies a strict `2 -> 1` witness. `TranscriptProtectedLabelExact` makes protected-output recovery weaker than full-state inversion: a transcript factorisation is already a break witness when it determines the protected label, while two different labels in one transcript fibre refute deterministic exact recovery.

`FiniteSecurityGameBoundaryExact` turns exact label recovery into perfect binary distinguishing. `FiniteAdvantageAccountingExact` adds exact finite-count advantage bookkeeping: for the canonical balanced two-trial experiment, random-guess baseline is `1/2`, perfect success is `2/2`, and the exact gain numerator is `1`. These records are not promoted into an IND-CCA proof.

## Prior, score and search factorisation

`PriorScoreSearchFactorisationExact` makes the three layers differently typed. Prior factorisation means local prior predicates plus coupling. Score factorisation means local scores plus a coupling score. Search factorisation means actual local enumeration, compatibility and assembly. A crossed Bool-pair regression passes both local predicates but cannot reconcile, so local prior/score decomposition does not construct global search.

`InvertibleTransformPriorCouplingRegressionExact` gives a stronger finite theorem for the NTT intuition. Two independently selectable source bits are carried through a genuine four-state bijection with exact `encode/decode` inverses, using the Z/5-shaped mixing pattern `(x,y) -> (x+y,x-y)`. In target coordinates all three `u` values and all three `v` values occur marginally, but the marginally admissible pair `(u0,v1)` is not in the joint image. Thus an invertible mixing transform can preserve every global state while creating a non-Cartesian transported prior in its local coordinates.

## Search accounting and algorithm-relative value

`IndexedSearchCostExact` separates generic Cartesian reconciliation

`sum(T_i) + product(n_i) * T_C`

from a supplied direct/functional route

`sum(T_i) + T_C`.

The concrete `3 × 5` survivor regression costs `48` versus `20`.

`AlgorithmRelativeRecoveryCostExact` then shows why candidate count alone is not the right information measure. One exact `2 -> 1` shrink saves `7` work units when reconciliation is unchanged, while another `2 -> 1` shrink raises total recovery cost from `2` to `11` because reconciliation becomes more expensive. A theorem-bearing information gain is therefore a proved drop in complete recovery cost, not merely a leaked bit or `log |F|`.

## Finite MLWE laboratory

`FiniteMLWEVectorLabExact` implements a 2×2 noisy linear system over Z/5Z with `A=[[1,2],[2,1]]` and `t=As+e`. For public `t=(2,2)`, two distinct hidden states survive. Residual testing leaves exactly two of four secret candidates, and a hidden-dependent first-secret-bit observation leaves one.

`FiniteMLWEPriorScoreSearchRegressionExact` proves the residual score decomposes exactly by rows, yet the two distinct surviving secrets both have zero score. Score factorisation therefore does not imply unique search. Under the lab's declared recovery architecture, the hidden-dependent observation changes exact total recovery cost from `13` to `8`, a cost drop of `5`.

## FIPS 203 source-faithful search geometry

Primary source:

National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203, published 13 August 2024, DOI `10.6028/NIST.FIPS.203`.

`MLKEMFIPS203SourceExact` records `n=256`, `q=3329`, the three approved parameter tuples/RBG strengths, key/ciphertext byte sizes, Table-1 decapsulation-failure exponents, Algorithms 13–18 identities and Algorithm-18 implicit-rejection selection. The boundary also retains NIST's requirements that K-PKE is not approved stand-alone, internal derandomized interfaces are not application-facing, the implicit-rejection flag is secret and may not be returned, every decapsulation ciphertext is checked, and conformance alone is not a security proof.

`MLKEMFIPS203SearchGeometryExact` extracts the finite search carrier without converting it into a security estimate: secret coefficient counts `512/768/1024`, CBD coefficient support widths `7/5/5`, public matrix polynomial counts `4/9/16`, and ciphertext bit counts `6144/8704/12544`.

`MLKEMNTTLocalPriorCouplingExact` records the decisive NTT boundary. FIPS factors `X^256+1` into 128 quadratic factors and multiplication in `T_q` is local across those 128 coordinates, but K-PKE samples the small-coefficient secret/error prior in `R_q` before applying NTT. Therefore local NTT multiplication does not establish independent secret-search lanes. The finite invertible-mixing theorem above is an exact regression showing how this failure can occur.

## Unified defensive frontier

The two blue-team programmes now meet at

`T_recover(t) = T_local(F_t) + T_reconcile(F_t)`.

A mathematical-search advance must prove exploitable prior or score decomposition **and** cheap reconciliation. An observation-side advance must supply a genuinely hidden-dependent split and then prove that the resulting refinement materially lowers protected-label recovery cost. Public-only repeated observations cannot do this; an invertible transform alone cannot do it; and candidate shrinkage alone does not prove it.

Conversely, those same theorems give defensive no-go certificates for attack families: public-factored trace invariance, protected-label nonconstancy within observation fibres, exact-vs-plausible fibre separation, transform-induced coupling, or reconciliation costs that erase the apparent local gain.

## Validation boundary

`scripts/check_crypto_blue_team_adversary_closure_round16.sh` cascades the Round-15 crypto checker, rejects holes/postulates/trust escapes, checks all load-bearing theorem markers, and invokes the cumulative Round-16 aggregate if a local Agda binary exists. No GitHub Actions workflow is added or invoked. No Agda kernel-clean claim is made without an observed typecheck.
