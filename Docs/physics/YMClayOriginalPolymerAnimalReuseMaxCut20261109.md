# Original Wilson D1 — polymer-animal reuse audit and corrected max-cut
Date: 2026-11-09. Scope: PR #1444 and existing merged YM corpus. No external repository writes.

## Finding: do not reimplement polymer-animal enumeration

The repository already contains the following substantive sources, beyond receipts:

| Original owner | Reusable theorem / construction | Exact application boundary |
|---|---|---|
| `BalabanPolymerDiameterEntropy.agda` | P06 mixed skeleton–decoration animal-count reducer, with rooted skeleton DFS enumeration | The module declares `BalabanPolymerContext`, `BalabanPolymer`, and `currentBalabanGraphAdapter` as postulates; a physical instantiation must not treat these as concrete original Wilson SU(2) data |
| `BalabanP06CanonicalAnimalConstantExact.agda` | `canonicalAnimalCountBound`, canonical skeleton/decoration constants | Requires a supplied `P06ModelLeafDischargePackage`; no second animal-count theorem is necessary once original physical support satisfies its hypotheses |
| `BalabanP06PhysicalModelLeafLightweightExact.agda` | explicit local graph/support, reduced skeleton and decoration/fibre contracts | Contains model-dependent rooted support/connectivity/multiplicity obligations |
| `BalabanClayT2RepositoryConnectedPolymerExtractionExact.agda` | least-root tree, fixed DFS trace, decoder and root-word injectivity | Physical connected-block carrier and canonical decoder input still needed |
| `BalabanCMP116R429ConnectedDomainCountingRound440Exact.agda` | reuse of canonical rooted-trace counting for literal R429 CMP116 domain | `trace`, `literalDomainIsRootedShell`, `literalDomainPolymerFaithful`, `canonicalTraceDepthIsR429TreeDepth` must be supplied for original domain |
| `BalabanClayP2BadComponentGeometryExact.agda` | bad-block finite path/component connectivity and gauge transport | Literal original Wilson bad predicate and physical measure activity are distinct |
| `BalabanClayGate4OscillationAnimalInfluenceExact.agda` | finite shell activity <= animal/oscillation majorant summation | `shellBelowMajorant`, scale-uniform decay and strict weighted ratio need original source estimates |
| `BalabanP06A1A2A3InfluenceExact.agda` | canonical P06 animal constant + per-link oscillation source assembly | `PhysicalA1A2A3InfluenceInputs` has conditional `p06ModelLeaf`, `shellsAt`, and strict ratio |
| `BalabanStepVCanonicalAnimalMarginExact.agda` | logarithmic animal entropy–decay margin transport | Needs original physical kappa/log-exp profile |
| `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.agda` | finite mixed log differentiation, connecting clusters, triangle and rooted-shell transport | `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` is still a supplied field |

`YMLatticeAnimalCountingBoundReceipt.agda` is explicitly a non-promoting receipt: the quoted rooted-Z4 (8e)^n statement is NOT a kernel proof of the concrete Wilson polymer hypothesis.

## Single high-alpha producer path

1. Select the *same* original changing-cutoff Wilson R445 Gibbs/polymer measure, original bad-region event and physical-block supports.
2. Prove these original supports inhabit the existing P06 physical model leaf and R429 canonical trace identification; reuse `canonicalAnimalCountBound`, not a fresh animal lemma.
3. Prove an original Wilson large-field/frustrated-polymer *activity* bound, with a quantitative decay exponent exceeding the canonical animal entropy: `C_anim exp(-kappa) < 1`, uniformly in physical cutoff and volume.
4. Transport that estimate through existing A1/A2/A3 / Step-V / KP/FP and the literal two-Wilson marked expansion to **the exact** finite charge-sum inequality `chargeSumBelowPhysicalRootedShell` for the existing physical-shell package. This must retain source identity, 2 support insertions, actual scale/root/distance, and signed/covariance equality.
5. Consume the already implemented `twoWilsonMixedLogBelowPhysicalRootedShell`, R320 and R333 consumers. No duplicate KP or animal counting.
6. E1 continuum convergence, D2 same-E1 OS spectrum, N1 continuum noncollapse, G1 compact-simple scope remain independent physical terminal gates.

## Physical counterexample to invalid promotion

Rooted-animal count alone controls how many connected supports exist; it gives no upper bound on their Gibbs probability or their polymer activity. A one-link coherent conditional cap also fails to control a sparse connected support of frustrated staples. Combining either with a finite polymer enumeration without actual joint activity domination is logically insufficient.

## Narrow new proof contract (not an already proved lemma)

`originalWilsonSparseFrustratedActivityBelowCanonicalP06Rate`:
For each original physical cutoff, volume, pair of Wilson test supports, and genuinely connecting selected polymer/cluster, bound the absolute marked mixed charge by the original physical activity decaying with canonical trace depth at a uniform rate whose exponential decay wins the P06/Step-V animal constant; establish the root-and-distance indexed *sum* rather than only a pointwise estimate.

This is the missing physical quantitative input. Do NOT replace it with `postulate`, an empty admissibility relation, a generic shell majorant field, or a high-temperature independent-plaquette model.

## Acceptance

This audit reads original GitHub source on PR #1444, not merely PR descriptions. It claims neither Agda kernel acceptance nor an all-Clay result. Existing source already pays counting and finite mixed-derivative transport conditional on model identification. The genuine remaining work is original Wilson physical activity and its source identification, then E1/D2/N1/G1.


## Additional source-owner check: P06 physical constructor and P11

`BalabanP06PhysicalModelLeafExact.agda` already defines `p06ModelLeafFromPhysicalInputs` and `p06PhysicalModelLeafReceipt`. Its record `P06PhysicalModelLeafInputs` supplies the support/reduced-skeleton/decoration/decomposition, concrete neighbour graph and finite-range summation components. Several interfaces carry propositions as `Set` plus evidence fields. This is a *constructor requiring proofs*, not an automatic derivation of original Wilson geometry.

`BalabanP11PhysicalPrefixTailEntropyExact.agda` already consumes the same canonical P06 animal constant in `canonicalAnimalConstantForP11`, and `p11AbsorptionFromPhysicalPrefixTail` transports P11 analytic input to the imported large-field absorption condition. The module explicitly classifies its finite prefix bound, asymptotic tail estimate and entropy payment as conditional. Therefore **P11 entropy absorption also must not be reconstructed from scratch**.

`BalabanStepVGeometricInfluenceSummationExact.agda` already implements `uniformInfluenceBoundFromGeometricSummation` from the A1/A2/A3 input and a majorant partial-sum bound. There is no missing finite-sum comparison theorem in this route.

**Further narrowed maximum cut:** (1) select original Wilson literal physical support into P06/R429 and prove the actual instance of its geometric/model fields; (2) original full Gibbs sparse-frustrated activity/scale bound with a uniform entropy margin and two-mark charge; (3) same-source physical-shell sum calibration. Only then consume the already-existing KP/FP, P11, Step V, CMP116, R320, R333 compilers.

This narrows obligations; it does not prove the missing original-Wilson analytic inputs.
