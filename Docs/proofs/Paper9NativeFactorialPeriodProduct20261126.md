# Paper 9 P0 — actual native factorial-period product and analytic max cut

2026-11-26. Entry PR #1546 93ab13a90bdbc22c46c9fa0a98fc4661ace418c6. Paper 9 only; no GRH/P vs NP/TOE lane edits or merge. All Agda/Lean declarations remain SOURCE-WRITTEN, UNCOMPILED, not kernel receipts.

## Audit of original owners and reuse

Inspected full recursive tree manifests at Agda master 8d5b3697050bf62f8823458177e79c28b858a718, #1529 d8956bb9ba274e40734bb5ff136c014dd9b38dda and #1546 entry head (not truncated). Queried PRs for CM163, Chudnovsky, Bishop, Eisenstein and period, inspected changed filenames on #1552, #1478, #1533, #1551, #1250. This is a targeted audit, not a claim of every historical branch being exhaustively searched.

- Native signed defect: BishopChudnovskyWidthSourceExact.scaledDefectBound and actual raw P/Q/T edge and positive pair gap already exist. Factorial normalization and nested windows already on #1546. Do not build another evaluator or series carrier.
- Canonical sqrt: BishopNatSquareRootRegularFloorExact, BishopNatSquareRootRationalCrossPrecisionExact, BishopNatSquareRootCanonicalApproximationExact, BishopNatSquareRootSemanticSquareExact, BishopNatSquareRootPositiveExact. Found a concrete source-type mismatch at master and entry branch: vendor Real.seq is total Nat -> Q, whereas the old assigned floorApproximationFraction requires a positive precision instance. Reuse the existing total FloorApprox.floorSquareRootApproximation (zero coordinate 0); expose canonicalFloorSequencePositive and transport the existing positive-index regularity, square/upper-square, nonnegative and monotonicity proofs. Commits 0e99c67e, 51b774ff. No claim this was kernel checked or all transitive consumers elaborated.
- Vendor/bishop pinned 240e38c7f6938f20f865b1f956c5f084da48bd54: RealProperties.lemma-2-14, Sequence.xₙyₙ→x₀y₀, Sequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀, Sequence.uniqueness-of-limits, Inverse.*-inverseʳ. Use actual regularity and explicit positive-series apartness. Correct old RP.≃-sym to pinned RP.≃-symm in overlap consumer (1164c550).
- Native Machin: master owns original Machin real, rational stage error and configured trig/two-pi period constructions. These are NOT the CM hypergeometric period.
- #1552 at 6d2260fbd45f6e335b726597e305fb163c4f557c: JInvariantBishopLatticeEvenPowerShellMajorantExact and JInvariantBishopPuncturedShellFiniteFoldExact pay original weight 4/6 summand bounds and finite guarded shell folds. They do not supply the infinite normalized q/lattice identity or the CM163 period. Retain donor provenance; no changes to #1552.
- Lean actual analytic endpoint inspected at 204c52d239af8641c1183f0e623036b625235879: Paper9HypergeometricSeriesODE.actualHyperIdentityGerm/On/Ball; Paper9SignedCMPeriod.actualCMWeightedPeriod and actualLiteralPrefixPeriod; Paper9ScalarCross.literalPeriodFromDisk; Paper9DiskGerm.literalPrefixFromFiniteChecks; Paper9LiteralCross.rawCrossFromFiniteChecks. Already source-written on actual Lean factorial and Mathlib real pi; not Agda proof transport. Reuse, not re-derive gratuitously.

## Native weighted factorial limit (9561c014, 532fe225)

Define S_n=T_n/Q_n with original zero prefix, and H_n=abs(delta_n). Existing source supplies delta_n=P_(n+1)*(13591409+545140134n), and M^n H_n <= A Q_(n+1), where A=13591409 and M=2^41. Native edgeAdd/edgeDifference/edgeMagnitude identify the actual signed difference and only then take magnitude:
  |S_(n+1)-S_n| = H_n/Q_(n+1) <= A/M^n.
For n>=1, A*n <= M^n since M>=A, M>=2, 2^(n-1)>=n. Thus |S_(n+1)-S_n|<=1/n. Every later prefix lies in the earlier adjacent interval, so |S_m-S_n|<=1/min(m,n)<=1/m+1/n. This directly constructs seriesReal via the original BishopRegularRationalApproximation/Real.mkℝ, with seq S_n including S_0=0, no Machin/CM premise. seriesPositive uses S_1=A>1, the original Positive witness at index 1. seriesConverges and factorialConverges use original vendor lemma-2-14 and source factorial normalization. sampleConverges handles any sampling f(n)>=n, not necessarily strictly increasing. Source owner BishopChudnovskyNativeFactorialLimitExact.

## Synchronized original period product (5480db8b, d191ca61)

Choose k=41*n (cofinal chart only; unchanged original schedule). Then cutoff(k)=n+1. Let h_n be the selected larger of S_(n+1), S_(n+2), exactly highV n, and r_k/s_k the actual lower floor fraction at dyadic scale. The exact literal reciprocal lower corner satisfies
  L_k * h_n = 426880 * r_k/s_k.
This clears only positive Nat denominators, not the signed original product. highIndex chooses the actual source prefix including the tie branch. h_n converges to seriesReal by sampleConverges and literal view equality; r_k/s_k converges to canonical sqrt(10005) via the same vendor approximation lemma at actual precision s_k>=n. L_k converges to chudnovskyReal by its original native interval membership and width 2^-k, without using Machin.
Pointwise exact product and vendor multiplication/uniqueness of limits source-write
  actualProduct : chudnovskyReal * seriesReal ≃ 426880 * sqrtReal.
No additional analytical identity is used in this product; its proof depends on still-uncompiled earlier arithmetic owners.

The classical period obligation is now exactly
  NativePeriod = bishopMachinPi * seriesReal ≃ 426880 * sqrtReal.
seriesReal positive gives explicit apartness, and the vendor inverse law cancels this one licensed factor. BIDI:
  NativePeriod <-> chudnovskyReal ≃ bishopMachinPi <-> forall k ExpandedCross(k).
sameRealToPeriod, periodToSameReal, expandedToPeriod and periodToExpanded source-write both directions. Do not conflate unconditional actualProduct with NativePeriod: it identifies the Chudnovsky candidate, not Machin pi. The remaining assertion is the classical modular period identity or its verified cross-prover transport, not a new open mathematical conjecture.

## Exact remaining native analytic obligations and available Lean source

The Lean chain is a constructive guide, not a kernel certificate:
1. Same actual native normalized E4/E6/E2 q-series, punctured lattice and modular relation at tau0. Existing lattice kernels/shell folds, Machin trig and CM finite packets are donors. Native q/lattice identification and normalized differential laws must be paid or transported. 
2. Native hypergeometric/Euler jet -> positive root branch: actual H(z)=sqrt(E4) on the selected disk using Ramanujan flow, the third-order hypergeometric ODE, cusp germ uniqueness and analytic continuation. The Lean owners are source-written; native all-index recurrence alone does not prove equality to modular E4.
3. Native CM value j(tau0)=-640320^3 and signed reciprocal disk correction kappa from the actual Hecke-41 product and its first retained residual derivative. Reuse finite diagonal/slice/shift/jet certificates and source-specific cusp bounds. Native analytic reflection (not only exact arithmetic certificate) needed. No higher jet needed.
4. Native positive signed CM period normalization on exactly seriesReal, canonical sqrtReal and bishopMachinPi. The Lean owner Paper9SignedCMPeriod.actualCMWeightedPeriod shows the original identity from the actual modular root and signed scalar correction. The final reduction in this tranche eliminates the separate factorial-limit, square-root comparison and reciprocal-interval semantic attachments on the native route, once elaborated.
Alternative: verified translation/checking of the actual Lean proof of all-index RawCross into native ExpandedCross. Matching source recurrences, hashes or finite tests do not supply that universal proof. No trusted foreign axiom/postulate added.

## Execution receipt

scripts/check_paper9_native_period_product.py at d191927c8e356166e50e1ec4efd4c272bc9017cf, Git blob 3040c81eba4e1390fa1b37d67710a40cb2b16c50. Local initial formatting difference in main guard was resolved to match remote source exactly; reran byte-matched script using Python int/Fraction/SymPy 1.14, timeout 90 s. 2 polynomial corner normal forms; 259 signed original edge identities/bounds; 258 positive inverse budgets; 16384 positive native factorial regularity pairs; 257 synchronized cutoff/root/paired corner product and shifted-product negative controls PASS; k=0..10496 in increments of 41. No numerical pi reference. No full CM163 GMP replay or performance acceptance this tranche; previous reference receipts retained. Local PATH lacks Agda, Lean and Lake, so no elaboration/axiom audit or promotion. All proof terms (including older dependencies) may need API/tactic repair. Root owner fixes confined to Paper9 PR; no broad shared-master edits.
