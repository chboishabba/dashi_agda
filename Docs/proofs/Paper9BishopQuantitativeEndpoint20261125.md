# Paper 9 — quantitative original-real endpoint (25 November 2026)

Status: source-written mathematical derivation and native consumer; no compilation, kernel, numerical execution, CI or benchmark in this tranche. Original P0 remains fastest independently certified pi. This cut is not COMP6f and adds no production arithmetic variant.

## Original owners and proof boundary

At PR #1546 parent 3e71cea0a56f0954ea9c470c55bedbbe0142aa52 the existing ConstantsAndKleinJCM roadmap (blob 74f92bb74d05d00b73e07d3d8f2d46d96086becb) already supplies a classical conditional derivation: degree-41 diagonal root isolation at K=-640320^3; diagonal plus fixed slice cubic jet giving s2=77265280/90856689; Ramanujan differential algebra; factorial recurrence and period coefficient. Preserve those prior receipts, not a new CM proof or a claim to have rerun them. General CM integrality is unnecessary for this selected point. The classical modular correspondence, q-series semantics, compactness, eta/Delta identity, valence and analytic uniqueness remain named premises. Existing check_chudnovsky_exact.py (eb58d9dd1d0a2e0d62e9ef16a0ad1ee9703e0e6b) and check_chudnovsky_bishop_semantics.py (656361343d475c7b0e91a56f82e4fb69aa14ec81) own the original interval evaluators. The native original bishopMachinPi is in BishopMachinArctanConstructionExact (be11dee1db4eb6856346267134dcd85fed96fc2a). The native cross-prover receipt (856dfcf466fcaeb3edc7a106952cc367d848d9dd) records the authored Lean Machin theorem, but no observed kernel or serialized same-object witness. Do not change those flags.

## A. Explicit cusp branch, no numerical phase recognition

Write C=640320^3, tau=(-1+i sqrt163)/2. Classical Machin identity and elementary angle bounds identify the classical pi used in q=exp(2 pi i tau). Since pi>3 and sqrt163>12, |q_CM|=exp(-pi sqrt163)<2^-36 (exp(1)>2). This bound concerns the classical q, not a native Bishop phase receipt. For t in [0,2^-36], sigma_k(n)<=n^(k+1), n<=2^(n-1), so |E4(q)-1|<=240t/(1-16t), |E6(q)-1|<=504t/(1-64t), both <1/16 on the entire negative real q segment. Hence E4,E6>0; 0<E6^2/E4^3<(17/16)^2/(15/16)^3<2. Thus |z|<1 for z=1-E6^2/E4^3. With classical Delta nonvanishing, z is nonzero off the cusp and D z=z E6/E4 gives nonzero local derivative; at cusp z=1728q+O(q^2). The inverse exists locally at every point of the segment. Analytic continuation of the unique cusp power-series solution through these overlapping local charts stays on the positive sqrt(E4) branch and inside the hypergeometric convergence disk. No global inverse or arbitrary complex branch is inferred. This supplies explicit ordinary mathematical branch bounds for the earlier conditional derivation. Native modular/q/phase identity remains open.

## B. Fixed schedule, all-degree enclosure width

Use original C, A=13591409, B=545140134. Absolute successive weighted term ratio <=42*1728/C<2^-41, by the original factor bound and A+B<42A. Thus the alternating bracket [Slo,Shi] at n>=1 has Slo>A/2 and width <=A*2^(-41n). The dyadic root bracket [rlo,rhi] of sqrt10005 has width 2^-b and rhi<=101 for b>=0. The Chudnovsky interval [426880*rlo/Shi,426880*rhi/Slo] has width bounded by

426880*(2/A)*2^-b + 426880*101*(4/A)*2^(-41n)
< 2^-b + 16*2^(-41n).

For every integer k>=0 take b=k+2, n=max(1,ceil((k+5)/41)). Width is <(1/4+1/2)2^-k<2^-k. This is a conservative explicit proof of total precision scheduling, independent of adaptive retry success. It does not by itself prove strict decimal-floor admission at a boundary or optimal cutoff.

For the literal Machin k-term partial M_k, use alternating brackets at 5 and 239. Their combined width <= (16/5+4/239)*25^-k <4*25^-k, including k=0 (empty partial). Let c_k be the midpoint of the CH interval at the fixed schedule. On the previously named classical analytic inputs both intervals contain the same classical pi, so for k>=1

|c_k-M_k| < 2^-k + 4*25^-k <= 2/(k+1) < 4/(k+1).

Indeed 2^k>=k+1 and 25^k>=4(k+1) for k>=1. At k=0, M_0=0 and 0<c_0<22/7+1<5; the sharper CH width <3/4 gives c_0<22/7+3/4<4. Thus the error 4/(k+1) bounds the entire stream. This proof is conditional on the classical identities, not inferred from finite matching digits. It also establishes an ordinary rational-Cauchy same-real theorem: the midpoint stream and the literal Machin partial stream differ by a vanishing quantified bound. No new pi carrier is necessary.

## C. Native consumer, precise remaining producer

Existing BishopVanishingDifferenceConvergenceExact proves convergence transfer from a vanishing pointwise difference; BishopBaselReciprocalSquareConvergenceExact owns reciprocal convergence; BishopPolynomialSuccessorFactorLimitExact owns constant convergence; the vendored Sequence uniqueness theorem is reused. New BishopChudnovskyMachinLimitWeldExact constructs the actual original Machin partial stream and writes its limit proof using existing product/addition/negation laws. It consumes an embedded rational candidate stream and explicit all-index error evidence, then returns convergence to literal bishopMachinPi, and equality of any independently supplied limit by uniqueness. This is an untested source-written consumer, not a paid native all-index Chudnovsky producer. Required next: define the concrete rational split/root midpoint on the native carrier; prove leaf/merge and interval correspondence; derive the all-index bound from the actual native modular/phase source or a sound certified rational semantic reflection; instantiate the consumer with 4/(k+1). No arbitrary sequence proof is allowed as a substitute for that source binding. Cross-prover transport remains a separate missing witness.

scripts/check_pi_p0_quantitative_same_real.py specifies fixed-schedule exact regression fixtures, reusing existing evaluators; no execution here. It tests constants, widths, finite overlaps and partial-to-midpoint error. Finite tests cannot instantiate the universal Agda premise.

## D. Remaining acceptance order

1. Native same-source rational split/root and all-index Machin/CH bound, then exact kernel replay of the existing modular/phase correspondence or a sound reflection proof. No finite digits promote equality.
2. Exact-source native COMP6e and indexed quotient cube, original output hashes, actual GMP portability check. Source hashes and measured costs retain separate receipts.
3. Calibrated physical speed/memory Pareto, including prior baseline and retries; independently certified external comparator.

Attribution: Machin, Ramanujan, classical modular correspondence and Chudnovsky brothers retain their mathematical identities; Bishop/Bridges and Murray/Csimma retain real/completion machinery. Earlier DASHI CM two-slice and rational certificate owners retained. New contribution here is explicit uniform branch/width bounds and a source-written native limit consumer with the quantified source gap exposed.
