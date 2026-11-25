# Paper 9 — selected hypermetric comparison, cusp-order filtration and factorial source

Agda parent cc275ba209eed953d59b617f2a4df56ca3c131d7. Lean companion d77fc04324e7b15eab2266ed8911a567085e365e then e9b8e422c4b8503074dbf45d6bf6632bd711bbae. Source-written only, no compiler, kernel, CI, arithmetic execution or benchmark. Exact-head source elaboration still required.

## Reused source owners, not name-based equivalences

Actual repository files read at parent: KakeyaYMUltrametricPhysicalComparisonExact (32696afec0b99757e072ba9cbd48cfac522aa225), BalabanRGTwoMetricUniformComparisonExact (40d02cfbcf6f93064777319d0f2494ad3fca5fb6), E6HyperformH3ResidualReopeningMetricExact (a877bf3fc0a72d8f4717a8d30de45ad8965d5386), IndexedAffineNativeGraphTransportExact (ea67250b4f27a02b199f1f5bb4d95f00f25d2cd0). The RG theorem requires selected metric comparison constants and an explicit reopening error; the H3 owner is a local finite receipt for radical/phase splitting, not a universal analytic theorem. The indexed graph owner uses pulled-back actual adjacency, not naive chart adjacency. No claim of isometry between the signed 369 fibre and an analytic germ. Search for hypermetric literal on indexed default branches was limited; these are the recovered relevant owners, not an exhaustive branch audit.

HypergeometricBSplitIntegerMergeExact (92f4ca0bb72666503c2079d1d841755c44be0ef5), BishopChudnovskyIndexedEdgeAlgebraExact (18599edad11788cd331f1a5cc2fdbddd117b896a), BishopChudnovskyPositiveGapExact (4299c107bf1147d176db11409d349b03c97665a6), BishopExponentialSeriesConvergenceExact (b62d767e74c6473e31bdf86458d93445656f6978), BishopExponentialBinomialCoefficientExact (9a859cd73f1f8c0a6fe8064af0aa689d86678a68) are actual computational and constructive source donors.

## Fixed-radical metric comparison, exact shared endpoint

Let S_n=T_n/Q_n be original literal positive sums, n>=1; the nested adjacent intervals give A/2<S_n<=A, and |S_(n+2)-S_(n+1)|<=2^-41 |S_(n+1)-S_n|. For any fixed positive radical numerator r, pi observation is r/S_n. Exactly
 |r/t-r/s| = r |t-s|/(s t).
This is the actual two-metric comparison, with factors r/A^2 through 4r/A^2 on the selected band. Stronger for adjacent source brackets: their middle endpoint is shared, so
 d_pi(n+1)/d_pi(n) = (|S_(n+2)-S_(n+1)|/|S_(n+1)-S_n|) * S_n/S_(n+2)
 whenever denominator nonzero. Thus d_pi(n+1)<=2^(-40)d_pi(n), without dividing by the source edge; the division-free inequality holds also when it vanishes. Actual source orientation remains retained; signed edge and index recover original step, magnitude alone does not. For varying radical r' and new sum t,
 |r'/t-r/s| <= |r'-r|/t+r |s-t|/(s t).
This is the exact reopening-error channel corresponding to the donor RG theorem (not a claim of new physical metric). Lean reciprocalEdge, reciprocalAdjacentContraction, radicalEdge and combinedEdge source-write rational general laws; native specialization on literal positive source and comparison to actual interval endpoints still needs proof reflection. The existing independent F3 interval width bound remains the endpoint budget, not replaced by this fixed-radical result. Distinguish scale-indexed root refinement, sum refinement, and signed zero mode.

## Actual analytic branch and cusp-order residual

On the selected small disk x=E4 stays in the right half-plane, y=E6 apart. Define F=exp(log(x)/2) with principal log; F0=1, F^2=x. This is the same local normalized square root as binomial series (uniqueness from (F-G)(F+G)=0 near zero; both value1), not an inverse modular coordinate. New Lean rootFSquare, rootFDeriv, rootFirst bind the actual branch and first Euler derivative, using actual q-Ramanujan system for nonzero q, explicit slit-plane and y apartness. At zero use analytic continuation of the equality, not division by q. Iterated product laws require local identities on selected disk and actual second/third multiplier binding. The selected disk inequalities still need formal source proofs.

Use ord_0 on analytic germs, ord_0(0)=infinity (germ zero), and distance d(f,g)=rho^ord_0(f-g) for 0<rho<1. This is the actual analytic valuation ultrametric, different from the finite 369 metric; triangle law follows from divisibility by powers of q. For nonzero difference w with w0=0, pinned Mathlib AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff gives w=q^n g on a neighborhood, n>=1, g analytic, g0 nonzero. With U_L=x/y, U_L0=1, the actual Euler transport is
 L(q^n g)=q^n G_n(g), G_n(g)=U_L(n g+q g'), G_n(g)(0)=n g0.
Thus L preserves positive order, multiplication by z raises order by at least one because z0=0. The ODE residual is q^n R_n(g), where R_n(g)=G_n^3(g)-z*(G_n^3(g)+3/2 G_n^2(g)+23/36 G_n(g)+5/72 g). R_n(g)(0)=n^3 g0 !=0. Hence the residual cannot vanish as a germ. This proves local uniqueness of two analytic solutions with constant1 (difference solves linear equation), without inverse coordinate, numerical matching or full coefficient-convolution development. On connected selected disk use analytic identity theorem. Lean leadTransport, leadStepAnalytic, leadThird, residualUnitZero, residualUnitAnalytic, nonzeroLeadingObstruction source-write key pieces, not yet full germ uniqueness consumer; remaining local differentiability of successive units, linearity and factor/reassembly of actual ODE, then actual H(z) analytic solution and disk extension. No assignment of arbitrary 369 values to analytic variables.

## F1 original factorial series and exact term ratio

c_n=(6n)!/((3n)!(n!)^3 1728^n), c_0=1. Expand six and three factorial successors. Cancel (6n+2)(6n+4)(6n+6)=8(3n+1)(3n+2)(3n+3), and (6n+3)=3(2n+1). Then
 c_(n+1)/c_n = (n+1/6)(n+1/2)(n+5/6)/(n+1)^3.
The ratio is positive and strictly less than one for every n>=0. Thus 0<c_n<=1, series and all fixed Euler derivatives converge uniformly on compact |z|<=rho<1 via existing polynomial-geometric majorant concept. At original CM z=-1728/C,
 c_(n+1) z^(n+1) = [ -24(2n+1)(6n+1)(6n+5)/(C(n+1)^3)] c_n z^n.
This is the actual leaf ratio in BishopChudnovskyRationalMidpointExact; source-written Lean factorial3, factorial6, coeffSucc, cmRatio, cmTermSucc are all-index algebra, not 24 finite fixtures. Multiply by A+Bn after coefficient transport, so weights are not confused with term-ratio products. Prefix semantic induction: P_n/Q_n is product of ratios of n leaves (p0/q0=1); at n>=1 it is c_(n-1) z^(n-1). T_0/Q_0=0, T_(n+1)/Q_(n+1)=T_n/Q_n+(A+Bn)c_n z^n by actual prefixPStep/QStep/TStep. The recurrence closes mathematical finite correspondence; Lean mirror and native Bishop rational equality/induction still require binding and formal replay. Existing split-tree associativity owner retained, not replaced.

A2 source-written, A3–A5 actual Hecke/CM/Taylor reflection unpaid; A6 branch, leading-order transport and factorial ratio source-written but actual H analytic ODE and full uniqueness/period bind unpaid. F5 universal crossed rational endpoints still principal. F6–F9 unchanged. Attribution: classical factorial hypergeometric/Chudnovsky identity and analytic isolated-zero theorem (Mathlib contributors) retained; prior DASHI metric and original 369/JMD donors retained; new work is selected reciprocal shared-endpoint comparison and cusp-order consumer, not discovery of the classical identity or equivalence of the carriers.
