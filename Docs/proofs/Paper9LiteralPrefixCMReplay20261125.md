# Paper 9 — literal rational prefix and original CM163 exact replay

25 November 2026. Parent 6a9c3e93394d02a093c31beecf104320e41f5cad. No CI, compiler, kernel or benchmark. Source-written proof terms may need elaboration repairs. Original exact Python certificate sources executed locally; no analytic proof promoted from a finite receipt.

## F1 original raw prefix

Read HypergeometricBSplitIntegerMergeExact (blob 92f4ca0bb72666503c2079d1d841755c44be0ef5), BishopChudnovskyRationalMidpointExact (4e91e1c5f8417d308ab60a3027a8d321dee156e2), IndexedEdgeAlgebra, PositiveGap, PairedTotality and WidthReflection. The original B_split is identically one. With raw P,Q,T and literal leaves p_n,q_n, a_n=A+Bn, define U_n=P_n/Q_n and S_n=T_n/Q_n. Exact denominator-cleared merge implies U_(n+1)=U_n p_n/q_n and S_(n+1)=S_n+a_n U_(n+1). The original positive denominator owner supplies Q_n>0. New BishopChudnovskyPrefixSemanticsExact.agda (ae698073bb899e13d5f9415e0d6754705bb86097, 1e9eccd0973efde95c34e50b62f9626423a27185) writes intended rawProductStep, rawSumStep, productSemantics, prefixSemantics and literalPositivePrefix on actual positiveView via the existing WidthReflection View. No new Bishop real.

Lean companion Integration/Paper9LiteralFactorialPrefix.lean (92599ad2ed252824d163640fd10f4308893434b5) mirrors the literal signed integer recurrence, keeps q positive, consumes existing coeffSucc and cmRatio, writes productFactorial and sumFactorial for every index and literalPrefixTendsto to the actual weighted hypergeometric jets. The empty prefix is n=0; the first unweighted term is one. For N terms, S_N = sum_(n=0)^(N-1) (A+Bn)(-1)^n(6n)!/((3n)!(n!)^3 C^n). Local Python Fraction and independently evaluated factorials checked both signed product and weighted prefix at all 96 indices (192/192); SymPy verified the denominator-cleared addition identity. These tests do not prove the native induction. Still required: prove the factorial identification on the Agda carrier or sound cross-prover rational reflection, including actual original source coordinates. No undocumented equivalence of real carriers.

## Original CM163 replay — exact source execution

Recovered actual source bytes and checked Git blob hashes locally before execution:
- check_cm163_modular_diagonal.py: add8e35866aa1e9f379b4a57059c4487e4c7241c
- check_cm163_derivative_slice.py: 0c1f7d04618943d6b9941f433ceed8c5cd9fd590
- check_cm163_dyadic_j_integer_certificate.py: 8581a684cfb6ba6bfbfa45adbf6bfe01e9617258
- check_cm163_source_bound_jet.py: c567dd5bfd9500309bca8daa3f79480f7a53af9d

Original dyadic checker passed at 128,160,256 bits. Approx widths 0.0360563129119842, 8.395014543082611e-12, 1.44851224556475e-31. Exact 128-bit offsets multiplied by 2^128 are -121397398953732472506062368501224644 and 12147930101178244703017603450764613085, matching the existing Agda receipt. Conditional analytic interpretation remains separate.

Original diagonal(41) and slice_poly(41,-640320^3) constructed the degree-82 and degree-42 polynomials; the original derivative_slice.main consumed these actual polynomials and passed. Then ran the exact committed source_bound_jet checker with the signed hexadecimal coefficient packet, including independent forward Laurent substitution, constant/linear zeros, nonzero transverse coefficients, strict complement dominance, original dyadic endpoints and signed scalar jet. EXIT 0; PASS finite original CM diagonal/slice Laurent replay, isolation and signed scalar jet. No floating-point acceptance. The checker shares the original j_unit producer; not an independent analytic construction. Dominance integer floor(left/right)=6593105375567751, left/right bit lengths 4711/4659. kappa=-77859659565707/19943834790540897829879824384000; s2=77265280/90856689; (1-s2)/6=A/B. Both complete signed coefficient arrays preserved in local JSON artifacts; only the compact receipt and regeneration procedure are committed here.

Reproduce from repository scripts directory:
```python
import json
import check_cm163_modular_diagonal as d
import check_cm163_derivative_slice as s
P=d.diagonal(41)
S=s.slice_poly(41,-640320**3)
open("coefficients.json","w").write(json.dumps([[hex(int(c)) for c in v.all_coeffs()] for v in (P,S)]))
s.main(lambda _:P,lambda *_:S)
```
```sh
python check_cm163_dyadic_j_integer_certificate.py --bits 128 160 256
python check_cm163_source_bound_jet.py --coefficients coefficients.json --output receipt.json
```
Executed with 90-second timeout per producer/replay process; both exited zero. SHA256 coefficients.json (no trailing newline) 000303d3c03b72f28a67fb4c2d9e690b05761626b4f6c8e1c2b603ad9553b5d4; receipt.json e7c41e260881febf3257bfc07e6eb4a32ca587e4c139405a55c8a487cc10f187. This is reproducible finite execution evidence, not a kernel reflection theorem.

## Actual CM point, sign and selected domain

For tau=(-1+i sqrt163)/2, f(tau)=tau^2+tau+41=0, h(t)=-41/(t+1), alpha=41/(tau+1)^2=-tau/(tau+1), gamma=-82/(tau+1)^3. Exact reductions: h(tau)=tau; 41 alpha^2+81 alpha+41=0; 82alpha+81=-(2tau+1)=-i sqrt163; gamma(2tau+1)=2(alpha^2-alpha). The actual upper-half-plane sign is negative imaginary, not a free conjugate choice. SymPy reduced all four rational residual numerators modulo f to zero. Lean Integration/Paper9ActualCMPoint.lean (73d3d41742e640534eaa1c64150ef86c25e319a1 then a83e83f45ebd8c71b2b692dfc31bd795a6bbfa5b) writes actual cmTau, heckeDerivative, heckeSecondDerivative, signedOrientationActual, gammaIdentity, cmQPhase and cmQSmall. The intended selectedHyperAtCM and selectedFirstJetAtCM consume actualHyperIdentitySelected and its first jet at this point. These source terms have NOT been compiled. Original E4/E6 real-positive branches and actual signed s2 normalization still need binding.

## Next critical gates

A3 actual invariant Hecke product/Laurent coefficient binding and pole removal, A4 native finite coefficient/dyadic analytic reflection, A5 actual Taylor source and signed correction, A7 positive real source binding, A1 original Machin semantics and F1 Agda factorial reflection, then F5 all-index rational crossed inequalities. The prior downstream width/budget/convergence consumer is already present. No new general-purpose infrastructure and no production GMP changes. F6-F9 remain open. Original classical Hecke/CM, Ramanujan, Chudnovsky, Machin, Bishop/Bridges, Murray/Csimma, Mathlib, prior DASHI/JMD donor attribution retained. New work here is original source execution, native rational prefix proof source, and actual CM point/jet source application.
