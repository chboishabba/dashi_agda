# YM P0 CMP102 — original A/B series uniform-modulus completion

23 November 2026; PR #1536 master-based branch. Source-first mathematical certificate; **no Agda kernel or CI execution**.

## Original source and exact scope

The original CMP109 positive series coefficients are a_n=1/(2n+2)!, b_n=1/(2n+3)!. The existing `BalabanCMP109BishopRootFreeSeriesExact.agda` on current `master` already constructs Bishop `aSeries X inside` and `bSeries X inside` as limits of `Seq.SeriesOf (term aCoefficient X)` and its B counterpart for |X|<=1/4. The original analytic module has since been imported onto #1536 at the identical source blob, and the same-source BIDI coefficient bridge is present. These source imports do not establish Agda kernel acceptance or the finite-polynomial limit comparison. Nothing below redefines the represented limits.

The new original #1536 `YMClayCMP102OriginalEndpointCauchyShiftExact.agda` is a **source-written, kernel-pending** proof of the coefficient identities e_n=o_n at every degree, with e_0=2a_0, e_n=2a_n+sum_{i+j=n-1}a_i a_j for n>=1, o_0=1, o_1=2b_0, o_n=2b_{n-1}+sum_{i+j=n-2}b_i b_j for n>=2. Its precise endpoint/sign identifications remain a pinned-Agda verification obligation.

## Direct analytic completion without an infinite-product Cauchy reindex

For N>=1 set A_N(X)=sum_{n=0}^{N-1}a_n X^n and B_N analogously, and G_N(X)=1-2A_N(X)-X A_N(X)^2+2X B_N(X)+X^2 B_N(X)^2. All coefficients of degrees 0,...,N-1 are exactly zero by the original finite CMP102 source identities, including the exceptional odd singleton and both even endpoints. Thus G_N is a polynomial supported only in degrees n>=N.

The original factorial ratios are exact:

- a_{n+1}/a_n=1/((2n+3)(2n+4))<=1/12;
- b_{n+1}/b_n=1/((2n+4)(2n+5))<=1/20.

Consequently 0<=a_n<=(1/2)12^{-n}, 0<=b_n<=(1/6)20^{-n}, and the positive coefficient sums of every A_N and B_N satisfy A_N(1)<=6/11, B_N(1)<=10/57. The complete coefficient l1 norm (before cancellation) of G_N is bounded by

  1+2(6/11)+(6/11)^2+2(10/57)+(10/57)^2 = 1089001/393129 < 3.

Since G_N has no degrees below N, **for every signed real X with |X|<=1/4**,

  |G_N(X)| <= 3*4^{-N}.

This is an all-N exact coefficient-support proof, not extrapolation from a sampled grid or the first 48 polynomials. Furthermore the original factorial ratios give explicit uniform limit tails

  |A(X)-A_N(X)| <= (24/47)*48^{-N},
  |B(X)-B_N(X)| <= (40/237)*80^{-N}.

The full represented limits and partial sums are bounded respectively by 6/11 and 10/57 in absolute value on the original disk. Therefore the elementary difference-of-squares inequalities yield

  |G(X)| <= 3*4^{-N} + (25/11)*(24/47)*48^{-N} + (119/228)*(40/237)*80^{-N},

where G(X)=1-2A(X)-X A(X)^2+2X B(X)+X^2 B(X)^2, and this inequality holds for every N>=1. The RHS tends to zero effectively and independently of X, proving the **mathematical same-represented-series identity G(X)=0 on |X|<=1/4**, conditional in Agda on kernel certification of the finite row witnesses and the explicit source attachment of the already-constructed master CMP109 limits. It does not require new series or a formal Cauchy-product theorem.

## Exact acceptance and negative control

`scripts/check_ym_cmp102_uniform_analytic_modulus_20261123.py` locally executed with Python `fractions.Fraction`: **2072/2072 assertions PASS**. Checks ratios and coefficient majorants n=0..127, first N=1..48 full polynomial low-degree cancellation, full coefficient-norm envelope, omission of the final A endpoint (producing nonzero coefficient 2a_{N-1}), and signed test arguments including both original quarter-radius endpoints. The test supports the general symbolic proof above but is not its proof or an Agda kernel test.

## Precise remaining P0 obligations

1. **Kernel/branch:** typecheck the now co-located original CMP109 series, #1536 CMP102 finite theorem, same-source BIDI bridge and new finite-G limit transport under pinned Agda 2.9, including all transitive imports. Do not treat a source comment, a `machineChecked` tag or Fraction check as kernel acceptance.
2. **Source analytic:** implement the specific polynomial/limit comparison above using existing `Sequence` convergence and real polynomial continuity; identify the actual CMP102/Bishop chart argument X=-w, not an arbitrary renamed formal variable.
3. **Geometry:** source-selected Bishop quaternion norm, normalized SU(2) chord/trace deficit, CMP98 nonlinear background Q and actual CMP102 plaquette/minimizer domain. Earlier #1444 consumer remains conditional until a true same-module import/definition equality.
4. **Dominant physical P0:** original interacting 4D Wilson/Haar/F19 and actual CMP119/122 physical T, termwise absolute CMP116/W3 rooted-shell bound uniform in cutoff/volume, interacting E1 reflection-positive continuum, dense same-H OS gap, N1/G1. No Clay theorem conclusion follows from this analytic identity.

Attribution: original Wilson/Haar, Bałaban CMP98/102/109/116/119/122, classical factorial/Cauchy algebra, Bishop/Bridges and Murray/Csimma Bishop backend, prior DASHI original named owners. No substitute operator, new postulate, auxiliary gauge measure, or weakened radius.


## 23 November 2026 — source-level original G-prefix limit transport

On PR #1536, commit [050ce7ca](https://github.com/chboishabba/dashi_agda/commit/050ce7ca476c58b3945c4110d63d5f39395de1e4) adds `YMClayCMP102OriginalGFiniteLimitTransportExact.agda` using the *original* `CMP109.aSeries` and `CMP109.bSeries` with the *same* CMP102 coefficient histories and original `|X|<=1/4` premise. No new series or limit carrier is defined.

The source-written theorem `originalGPrefixConvergesToOriginalG` builds the finite five-term G_N limit from existing Bishop `Sequence.xₙyₙ→x₀y₀`, `xₙ+yₙ→x₀+y₀`, `-xₙ→-x₀`, and the source BIDI A/B convergence proofs. `originalGZeroFromOriginalPrefixConvergence` then consumes an **explicit** `Seq._ConvergesTo_ (originalGPrefix X) 0` witness and applies the original `Sequence.uniqueness-of-limits`. **This zero-prefix premise is not discharged by this module.** The old mathematical rational inequality `|G_N(X)|<=3*4^-N` remains to be translated into this exact Bishop zero-convergence witness. Thus this is real source-written limit compatibility, not a kernel-certified G(X)=0 theorem.

The new Agda file's Git blob is `670955eb1ed471584eec5637d4df6e6992c33322`, byte-identical to the locally authored source. Local Fraction cross-check: 80/80 five-term polynomial-expression comparisons for 16 prefix lengths at signed quarter-radius sample points. That check is **not an Agda kernel pass**.

### Exact import-safety preflight, fail-closed

A direct live source audit of 15 selected existing Agda files found **at least 13** specific `--safe` → non-`--safe` import edges. Affected safe consumers include `BishopFiniteEvenOddCauchyReindexExact`, `BishopUnsignedFactorialCauchyParitySplitExact`, `BishopSignTwistedFiniteCauchyCoefficientExact`, `BishopRound11SignedFactorialExponentEncodingExact`, and `YMClayCMP102NativeMasterSignedParitySpecializationExact`. Their non-safe imports include `BishopFinSumSeriesBridgeExact`, `BishopFiniteCauchyRowReindexExact`, `BishopExponentialSeriesConvergenceExact`, and other original parity/factorial owners. Count is a **lower bound within the selected dependency set**, not a whole-repository transitive audit. Do not solve this by deleting `--safe` pragmas without reviewing the full downstream trust contract.

Next exact local acceptance command in a populated checkout with pinned Agda 2.9 and compatible stdlib, using the existing project wrapper rather than CI:

```sh
DASHI_REPO_ROOT="$PWD" scripts/run_agda29_parallel_check.sh DASHI/Physics/YangMills/YMClayCMP102OriginalGFiniteLimitTransportExact.agda
```

In the current execution environment, neither Agda nor Nix is present and network cloning is unavailable. **No compiler was run; the kernel/import-safety gate remains OPEN.** Independent physical CMP119/122 T, absolute W3 and same-H OS remain entirely unpromoted.


## 23 November 2026 — local SymPy all-degree independent acceptance (instead of Agda/Lean)

Executed Python 3 with **SymPy 1.14.0** locally, not GitHub CI and not Agda/Lean. The committed independent checker is
[scripts/check_ym_cmp102_sympy_source_certificate_20261123.py](../../scripts/check_ym_cmp102_sympy_source_certificate_20261123.py) from commit [78937348](https://github.com/chboishabba/dashi_agda/commit/78937348be3a214f66ce83d53fe86400b35a73f4), Git blob **768a766a567c74b58b25de79efe6f8e579eb1d20**, verified byte-identical against the locally executed file (SHA-256 \`9109433495d14a8dd6cae11477dc21b476fb72c04b36b067cbfa6c29a0e4026a\`). Result: **2,602/2,602 exact assertion groups PASS**, including generic symbolic n, original 128 explicit coefficient degrees, 48 finite prefix polynomials, 240 signed original-radius boundary samples, 48 omitted-endpoint negative controls and factorial/majorant/tail constants.

Crucially, the generic **all-degree symbolic** cancellation is not extrapolated from those 128 degrees:

\`\`\`text
sum_{k=0}^{2n+2} (-1)^k binomial(2n+2,k)
= (1-1)^(2n+2) = 0, for all n>=0.
\`\`\`

Even/odd split of the original \`exp(z)*exp(-z)\` coefficient reproduces *exactly* the source CMP102 shifted Epart/Opart including the odd degree-0 singleton and both even/odd endpoints. SymPy independently reduces the original same-series function after the analytic substitution \`X=z**2\`:

\`\`\`text
E = 1+X*A = cosh(z)
z*(1+X*B) = sinh(z)
X*G = 1-E**2+z**2*(sinh(z)/z)**2
    = 1-cosh(z)**2+sinh(z)**2 = 0.
\`\`\`

\`G(0)=0\` is verified through the removable origin. This also gives an *ordinary complex-entire analytic identity* when the factorial functions are continued, **without changing the original Bishop CMP109 construction domain** \`|X|<=1/4\`.

The positive factorial majorants are unchanged: \`A_N(1)<=6/11\`, \`B_N(1)<=10/57\`, \`L1<=1089001/393129<3\`. For every N>=1 the original \`G_N\` coefficients vanish below degree N, and its first surviving coefficient is precisely **2a_N**. Hence the same uniform estimate \`|G_N(X)|<=3*4^-N\` and original tail modulus hold across all real \`|X|<=1/4\`. The coefficient and norm conclusions follow symbolically from finite algebra, ratio inequalities and the binomial identity; grid evaluations are regression controls, not the proof.

### Acceptance boundary

This is mathematical/SymPy closure of the all-degree analytic CMP102 A/B identity against the original factorial histories. It **does not** elaborate Agda, certify the original Bishop \`Seq._ConvergesTo_\` theorem \`originalGPrefix -> 0\`, fix the documented \`--safe\` import graph, identify the CMP102 native quaternion/chord physical source, or supply any original CMP119/122 physical T, absolute W3 or same-H OS mass gap. The Agda source \`originalGZeroFromOriginalPrefixConvergence\` still requires that explicit Bishop zero-convergence input; do not confuse the SymPy certificate with an inhabitant of that type. No Clay result is promoted.
