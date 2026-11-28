# BSD P0 — Hecke-translated Kurihara anchor and finite analytic-source recovery (25 November 2026)

Parent: 42a1cb9c44ae0a3c6b641f9e4ade08ce2a0ec359. The complex jet, Selmer, Kummer, Sha, Mellin and terminal rank comparison already have original owners. No replacement interfaces. This tranche proves a classical same-source recovery lemma, not universal BSD.

## 1. Original constructors and source correction

Reuse Agda EllipticSelectedHeckePrimePowerExact (original selected Frobenius / Hecke recurrence), EllipticCMNormalizedOneDimensionalQSeriesExact, scripts/check_bsd_level32_sturm_shortcut.py, MellinSplitFunctionalEquationExact, EllipticCMLevel32FrickeMellinExact. The actual generic newform and all-prime identities are supplied by classical modularity and Hecke theory; the selected Agda source is not promoted to a generic native proof. Lean MillenniumBSDUniversalRankWeld (blob 838c4e0877a47461dbdbf11b559825e74d96a868), rank_factorization, analyticRank_eq, BSDClayCoreObligation and universalBSDRankTheorem_of_background remain the literal consumer. Existing cohomological and finite Selmer owners remain unchanged.

Correct citation: Chan-Ho Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, https://arxiv.org/html/2203.12159v5, Theorem 1.8 (not 1.9 in v5); Corollaries 1.12, 1.13. In v5 Conjecture 1.9 concerns the Tamagawa valuation. For p>=5, surjective residual representation, p-unit Manin constant and nonvanishing collection, the order of the collection is the p-infinity Selmer corank. No finite Sha assumption in the corank statement. The theorem does not assert equality with the complex analytic rank.

## 2. Exact original source transport

Let E/Q have conductor N and normalized weight-two newform f=sum a_n q^n. Let lambda(r)=[r]^+ be Kim's period-normalized plus modular symbol on the rational cusp r. The normalized holomorphic primitive has q-expansion sum a_n q^n/n, with the consistent sign fixed by the integral from r to infinity. Taking the real part and dividing by the same nonzero real period gives lambda. For a good prime l, Hecke on the weight-two form is l f(lz)+l^(-1) sum_b f((z+b)/l), b=0,...,l-1. Integration of the pullback differentials (the factors cancel the change of coordinate) gives

a_l lambda(r)=lambda(lr)+sum_b lambda((r+b)/l).

At l|N, U_l omits the first term. The root-of-unity sum vanishes unless l divides the Fourier index; the integrated coefficient identity is the same as the original Hecke recurrence. The q-series manipulations hold inside the upper half-plane; rational cusp integrals extend by cuspidal convergence. The plus projection commutes with these real Hecke correspondences. This is a classical modular-symbol identity; see https://www.wstein.org/books/modform/modform/modular_symbols.html and https://www.wstein.org/edu/Fall2003/252/references/cremona-algs/Cremona-Algorithms_for_modular_elliptic_curves.pdf.

For an admissible squarefree index m, choose integer representatives of its discrete-log weights w_a. Fix them for every evaluation. D_m(h)=sum_{a unit mod m} w_a h(a/m). D=D_m(lambda) is a rational lift, p-integral under Kim's hypotheses; its class modulo the original I_m is the Kurihara number. D nonzero modulo I_m implies D nonzero in Q. Then H_l=D_m(T_l lambda)=a_l D, where T_l is the explicit path action above (U_l at bad primes). Thus a_l=H_l/D exactly. Choosing other lifts of weights may change D and H_l but not their ratio when the denominator is nonzero. This does not identify the raw rational lift with a canonical Kurihara number beyond the prescribed quotient. In particular, H_l must be evaluated using the actual translated cusp paths, not supplied from an assumed a_l. Retain repeated cusps and bad-prime branches.

## 3. Sharp finite-precision bound, with valuation residual

Suppose D and H_l are retained modulo p^K and v=v_p(D)<K. Divide the two residues by p^v and invert the resulting unit D/p^v modulo p^(K-v). This recovers a_l modulo p^(K-v). Division by the original nonunit in Z/p^K is NOT allowed. Precision loss v is exact; the surviving residue alone cannot distinguish a_l and a_l+p^(K-v).

The original conductor gives the weight-two Sturm bound
B=floor([SL_2(Z):Gamma_0(N)]/6)=floor(N product_{q|N}(1+1/q)/6).
See the existing E32 Sturm shortcut and https://www.lmfdb.org/knowledge/show/cmf.sturm_bound.

Recover only primes l<=B. Hasse and the bad-prime coefficients imply |a_l|<=floor(2 sqrt(B)). Thus p^(K-v)>2 floor(2 sqrt(B)) suffices for unique signed integer recovery at every prime l<=B. All composite coefficients up to B follow by multiplicativity and the good prime-power recurrence a_{l^(j+1)}=a_l a_{l^j}-l a_{l^(j-1)}, with a_{l^j}=a_l^j at bad primes. Equality of the first B coefficients of actual forms of this level and weight identifies the whole newform. The normalized completed L-function, its functional sign and every analytic jet are then uniquely determined. Reverse direction: the normalized f determines all period-normalized symbol ratios H_l/D; actual E period normalization and index must be retained to recover the arithmetic residue itself. The newform identifies the rational isogeny class, hence Mordell-Weil rank and p-infinity Selmer corank are also invariant within the class. This does not imply the two ranks equal.

For finite precision above I_m, use the same fixed integer weights and original p-integral symbol values at higher precision; this is an analytic-source recovery observation, not a canonical higher-precision extension of the original Kurihara number or an additional arithmetic theorem. No claim that I_m itself always contains enough precision. No need to assume CM exclusion for the Hecke recovery lemma; Kim's arithmetic theorem does have the stated hypotheses.

At selected N=8,840,664, index=20,217,600 and B=3,369,600. For p=5, a unit anchor would require K=6 for the prime-only sufficient bound (rather than K=11 using |a_n|<=2n for all n<=B). This is a bound calculation, not evidence of an actual suitable anchor or evaluations for that curve. No selected rank proof is rerun.

## 4. Exact endpoint frontier

For Kim-admissible p, write k=ord(delta), d=corank Sha[p^infty], r=rank MW, a=analytic rank. Existing Kummer gives r+d=k. The required comparison is still k=a+d, equivalently r=a. Kim v5 Corollary 1.12 gives k congruent a mod 2, not the integer equality. Retaining a nonzero Kurihara anchor and its Hecke orbit is sufficient to identify the original analytic source, not to prove a formula for the order of vanishing from the minimal squarefree index. H_l=a_l D is an eigenvalue identity; it does not supply an independent rank comparison or turn approximate analytic values into exact zero tests. No arbitrary identification between real log path derivatives and finite discrete-log contractions. No new generic jet or Selmer framework. The ordinary BSD terminal may be attacked directly without requiring this optional Kurihara route, particularly for CM or other uncovered cases.

The exact remaining mathematical obligation on this route is a cross-identity comparing complex vanishing with the arithmetic quotient after separating the divisible Sha residual. Existing higher Fitting ideals determine Selmer structure under hypotheses but do not separate its divisible MW and Sha components. A proof must either establish this separation and the appropriate complex-order identity, or bypass them by a direct rank theorem. Do not count source recovery as paying the universal equality.

## 5. Execution and provenance

scripts/check_clay_hecke_symbol_recovery.py: exact finite root-of-unity trace, rational integrated Hecke coefficients for arbitrary finite polynomial data, residue decoding with nonunit valuation, insufficient-precision collisions, and actual conductor/Sturm-bound arithmetic. Local Python and Python -O both 15,570/15,570 PASS under 90-second timeout. Git blob ec4d8522c833e934a7414e1cd635248040242f94, byte-identical local and remote. No actual modular symbols evaluated, no native kernels, no CI, no universal rank equality. Attribution: classical Hecke/modular symbols, Hasse, Sturm, Kim and Kurihara; DASHI composition and exact controls. No new external theorem claimed.
