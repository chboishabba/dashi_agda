# RH/GRH P0 — actual ζ angular population and signed zero–Gamma reverse solve (23 November 2026)

**Scope / admission:** We ACTUALLY attempt the original selected-W signed zero source. The all-large-height **existence of zeta zeros inside two certified negative-kernel angular sectors** is a consequence of the standard unconditional Riemann–von Mangoldt zero count, exact zeta strip, original source moments, and the quantified harmonic sign-sector inequality. This argument is written mathematically and checked by SymPy; it has **not** been implemented or replayed in the Lean/Agda kernel. Independent mpmath actual-zeta numbers at 10^6 and 10^6+2 have source-uniform analytic sign margins but the numerical zero locations and quadrature are **not rigorous interval certificates**. The entire P0 strict signed inequality is **OPEN**, and GRH additional all-character formal admission is separate.

## Original owners, same W, same physical variables

On `chboishabba/dashi_lean4` `main`: `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean` owns the same-object equalities `signedLiteralPairSourceTerm_eq_normalizedPairKernel` and `signedNormalizedPairKernel_eq_jointJet` with original `P_W=quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t`; `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleQuantitativeBand.lean` owns `||P_W||_1<5184` and support `|v|<pi+1<5` for every original selected W at t>=200; `...SignedPolePair.lean` owns the selected floor `T_W=W.targetStrength>=7*pi^4/1600>567/1600`. The source's J2 and J4 theorems imply `M0=0`, `M2=0`, `M4=-4T_W`.

`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean` owns `completedSignedResidual_eq_jointPairSource`, with the exact **one-half** normalization. `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` owns `postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack` and the nonnegative full local slack. `Synthesis/RiemannZetaMuZeroCountOneSided.lean` owns an unconditional original `N(A,B)-int_A^B mu=O(log(A+3)+log(B+4))`. External source for critical-line verification below 3e12: Platt and Trudgian (2021), *The Riemann hypothesis is true up to 3·10^12*, DOI 10.1112/blms.12460, https://doi.org/10.1112/blms.12460 .

Keep all original zero coordinates, including `rho=beta+i gamma`, multiplicity `m_rho`, horizontal `a=beta-1/2`, physical height `t`, normalized `alpha=a/(t/16)`, `q=(gamma-t)/(t/16)`, and the smooth Gamma density `mu(tau)=[Re digamma(1/4+i*tau/2)-log pi]/(2*pi)`.

Define the **original** pair kernel

    K_W(alpha,q)=integral P_W(v) cosh(alpha*v) cos(q*v) dv.

Then the source per-zero term is exactly `m_rho*K_W(alpha_rho,q_rho)/(t/16)^2`. Its zeroth and second moments vanish; no invented smooth bump or fixed R is used.

## A. UNCONDITIONAL all-large-t occupancy in two genuine negative sectors

Fix `h=1/10000`, `r=t/16`, and two positive-ordinate windows on either side of t:

    I_t^- = (t-r*h/2, t-r*h/4]
    I_t^+ = (t+r*h/4, t+r*h/2].

For ANY actual nontrivial zeta zero with gamma in either window, even a hypothetically off-critical one, the original critical-strip bound gives `|alpha|=|beta-1/2|/r <= 8/t`. At `t>=960000`, this is <= `|q|/3` because `|q|>=h/4`; also `sqrt(q^2+alpha^2)<h`. With `x=|alpha/q|<=1/3`,

    (q^4-6*alpha^2*q^2+alpha^4)/(q^2+alpha^2)^2
       = (1-6*x^2+x^4)/(1+x^2)^2 >= 7/25 > 1/20.

The exact factorization of the excess is

    (1-6*x^2+x^4) -(7/25)*(1+x^2)^2
       = (18/25)*(x^2-1/9)*(x^2-9) >= 0.

Thus the existing *uniform actual selected-W harmonic sign-sector* estimate gives

    K_W(alpha_rho,q_rho)
      <= -(9/12800)*(alpha_rho^2+q_rho^2)^2
      <= -(9/12800)*(h/4)^4 < 0.

Crucially, **these are genuine possible source zero coordinates, not hypothetical bit addresses**. The signs are established for *any real beta in the critical strip*, not by presupposing RH.

Prove occupancy next: `mu(x)=(1/(2pi))log(x/(2pi))+O(x^-2)` at large positive x, and hence for all sufficiently large t, uniformly on both `I_t^\pm`, `mu(x)>= log(t)/(4pi)`. Each interval has physical length `r*h/4=t/640000`, so

    integral_(I_t^\pm) mu >= t log(t)/(2560000*pi).

The original unconditional arbitrary-endpoint RvM theorem gives

    N(I_t^\pm) >= t log(t)/(2560000*pi) - 2*C_RvM*log(2t+4).

The RHS is eventually positive. Therefore **for every sufficiently large t both I_t^- and I_t^+ contain actual zeta zeros, counted with multiplicities, and EVERY one lies in the original selected-W certified negative kernel sector**. An effective threshold needs the actual source's RvM constant and mu cutoff; `960000` alone is only the angular cutoff and MUST NOT be advertised as the unconditional all-height occupancy threshold. This proof is independent of RH; no claims about those zeros' individual real parts.

The raw annular `sum m K_W/r^2` is strictly negative once populated. **This does NOT make the original P0 zero-minus-Gamma comparison negative:** the corresponding `int_I K_W(0,q) mu/r^2` is negative too, and is SUBTRACTED.

## B. Exact original zero-minus-mu/horizontal BIDI decomposition and reverse-solved P0

For an arbitrary bounded Borel window `I` away from q=0, define

    E_I(W,t) = (1/r^2) [
       sum_{actual zeta zeros rho: gamma in I} m_rho*K_W(alpha_rho,q_rho)
       - integral_I K_W(0,(tau-t)/r) mu(tau) d tau
    ].

Exact linear decomposition without dropping t/q/beta/multiplicity:

    E_I = V_I + H_I,

    V_I = (1/r^2) [
       sum_(rho in I) m_rho*K_W(0,q_rho)
       - integral_I K_W(0,q) mu(tau) d tau
    ],
    H_I = (1/r^2) sum_(rho in I) m_rho [
       K_W(alpha_rho,q_rho)-K_W(0,q_rho)
    ].

On the two micro-annuli, `H_I` is **NONNEGATIVE** (and strictly positive if any member is truly off-critical) by the stronger source-uniform horizontal estimate below. The raw zero sum is negative, but its horizontal correction raises the signed zero source relative to the critical-line vertical baseline.

The original completed high source is `1/2*(sum off-ordinate pair source - full signed mu integral)`. Therefore, with `E_{\rm rest}` the exact complementary ALL-ordinate source (including far q, opposite gamma and all other original zeros), and `S_W` the canonical nonnegative local slack, original P0 is

    E_{I^-}+E_{I^+}+E_rest+S_W < 4*d_W(target).

**Reverse-solved P0:** `E_rest < 4*d_W(target)-S_W-E_{I^-}-E_{I^+}`, with no dropped or double-counted original contributions. The annulus proof furnishes neither the sign nor the necessary bound of `E_rest`; `E_rest` includes the full unknown signed correlation and Gamma compensation. A negative raw zero sector or a positive original off-line target defect alone does NOT settle this terminal.

## C. New ORIGINAL selected-W off-axis horizontal positivity, with an alpha-squared margin

Let `H_W(alpha,q)=K_W(alpha,q)-K_W(0,q)`. The even compact source yields `H_W(0,q)=0`, `partial_alpha H_W(0,q)=0`, and for `0<=|s|<=|alpha|<=|q|/3`,

    partial_alpha^2 K_W(s,q)
      = integral P_W(v)*v^2*cosh(sv)*cos(qv) dv
      = 2*T_W*(q^2-s^2)+R4(s,q),

where the source moments `M2=0`, `M4=-4T_W` are retained exactly, and

    |R4(s,q)| <= (5184*5^6*2/24)*(q^2+s^2)^2
               <= (25,000,000/3)*q^4.

For `|q|<=h/2=1/20000`, the target floor gives

    partial_alpha^2 K_W(s,q)
      >= [2*(567/1600)*(8/9) -
           (25,000,000/3)*(1/20000)^2]*q^2
       = (731/1200)*q^2.

Integrating twice with the exact even-in-alpha initial conditions obtains

    *** H_W(alpha,q) >= (731/2400)*alpha^2*q^2 > 0 ***

for every `0<|alpha|<=|q|/3`, `0<|q|<=5e-5`, and the original selected W at all high t. This is NOT a loose `O(h^6)` approximation and stays nondegenerate as `alpha->0`. In the real source, every off-critical zero in the annulus contributes **positive horizontal compensation**, with multiplicity and `r^-2` retained. Critically, this positivity does not imply a real off-critical zero exists.

## D. The same exact source exposes the RvM-only weighted obstruction

Because `M0=M2=0`, the exact original selected-W support/mass bounds imply on the real q-axis

    |K_W(0,q)| <= (5184*5^4/24)*|q|^4 = 135000*|q|^4,
    |dK_W(0,q)/dq| <= (5184*5^4/6)*|q|^3 = 540000*|q|^3.

Apply Stieltjes integration by parts to the ACTUAL count-minus-mu measure on one annulus, using `|N(A,x)-int_A^x mu| <= 2 C_RvM log(2t+4)`. Then

    |V_I| <=
      (540000*C_RvM*log(2t+4)/r^2)*(h/2)^4
      = O(h^4 log(t)/t^2).

That is a rigorously source-uniform absolute bound but still **FOUR POWERS** larger than the target same-ordinate off-critical defect `d_W(a)=O(a^4/t^6)` for fixed horizontal `a=beta-1/2`, and even weaker when `a->0`. This DIRECT original zero-minus-mu cut is not paid by RvM alone, consistent with earlier R2-N0 fourth-primitive counterexample. The required high-source proof must use zeta-specific **signed correlations** (or an independently admitted external proof), not zero density or unsigned shell counts.

## E. Actual finite-height numerical BIDI, including full Gamma subtraction

Executed exact source-aligned regression `scripts/check_rh_p0_actual_zero_annulus_bidi_20261123.py`. Git **blob** `38636aa9a69e99069666cfe420ac287da9958d7f` matches byte-for-byte the locally executed, `py_compile`-passing script; SymPy exact rational sector/horizontal/Stieltjes tests PASS, high-precision mpmath `nzeros`, `zetazero` and original **digamma mu** quadrature PASS, independent compact-C∞ bump fixture PASS (fixture is NOT the original abstract selected Mathlib `unitContDiffBump`).

At t=1000000, `r=62500`, the negative-sector intervals are `I^-=(999996.875,999998.4375]` and `I^+=(1000001.5625,1000003.125]`.

| t | side | numerical zeros | `A_I=sum q_gamma^4-int_I q(tau)^4 mu(tau)dtau` | rigorous selected-W **remainder bound conditional on numerical inputs** gives |
|---|---|---:|---:|---|
| 1000000 | left | 3 | +2.176974085644947e-18 | `E_I <= -2.753511492e-29` |
| 1000000 | right | 2 | −1.855723048419431e-18 | `E_I >= +2.357779819e-29` |
| 1000002 | left | 2 | −2.536135528855763e-18 | `E_I >= +3.386549467e-29` |
| 1000002 | right | 3 | +4.191243954522473e-20 | sign **UNDETERMINED** |

The conservative bounds use `T_W>567/1600`, `|E6|<225000*|q|^6`, and `int_I|mu|` (not the incorrect `|int_I mu|` substitute). The ratios of quartic main margin to the uniform remainder at t=1000000 are **6.117** (left) and **6.262** (right). For the **bilateral union**, t=1000000 is undetermined by this bound, but at **t=1000002** the same source-uniform test gives `E_{I^-}+E_{I^+} > +2.785106253e-29` on the numerical input. The original W itself is not reconstituted numerically: the proof envelopes apply for any source-selected W satisfying the floor, mass, support and moments, which is a stronger quantifier than one hand-picked surrogate. All actual known zeros in these samples have `alpha=0`, consistent with independent Platt–Trudgian rigorous verification of RH below 3e12; that paper does NOT supply a certified enclosure for each mpmath-reported ordinate in this test.

**Do not promote:** the mpmath nzeros/zetazero and quadrature results are numerical, not interval enclosures. Even a fully certified finite-height sign would not prove the universal high **off-critical target** implication, as this t lies in the already independently verified lower RH region. The sign-reversing ANNULLAR zero-minus-Gamma evidence is a counter to naive pointwise negativity, not a counterexample to RH or a theorem about the complete source sign.

## F. Genuine P0 remaining min-cut, explicit acceptance

The next required mathematical theorem (not new source geometry) is an independent same-selected-W bound on `E_rest` strong enough to defeat `S_W+E_{I^-}+E_{I^+}` at EVERY hypothetical high off-critical target, with actual zero multiplicities, complete horizontal phase, full exact mu, and all q/negative ordinate/far sectors. Equivalently directly prove `H_W+S_W<4d_W(rho)+I_W` or existing R2-S0 finite signed `H_n+E_n+S_W<T_W(rho)` / R2-S1 sharpened compensation. The boundary is exact; all-local sign, RvM, Gamma-only, finite-height count, atom/dyadic reindexing and existential test choice alone do not pay it. Maintain separate external original all-character Lean 4.33.1 kernel-axiom/root import and Agda H_X→sampleTest same-object admission.

**Attribution:** Riemann–von Mangoldt original zero-count theorem, existing Zeta23 mu/zeros, Platt–Trudgian finite RH verification (only its published range), existing Lean signed quartic W and paired source/terminal owners, new P0 two-annulus zero occupancy and same-selected-W alpha-squared horizontal bound, and locally executed non-promotion tests. **RH and GRH OPEN**. No Lean/Agda kernel or GitHub CI was run.
