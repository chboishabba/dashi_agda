# BSD — universal Clay-rank versus strong-refined scope, S5/S6 fail-closed (2026-11-17)

### BSD P2 — consecutive ramified Kummer transition defect

Use original actual E/Q, all places, ell prime. At n+1 and n the exact sequences 0->E(Q)/ell^n E(Q)->Sel_{ell^n}->Sha[ell^n]->0 commute under reduction on MW, multiplication-by-ell on coefficients E[ell^{n+1}]->E[ell^n] on Sel, multiplication-by-ell on Sha. This follows from natural Kummer diagram (division point Q for ell^{n+1} maps to ell Q for ell^n) and local restrictions. The left map is surjective. Snake yields 0->ell^n E(Q)/ell^{n+1} E(Q)->ker(Sel transition)->Sha[ell]->0 and coker(Sel transition) is isomorphic to Sha[ell^n]/ell Sha[ell^{n+1}]. These are F_ell groups: kernel killed by ell by composing transition with coefficient inclusion (inclusion need not be injective on cohomology), cokernel killed by ell because ell times each element in smaller level lies in the image. Thus dimension d_n=z_1-(z_{n+1}-z_n), kernel dimension=r+(t_{n+1}-t_n)+z_1. Previous nonincreasing Sha increments imply d_n nondecreasing, eventually constant. Recover increment z_{n+1}-z_n=z_1-d_n, retain base z1, zero n=0, local place/ramification and actual transition maps; not reconstruct Sha group from dimensions alone. On direct-sum primary models of finite cyclic and Q_ell/Z_ell components, d_n counts the finite summands of length <=n, divisible components have zero transition defect. This model is not an assertion of finiteness or computation of actual Sha. Abstract rank-vs-divisible model collision: MW Z with Sha=0 versus MW=0 with Sha=Q_ell/Z_ell both have same cyclic Sel tower with surjective transitions, not examples of elliptic curves or a counterexample to BSD. Hence transition observer alone cannot replace actual arithmetic residual or analytic comparison.

P1/P2 classical source-level deduction from Kummer and snake, 270 exact primary-model count checks (not actual elliptic-curve arithmetic). Existing EllipticTwoDescentRoadExact, EllipticOriginalSelmerCohomologyExhaustionExact, selected Tate E32 and Fricke/Mellin (#1499/Lean #108), BSDUniversalScopeFirewallExact remain owners. Exact P2/S6 unpaid: all-E/Q analytic rank equals actual residual-corrected rank, without assuming full Sha finite or equating corank to rank. P3 all-rank quantifier, P4 actual BSD consumer, P5 native proof open. Refined Sha finiteness and leading coefficient separate.


## 23 November 2026 — twisted odd-cubic reverse-symmetry control

[Geometry-forward BIDI/reverse-solve](ClayFourLaneGeometryForwardBidiReverseSolve20261123.md) checks the *scope* of the original E32 involution. The same Legendre oddness cancellation holds for `x³-d²x` at good primes `p≡3 (mod 4), p∤2d`, but these are **different quadratic twists** when `d≠1`. A local exact regression checks 127 (prime,d) pairs below 301 and original E32 `a_5=-2` as a split-prime negative control; [script](../../scripts/check_clay_geometry_reverse_20261123.py). This mathematical symmetry neither identifies the E32 all-n q-series nor proves a chosen same-curve eta/Mellin source or universal S6 rank. Retain original selected E32 and Rubin S5 attribution; no S6 gate promotion.


## 23 November 2026 — original E32 inert-prime source-shortcut (no S6 promotion)

The original conductor-32 curve E:y²=x³−x has a_p=0 for **every odd prime p≡3 (mod 4)**. The [four-lane max-cut](ClayNonYMRHFourLaneGeometricMaxCut20261123.md) gives a direct classical proof: f(x)=x³−x is odd, chi_p(-1)=-1, and x↦−x cancels the complete finite-field character sum, including zero-character fixed points. This is an exact all-inert-prime character lemma for the same E32, not an E36/CM-j=0 substitution. The [executed script](../../scripts/check_clay_four_lane_geometric_shortcuts_20261123.py) checks 40 inert primes below 401; the split-prime p=5 has a_5=-2, so the shortcut does not apply to all primes.

The symmetry eliminates explicit coefficient enumeration on the inert-prime branch but does not identify the full q-series, prove eta modularity or original E32 Mellin, give a new Sha computation, run a native Agda/Lean kernel, or discharge S6 universal BSD. Earlier S5 selected-curve classical Rubin closure remains established prior work. Both universal BSD endpoints remain OPEN.


## Important correction to supplied explanatory text

Read Andrew Wiles, *The Birch and Swinnerton-Dyer Conjecture*, in Clay/AMS, *The Millennium Prize Problems* (2006), printed pages 32–33, official https://www.claymath.org/library/monographs/MPPc.pdf and Clay current unsolved listing https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/ .

**Official formal prize statement:** for EVERY elliptic curve C over Q, L(C,s) at s=1 has leading term c(s-1)^r with c nonzero and r=rank C(Q). In the official Wiles description, the full leading-coefficient expression with |Sha|, real period, regulator, torsion and Tamagawa appears in *Remark 1*, termed a **refined version**. Therefore the attached text's assertion that proving both rank and strong leading coefficient universally is explicitly necessary for the formally stated Clay conjecture is inaccurate. We track two targets:
- **S6-Clay**: genuine universal analytic rank equals algebraic rank for all E/Q, including arbitrarily high rank and non-CM curves.
- **S6-Strong**: universal finiteness of Sha and exact full leading coefficient as a strictly stronger refined research target.
Neither has been proved.

Also avoid saying *all individual rank >=2 cases are completely open*: the general higher-rank theorem remains open; individual curves can have certified rank and coefficient cases. Classically known rank zero/one results have delicate prime-by-prime refinements.

## Selected curve S5 remains classical, not native

Original E:y²=x³−x, conductor 32, j=1728 (CM by Z[i]); classical rank 0, E(Q)=(Z/2)^2, Sha(E/Q)=0, regulator=1, c2=2, and Omega=8L(E,1). Rubin's complex-multiplication work (see his 2006 MSRI lecture https://www.math.uci.edu/~krubin/lectures/msri2.pdf) and original classical 2-descent are external analytic/arithmetic inputs. SymPy checks `Omega*1*1*2/4²=Omega/8=L`, **not** Rubin's Euler-system proof.

## Native interface implemented (NOT kernel checked)

`DASHI/Mathematics/Arithmetic/BSDUniversalScopeFirewallExact.agda` imports the original `BirchSwinnertonDyerBoundary.agda`, rather than altering the arithmetic owner.

- `UniversalBSDRankInterface` requires for every `curve : ShortWeierstrassCurve` the curve-indexed actual `MordellWeilData`, `EllipticLFunctionData`, and its `BSDRankConjecture`.
- `UniversalBSDRefinedInterface` carries the rank interface and for every curve a leading-coefficient conjecture datum.
- `toySelectedTrue` and `toyUniversalFalse` are constructive logical controls proving that being true for a SELECTED Boolean index is insufficient to prove `∀ index`. These are not mathematical counterexamples to BSD.
- No concrete inhabitant of either universal interface is defined. The original `BSDScalarData` uses rational placeholders and cannot, by itself, realize genuine transcendental periods, analytic leading coefficients, or actual Sha finiteness. This source-meaning weld must be built, not inferred from records.

## Implemented local verification

`/mnt/data/check_bsd_universal_firewall_20261117.py` is a runnable, user-accessible Python/SymPy regression. `python check_bsd_universal_firewall_20261117.py --self-test` PASSED on 2026-11-17. It checks selected scalar arithmetic and four deliberate fail-open ledger mutations: marking S6 settled, claiming native S5 kernel acceptance, contradicting 14 open gates, and falsely setting S6 endpoint proved. In a repo checkout, `--ledger Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json --agda DASHI/Mathematics/Arithmetic/BSDUniversalScopeFirewallExact.agda` reads the ACTUAL source JSON and proposed Agda module. Python checks symbols and flags only, not Agda elaboration or proof validity.

## Exact still-missing constructions for universal S6

1. `bsdEveryRationalEllipticCurveSameObjectCarrier`: actual all non-singular E/Q with minimal models, isogeny-invariant L, Tamagawa and period normalizations; not just one short Weierstrass CM model.
2. `bsdEveryCurveAnalyticRankWellDefined`: actual completed analytic L and analytic order of vanishing, all E; modularity is known classically, original-type weld open.
3. `bsdAllCurvesMordellWeilAnalyticRankEquality`: universal theorem `ord_{s=1}L(E,s)=rank E(Q)` with *no* restriction to rank <=1, CM or conductor 32 — **the central Clay prize obstruction**.
4. `bsdAllCurvesHigherRankEulerSystemOrAlternative`: genuinely new higher-rank control/height or different valid proof mechanism; simply reusing CM Rubin does not give it.
5. `bsdEveryCurveShaFinite`: global arithmetic Tate–Shafarevich finiteness for every E/Q, essential for the strong refinement but NOT literally separately asserted in Wiles's formal prize conjecture.
6. `bsdEveryCurvePeriodRegulatorTamagawaSourceWeld`: same selected E all local data/height determinants and correctly normalized real periods in REAL analytic carriers, not generic rational scalar placeholders.
7. `bsdEveryCurveStrongLeadingCoefficient`: universal equality of normalized Taylor leading coefficient and actual arithmetic invariant ratio, all p and arbitrary analytic rank, with Sha finiteness.
8. `bsdUniversalNativeKernelReceipt`: proof terms for original concrete Lean/Agda fields in pinned versions, transitive axioms/audit, no postulate, no Set-valued dummy proofs, no selected-curve quantifier casting.

**S5 classical CLOSED; S5 native OPEN; S6-Clay OPEN; S6-Strong OPEN; overall 14/28 open; original Clay BSD terminal UNSOLVED.** Source attribution: Wiles/Clay for prize/refined distinction; Rubin for selected CM example; DASHI original source authors for generic boundary records; current contribution is only explicit new scope interface and tests.
