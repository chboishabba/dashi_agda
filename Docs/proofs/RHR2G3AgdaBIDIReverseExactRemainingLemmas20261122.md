## 22 November 2026 — finite-t × positive-width J2-preserving mixed jet; six-face geometry audit

Original same-source definitions consumed: `RiemannProjectiveQuarticFourWindowAtomic.lean`, `RiemannProjectiveQuarticFourWindowPoleSameObject.lean`, and `RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`.
Local executable: `scripts/check_rh_positive_width_finite_t_mixed_jet_20261122.py`.

Fix physical horizontal a=0 and normalized q=4; u=pi/t and eps=E[Y²]/2 for a common normalized even bump around every source centre. Enforce the *same original J2=0 condition* at each lambda by mu(lambda,eps)=mu0(lambda)+mu1(lambda)eps+O(eps²). The original finite pole weight is `cosh(8x/t)*cos(16x)*cos(cx)` and the exact selected determinant/profile orientation is `P_two*K_half-P_half*K_two`.

Independent local SymPy exact symbolic jets give:
```text
[eps^0 u^0] K = 0
[eps^0 u^2] K = 0
[eps^1 u^0] K = 120/13
[eps^1 u^2] K = 640*(2*pi-sqrt(3))/(39*pi) > 0
```
The pre-existing atomic calculation additionally gives
`[eps^0 u^4] K=5120/351` at a=0,q=4.
Consequently the **formal two-variable expansion** starts
```text
K(0,4;eps,u) =
  (120/13)*eps
 +[640*(2*pi-sqrt(3))/(39*pi)]*eps*u²
 +(5120/351)*u⁴
 + terms of higher order in eps and u.
```
The displayed mixed coefficient is strictly positive because 2*pi>sqrt(3).
No positivity for every finite u or selected compact positive radius follows without a *uniform remainder bound* and an exact source J2 branch. No numerical Gaussian surrogate is being silently identified with the Mathlib normalized bump.

### Exact six-face indexed transport audit (conditional structure, not an analytic theorem)

Three axes determine 8 typed vertices, 12 oriented edges, and 6 square faces:
- Reflection r: source `a -> -a`; apply to the original complex zero carrier WITH multiplicity. A kernel-even observation is not a proof of an analytic zero map.
- Smoothing b: atomic eps=0 -> original even-bump eps>0; preserves each signed centre, history/index and independently solves mu(eps) for J2=0.
- Pole limit p: finite u>0 -> u=0; retains normalized q as a selected coordinate, NOT gamma as a fixed ordinate. A moving q must be tracked when t changes.

Six faces are (r,b) at p=0 and p=1; (r,p) at b=0 and b=1; (b,p) at r=0 and r=1. Algebraic parity r commutes with the even source kernels at these fixed coordinates. The b/p faces are formally compatible for analytic Taylor germs *if* uniform source bump moments and mu branch hold; physical same-zero, finite-t source identification and convergence are OPEN and must not be marked as commuting Lean/Agda theorems. The q=4 moving ordinate and the fixed-physical-gamma chart are different observers and need an explicit change-of-coordinates edge, not an implicit cube equality.

For each vertex keep a tagged source record: analytic ζ-zero/not-a-zero status and multiplicity; physical (beta,gamma,t) and normalized (a,q); exact signed centre weights; mu selection; source pole determinant; original Hnear/Hfar and local slack; zero-observation vs genuine scalar zero vs balanced nonempty cancellation. C3 cyclotomic zeta, a neutral exponent-zero phase, and Riemann ζ(s) are distinct types. Retain signed ternary polarity and residual histories across all 12 maps; a Fourier-zero observer is not faithful on underlying modes.

**Terminal:** `H_n+E_n+S_W<T_W(rho)` for all hypothetical high off-line actual ζ zeros is still OPEN. Neither strictly positive q=4 response nor any of the six square sketches closes the signed aggregate or pays prime-side local slack.

---

## 22 November 2026 — J2-preserving positive-width second-moment jet (new exact local source calculation)

Read-back original source owners: Lean main
`Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean`
(`quarticFourNormalizedPoleWeight` = cosh(8x/t) cos(16x) cos(cx)),
`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
(signed profile 4G(x)[A1 cos(2x)-A2 cos(x)]), and
`Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean`
(the J2-null fourth-window family). This avoids confusing on-line pairings
with pole pairings or freezing the wrong mu.

For a normalized symmetric bump Y of small scale, let
`eps=E[Y^2]/2`. Formally
`E[f(c+Y)]=f(c)+eps*f''(c)+O(E[Y^4])`.
For each lambda in {1/2,2/3}, solve the SAME source
`J2=A1*M2-A2*M1=0` through first order via
`mu(lambda,eps)=mu0(lambda)+eps*mu1(lambda)+O(eps^2)`,
with mu0=(13lambda-8)/(144-54lambda). The exact jet is
`mu1=-(partial_eps J2)/(partial_mu J2)` at atomic mu0.
The original high-t *smooth* pole is
`P= B1*A2-B2*A1` with Bc=E_G[cos(16x)cos(cx)],
and `K_lambda(0,4)=4 E_G[(A1cos(2x)-A2cos(x))cos(4x)]`.
The selected source is `P_two*K_half-P_half*K_two`.

SymPy independently checks: atomic P0=3(2-lambda)/4;
atomic K0=3(lambda-2); selected zero constant term;
the moving-mu first-order selected coefficient is EXACTLY `120/13`:

```text
K_selected,high-t,smooth(0,4)
   = (120/13)*eps + O(E[Y^4]+eps^2).
```

For a nondegenerate fixed-shape shrinking even bump Y=R*Z,
eps=(R^2/2)E[Z^2], E[Y^4]=O(R^4):
strict leading coefficient positive, so high-t *smooth* q=4
kernel is positive for sufficiently small R (assuming the
exact smooth J2 root is locally realized). This is not uniform
in arbitrary even bumps lacking bounded fourth-moment
scaling, nor is it yet source-selected positive-R finite-t
Lean acceptance. A separate smooth mu existence/uniqueness
via analytic implicit-function argument, uniform finite-t
error, and actual compact bump normalization remain to be
attached before promotion to the original selected W.

Independent Gaussian *surrogate* numerical quadrature
(with J2 root solved for each lambda) gave K/eps
8.6507901 (sigma=.02), 9.0822512 (sigma=.01),
9.1934151 (sigma=.005), converging toward 120/13.
This checks the symbolic sign independently but the Gaussian
is not the original compact Mathlib bump.
Local SymPy script:
`scripts/check_rh_selected_positive_width_second_moment_20261122.py`.

**Impact:** earlier O(R) smoothing estimates alone lose the
atomic O(t^-4) sign. The new J2-preserving second-moment jet
shows that smooth high-t q=4 can instead have POSITIVE O(R^2)
leading amplitude at fixed small R. However no claim follows
about aggregate actual off-line zeta-zero source terms:
q=4 is only a normalized offset, the full signed source retains
actual multiplicities, other q lanes, far source and local slack.
**P0 missing terminal remains** `H_n+E_n+S_W<T_W(rho)`,
or the actual-zero marked-pair/prime-side local estimate
coupled to the original selected source. No RH/GRH closure.

---

## 22 November 2026 — exact moving q=4 atomic boundary layer (new, local SymPy)

**Reuse original source; no positive-width or actual-zero claim.**
Executable new source regression:
`scripts/check_rh_selected_atomic_q4_boundary_layer_20261122.py`
(committed on draft #1533). With original finite-t atomic pole determinant,
u=pi/t, physical a=beta-1/2, and moving normalized ordinate
q=4+z*u, exact symbolic Taylor algebra yields

```text
K_t,atom(a,4+z*u)
 = (5/1404)*[4096-65536*a^4+1536*pi^2*a^2*z^2-pi^4*z^4]*u^4
   + O(u^5).
```

Coefficients u^0,u^1,u^2,u^3 vanish identically. The z=0
specialization recovers the previously proved
(5120/351)*(1-16*a^4)*u^4. At fixed |a|<1/2, the leading
coefficient is strictly positive exactly when

```text
|z| < (8/pi)*sqrt(12*a^2+sqrt(1+128*a^4)).
```

Because the source q=16*(gamma-t)/t, its moving centre q=4
means gamma=5*t/4, and its *leading-coefficient* ordinate half-width is

```text
|gamma-5*t/4| < (1/2)*sqrt(12*a^2+sqrt(1+128*a^4)).
```

In particular a=0 has limiting half-width 1/2 in gamma.
This is a fixed-physical-width boundary layer with vanishing
kernel amplitude O(t^-4), not a uniform signed-margin estimate.
At z on the root, the leading coefficient is zero and this
calculation supplies **no sign**. The strict leading sign for
each fixed (a,z) strictly inside/outside its boundary holds only
for sufficiently high t, and the result is not uniform up to
|a|=1/2 or the moving z boundary.

The actual selected W has positive bump radius R and non-atomic
mu parameters. No estimate here promotes the atomic sign to W.
The relevant off-ordinate zeros must be actual zeta zeros with
multiplicity and the same t-dependent target selection;
the presence of zeros in the indicated ordinate band is not
proved or assumed. Even if present, this positive local lobe
does not prove failure or success of the aggregate signed payment
H_n+E_n+S_W<T_W(rho). Retain the complete far-source and local
slack. **Missing analytic leaf unchanged:** actual-zero
localized marked-pair/prime-side sign bound plus coupling
to the original finite signed source.

---

# RH R2/G3 ↔ Agda BIDI: reverse-solved exact remaining lemmas (22 November 2026)

## 22 November 2026 — exact original selected-atom sign bifurcation and marked-pair BIDI

### Source-first geometry, NOT a same-object positive-width witness

New original-source mathematical test is in
`scripts/check_rh_selected_finite_t_atomic_sign_20261122.py`
(commits `964db866` / `ed54cef3`; readback blob
`af78e6365b55b194bc23d6dd5efb14ad979f580b`).
Local SymPy **1.14.0** and Python byte-identical Git blob both checked.
Original Lean `main` sources reread:

- `Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean`
  blob `f2f49ccb889e948a73a6724ce9ce1a59e36a24c1`:
  exact `μ_0(λ)=(13λ−8)/(144−54λ)`, J2=0 and signed J4.
- `Synthesis/RiemannProjectiveQuarticFourWindowAtomicPoleSign.lean`
  blob `64584ceecb34770af0bb547249cd904d4d93706e`:
  high-`t` `P∞(λ)=3(2−λ)/4` and exact **finite-`t`** atomic
  pole determinant.
- `Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean`
  blob `60cc239d3968e25b8a42cebc18bf4744907facd3`:
  literal normalized pole weight
  `cosh(8v/t)cos(16v)cos(cv)` at c=1,2 and exact
  determinant `P_t=B1 A2−B2 A1`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`
  blob `16110e433efd16379c6b93bdc13420036b1d6411`
  and `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
  blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`:
  the **source-defined** signed profile is
  `P_{2/3} P_{G,1/2} − P_{1/2}P_{G,2/3}`,
  with `P_G(v)=4G(v)(A1 cos(2v)−A2 cos v)`.
  The exact Lean selected W uses **positive** bump radius `R>0`;
  these calculations concern its **R→0 atomic source model** only.

**A previously unrecorded global identity for the high-`t` atomic BASE.**
At `λ=1/2,2/3`, `μ_0(1/2)=−1/78`,
`μ_0(2/3)=1/162`, atomic centres `0,π/3,π/2,π`,
weights `(1,−1,λ,μ_0)`,
`A1=1/2−μ_0`, `A2=3/2−λ+μ_0`.
With `α` as **independently normalized horizontal** displacement,
the *high-pole-limit atomic* signed Fourier/cosh kernel is exactly
```text
K∞(α,q)
  = (160/351)cos(πq/2)cosh(πα/2)
    −(40/351)cos(πq)cosh(πα)−40/117.
K∞(0,q) = −(80/351)(1−cos(πq/2))² <= 0,
equality precisely q in 4*Z.
```
Thus the entire BASE atom is nonpositive—not merely integer samples.
Nevertheless, put `h=cosh(πα/2)>1`,
`c=cos(πq/2)`, and `c*=h/(2h²−1)∈(0,1)`.
The sign function is a *concave quadratic* in c,
with exact values
```text
K∞(α,4k)=−(80/351)(h−1)² < 0
K∞(α,q with c=c*)=
    (160/351)(h²−1)²/(2h²−1) > 0.
```
Both horizontal `±α` sides have the **same** sign.
The `α>0` positive lobe is not a finite-`t` selected W or an
actual-ζ-zero witness: when physical `a=β−1/2` is fixed and
`t→∞`, `α=16a/t→0`.

**New exact FINITE-`t` atomic result; retains source pole correction.**
Use `u=π/t`, `a=β−1/2`, physical normalized
`α=16a/t`, and
```text
h1=cosh(8u/3), h2=cosh(4u), h3=cosh(8u)
B1(λ)=1+h1/4−μ_0(λ)h3
B2(λ)=1−h1/4−λh2+μ_0(λ)h3
P_t(λ)=B1(λ)(3/2−λ+μ_0(λ))
        −B2(λ)(1/2−μ_0(λ)).
```
Insert `P_t(2/3),P_t(1/2)` into the **same**
atomic four-centre signed profile and cosh/cos Fourier response.
SymPy exact Taylor coefficient collection gives
```text
K_{t,atom}(a,4)
  = [5120/351*(1−16a^4)]*(π/t)^4 + O(t^−6)
K_{t,atom}(a,1) = −80/351 + O(t^−2).
K_{t,atom}(a,0) = −81920/351*a^4*(π/t)^4+O(t^−6).
```
In particular, **for every fixed** `|a|<1/2`,
there is a sufficiently large `t` with
`K_{t,atom}(a,4)>0` but `K_{t,atom}(a,1)<0`.
This is a mathematical asymptotic existence conclusion
from an **exact strictly positive fourth-order coefficient**;
it is NOT a claim of uniformly positive `q=4` over all `t≥200`
or uniformity in `a` up to `±1/2`.
At `a=1/4`, the exact `(π/t)^4` coefficient is
`1600/117`. Numerically evaluated **untruncated**
source pole cosh formula at `t=200,400,1000,10000`
and `a=0,1/16,1/4,49/100`: **16/16**
positive `q=4` / negative `q=1` pairs passed
at 55-digit precision; numerical signs are
**stress tests**, not certified interval enclosures.

**Why this matters to P0:** The original signed
`literalOffOrdSource(σ)` equals
`mult(σ)/(t/16)^2*K_W((β−1/2)/(t/16),
(γ−t)/(t/16))`, with actual zero multiplicity.
The atomic sign-change test prohibits replacing the
signed literal sum by a *universal atom-level
pointwise nonpositive assertion* or using the
`α=0` square as its full kernel.
It does **not** say that any actual ζ-zero
occupies a favourable or adverse toy offset.
Since the source **positive** atomic q=4
margin is `O(t^-4)`, an undifferentiated
fixed-width smoothing error `O(R)`
cannot certify that sign for arbitrarily
large t (for fixed R>0, an upper error
bound of size `C R` eventually exceeds
the `t^-4` margin). A sharper
moment-sensitive smoothing comparison or
a different **signed aggregate** argument
is required if this atomic sign is used.
This is a *limitation of that bounding
method*, not a no-go for all positive-R W.

### Original Agda marked-pair producer recovered in BIDI audit

Additional exact Agda `master` source reread:
`DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda`
blob `703d721bfd3625e31b1cf74f15d3efdb060e99ad`,
which records a **PAID**
target/reflection fourth-angular reconstruction:
```text
P2(x,d)=x²−d², P4(x,d)=x⁴−6x²d²+d⁴
P4(x,d)=[P4(x−A,d)+P4(x+A,d)]/2
       −3 A² [P2(x−A,d)+P2(x+A,d)]
       +5 A⁴.
```
Source status already has the 0/2/4 even-marked
operator **PAID**, but the localized
one-centre marked-pair producer, prime-side
sign/estimate, target-centred fourth angular
bias and coupling to far source are **OPEN**.
`RiemannQuarticSignedPoleFrontierExact.agda`
blob `ad96304383e60526bbbede5e12ddf7d0799412f7`
already owns the historical G1/G3 carrier and
compiled fourth-Lipschitz/band; do not rebuild it.

Exact SymPy BIDI identity PASS. Finite *synthetic*
countermodels have **equal M0=4 and M2=4**
but different `M4=4` versus `M4=8`:
```text
d=(-1,-1,1,1)    => M4=4
d=(-√2,0,0,√2)   => M4=8.
```
The chosen fourth-moment comparison to
`6` has opposite signs. These are **not**
actual ζ-zero configurations; they prove only
that count/second moment cannot determine the
fourth marked quantity from those inputs
alone, and confirm why the existing Agda
fourth-marked producer is not discharged by
the RvM count bound.

### Exact updated proof-search frontier — no extra API

1. **Main Lean R2 signed terminal:**
   for every hypothetical high off-line
   actual ζ `ρ`, preserve original positive-width
   `W`, `t/16`, multiplicities,
   `H_n`, `E_n`, `S_W` and
   `T_W(ρ)`. **OPEN:** prove a strict
   `H_n+E_n+S_W<T_W(ρ)` for some
   true finite half-open window, or the
   sufficient source-sharpened inequality
   `B_n^sharp+S_W≤T_W(ρ)−ε`.
   The atomic sign algebra does NOT produce
   this certificate.
2. **Existing BIDI marked-pair alternative:**
   use the already-proved 0/2/4 even-marked
   identity to translate the remaining
   fourth-order target into an **actual ζ**
   localized marked-pair/prime-side
   quantitative signed estimate, retaining
   actual `μ` background and far coupling.
   This is a genuine **analytic leaf**, not
   another abstract marked-fourth lemma.
3. **Agda original independent high route:**
   the full literal balance-free
   `literalNear + far + Γ < ClusterResponse`
   for each high off-line case, with
   downstream balance attachment and
   low/located source. No presumed Lean
   `W` ⇔ Agda `G2` equality without
   a genuine same-zero/test/scalar weld.
4. **Source trust**: exact Git blob and SymPy
   assertions passed; **no** Agda or Lean
   kernel, no external all-character kernel
   acceptance and no RH/GRH theorem.

---

**Controlling roadmap**: `Docs/roadmaps/AlpogeGRHGeometricTransport20261121.md`.
**Native detailed owner**: `Docs/roadmaps/ClayRHR2ExplicitA160SelectedWRemainingLemmas20261117.md`.
**Mathematical regression**: `scripts/check_rh_bidi_reverse_terminal_20261122.py`.
**Execution policy**: local SymPy 1.14; **no Lean/Agda kernel or GitHub CI run**.

The source-first audit was run in both directions: (1) original terminal → literal necessary scalar inequality → genuine original zero producers; (2) original selected-W/source machinery and Agda producer ports → their actual consumers. It is a dependency audit, not a new RH/GRH proof or an assertion that two response functions with similar names are identical.

## End A — Lean actual selected-W, exactly reverse-solved

Original owners on `chboishabba/dashi_lean4/main`:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean` (blob `f120fe4f8dcf9c01c81c7856986cfec693921a95`): `completedSignedResidual_eq_jointPairSource` and the source-derived constant-density origin/mu-variation factorization.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` (blob `fece9d70499d6e324a849ba4bf7c62870ed3d82b`): `canonicalSignedHighResidual_eq_completed_sub_localHalf`, `canonicalLocalBudgetSlack_nonneg` and **`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`**. The full post-sixth endpoint is **not** the weaker G3 completed residual inequality.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean` (blob `2fb66d2e7c4345673e1dda82e67823bf2d7e0481`): the same literal off-ordinate finite source, cone/good/far partition, exact sharpened budget, `UniformSharpenedSignedCompensationGap`, original old→sharpened implication, and cofinal tsum. Existing sharpened source was missed by the prior roadmap and MUST be reused.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleAbel.lean` (blob `556190b96b85b44ffdb5dbeb3b0b1d28a4f8d0e9`): `centeredZeroFinset t n` means **exactly** `t-n < Im ρ ≤ t+n`, and its increasing cofinality is theorem-written.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean` (blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`): literal same-selected-W off-ordinate term ↔ original weighted cosh/cos kernel with multiplicity and `t/16` scaling; quartic source geometry and adverse phases.

For fixed true selected `W : QuarticFourSignedPolePair t`, target `ρ : Zeros` with `Im ρ=t` and `heightOf ρ ≠ 0`, write

```text
H  := ∑' σ : (SameOrd t)^c, W.signedLiteralPairSourceTerm σ
I  := ∫ τ, W.signedOrdinateTest τ * Zeta23.mu τ
d  := W.combinedZeroHeightDefect ρ
S  := W.canonicalLocalBudgetSlack (quarticSignedPoleCanonicalV4Error CV t) ≥ 0
T  := 4*d + I
Hn := W.literalOffOrdExactAt n  -- original (t-n,t+n] finset
```

Original Lean has `W.completedSignedResidual = (H-I)/2`, and the post-sixth endpoint is **exactly**
```text
W.PostSixthCanonicalSignedHighCut ρ EV
    ↔ (H-I)/2 + S/2 < 2*d
    ↔ H + S < T.
```

This scalar equivalence was tested with SymPy symbolically and **108/108** exact substitutions. **Counterexample to lost slack**: `H=3,I=0,d=1,S=2` has `(H-I)/2<2d` but `(H-I)/2+S/2 ≥2d`. So the earlier `UniformSignedCompensationGap ρ` or the already-owned sharper `UniformSharpenedSignedCompensationGap ρ` is **not automatically enough for the final post-sixth inequality** unless its margin also absorbs `S`. Do not assert that G3's completed-only compiler proves the actual terminal.

### BIDI finite signed certificate: an exact alternative to a stronger global gap

Suppose the already source-grounded absolute two-sided tail certificate supplies `E_n≥0`, `|H-Hn|≤E_n` for all `n≥ceil(t+7)`, and `E_n→0` for each fixed `t,W`. The existing R2 roadmap supplies the actual-ζ count donor and explicit bound
```text
En=5*C_N*(t/16)^2*Dstar(R)*[
 log(2*n)/n^4 + log(2*n)/(3*n^3) + 1/(9*n^3)]
```
with original multiplicity and negative-height conjugation. `C_N` exists by original Lean theorem; `Dstar(R)` is symbolic finite if the original fixed-width witness is paid, not presently an effective decimal constant.

Then **exact mathematical equivalence at fixed `t,W,ρ`**:
```text
H+S<T
  ↔ ∃ n≥ceil(t+7), Hn+En+S<T.
```
Forward: set `g=T-H-S>0`; use `En→0` to find `En<g/2`, then `Hn+En+S≤H+2En+S<T`. Backward: `H≤Hn+En`. This is a strict-sign, **same-zero actual-source** finite certificate with all original sign information retained. It is an equivalence **conditional on the cited analytic tail bound**, NOT an algorithm that enumerates all actual zeros rigorously or an unconditional signed inequality.

Another sufficient (but **not necessary**) old-to-new route is the already-owned sharpened budget `Bn=W.literalSharpenedJointBudgetAt η n`, with `Hn≤Bn`: prove eventually `Bn+S≤T-ε` for some `ε>0`; the cofinal limit gives `H+S<T`. The bare `Bn≤T-ε` only proves the completed G3 inequality and may miss `S`.

Exact finite signed negative controls in SymPy:
- cone exact source `x=max(x,0)-max(-x,0)`; the source's `literalConeGainAt` retains `max(-x,0)`. Existing `literalSharpenedJointBudgetAt_le_jointBudgetAt` explicitly states sharpened ≤ unsharpened; **the reverse implication is false**.
- good-lane signed quartic plus remainder: `p+r ≤ p+|r|` for `p≤0` but converse can be strict. Even the sharpened budget may lose negative good remainder.
- original selected atomic `μ(λ)=(13λ-8)/(144-54λ)` gives `μ(1/2)=-1/78` and `μ(2/3)=1/162`; exact `J₂=0`, negative `J₄`, and selected high-`t` atomic kernel `K(0,1)=-80/351`, `K(0,2)=-320/351`, `K(0,4)=0`. These are original **atomic-limit** signals, NOT a smoothed selected W nor actual ζ-zero observations. Absolute values destroy legitimately negative far-source contributions.
- finite scalar compensation ε per `(t,W,ρ)` does NOT provide a global ε across those parameters. `ε_m=1/(m+1)>0` has infimum zero.

## End B — Agda preferred RH consumer and its BIDI producers

Original `chboishabba/dashi_agda/master` files **actually read**, not inferred from GitHub search counts:

- `DASHI/Analysis/RiemannG2ClayTerminalBishopLocatedExact.agda` (blob `a3b647d20edb8bdd4716bd7b961587af1c7f1406`): preferred low-side terminal requires same original Bishop-analytic carrier, located height split, published same-substrate low criticality, Bishop half-line characterization, and **high producer**. Its status says required inputs are not jointly inhabited.
- `DASHI/Analysis/RiemannG2UniformCertifiedHighOffLineProducerExact.agda` (blob `ac935ae2f2a8f86cb8777e6a670d724a05e2c2a0`): for **every high off-line zero** one same-case certified Off core, same-taper Gamma core, original representation attachments and completion. A single finite certificate is not the uniform high theorem.
- `DASHI/Analysis/RiemannG2UniformLiteralPhaseHighProducerExact.agda` (blob `4b49f6a00223881e933d230fdff747c7133beefa`): an even shorter alternative **per-zero** consumer: balance-free context + literal near model + `literalNear + far + Gamma < ClusterResponse`; its final balance is a **separate downstream attachment** and cannot be used to prove the independent analytic margin.
- `DASHI/Analysis/RiemannG2ZeroSideHMBypassBidiExact.agda` (blob `477a1e9adc63d8067381fc50cd8e467905393efe`): `H_X` → `H_T` and literal target-window+same-object attachment → `H_W` already bypass the historical `H_M` detour. The window same-object weld and finite signed near evaluation remain work.
- `DASHI/Analysis/RiemannG2HASingleSourceProducerBidiExact.agda` (blob `401be49e5e8d3b7580b9bc9f0f1e47c2ba3df351`): six math coordinates of `H_A` are projections of **one dependent source-native `SourceNativePhiHatModulation` object and indexed proof**; actual producer recovery/provenance remain open, not six new infrastructures.
- `DASHI/Analysis/RiemannG2ExistingScalarDonorInventoryExact.agda` (blob `911027c04517abbd984e4f226b3f03c93603bfb2`) and `RiemannG2ScalarDonorToPostBalanceBidiExact.agda` (blob `62b587249ac569a7c8d48c5afafe67c2dccb82a1`): reuse actual Riemann–Siegel/explicit-formula/reflection candidates but **none currently inhabits** the precise target-centred cancellation donor; downstream balance break and strict comparison are distinct.
- `DASHI/Analysis/RiemannG2FinalCutIntrospectionExact.agda` (blob `d3f78c8e973c3fe89e714354471f87d77277d679`): actual high G2 scalar leaf and finite-near same-object path remain fail-closed; no representation, balance or visualization can pay the actual strict margin.

**Crucial interoperability non-equivalence:** the Lean selected `W` signed-pole/zero-weighted `H+S<T` theorem and the Agda literal target-window `literalNear+far+Gamma<ClusterResponse` are **different stated consumers**. Their correspondence is not established by both using ζ, cosh, Fourier or the word “margin”. To transport a Lean finite signed certificate into Agda, the minimum independent **same-object identification** must prove (a) the exact actual zero/ordinate/multiplicity correspondence; (b) the same physical test/taper/window and normalization; (c) the exact Lean full terminal residual, local slack and source target equal the Agda final scalar under a common ordered-real semantics; (d) the per-high-off-line quantifiers and the separately owned balance attachment. No current examined source provides that entire weld. Alternatively, work **directly in the Agda literal consumer** without forcing the Lean quartic witness to be its producer.

## Exactly remaining theorem leaves, by owner

| Gate | Exact target | Status |
|---|---|---|
| R2-F0 | `UniformQuarticFourPoleDeterminantCompilerTarget`, from the explicit t-uniform radius `η₀/[22(83/30)19cosh1]` | source mathematics/SymPy PASS; native proof term still **OPEN** |
| R2-F1 | Source selected `W` with uniform quantitative band, signed sixth moment, local slack, literal zero carrier for every target `t,ρ` | conditional witness/consumers exist; uniform per-zero strong property **OPEN** |
| R2-F2 | Actual selected `H_n` **and** source `E_n` in the correct half-open window with effective error certificate | original analytic count/summability donors PAID; exact finite signed values and effective (b_j) **OPEN** |
| R2-S0 | **Full** `H_n+E_n+S_W<T_W(ρ)` for at least one admissible (n) per target, or equivalently the infinite `H+S<T` | **OPEN; strict-sign mathematical leaf**, not proved by absolute tail |
| R2-S1 | Alternative eventually **sharpened** budget `B_n^{sharp}+S_W≤T_W(ρ)-ε` with `ε>0` (per fixed target) | existing sharper cone/good/far algebra PAID; signed inequality **OPEN** |
| Agda-A0 | Recover actual `H_A` single dependent source with proven original function/phase/Weil action and provenance | conditional compiler PAID; concrete source producer/receipt **OPEN** |
| Agda-A1 | Same literal target-window attachment, finite signed-near payment or direct balance-free cluster margin, same-case sharp Gamma and final independent balance | conditional compilers PAID, analytic payment **OPEN** |
| Agda-A2 | One `UniformLiteralPhaseHighProducer` or `UniformCertifiedHighOffLineProducer` **for every high off-line zero**, plus Bishop same-substrate low/located consumers | **OPEN; one finite numerical case insufficient** |
| Cross-T | If claiming Lean-W→Agda-G2 reuse, prove zero/weight/scalar/quantifier identity (not name or generic ζ equivalence) | **OPEN; optional if using independent routes** |
| External-E | Independently run pinned original all-character Lean v4.33.1 kernel and `#print axioms`; compatible root trust admission | **OPEN here; source declarations not proof receipts** |

## Local audit acceptance and attribution

Local SymPy 1.14.0 run on `/mnt/data/check_rh_bidi_reverse_terminal_20261122.py`; its **exact Git blob** agrees with the committed GitHub file `scripts/check_rh_bidi_reverse_terminal_20261122.py`, blob `6eb3222e13d178ccc855f6ae24f1641221bb79d8`. `py_compile` PASS. **108/108 exact terminal substitutions**, sharpened/unsharpened cone counterexamples, true original rational atomic sign geometry, fixed-varying-`ε` no-go, and finite-tail BIDI examples PASS. The earlier existing `rh_uniform_source_audit_20261122.py` was rerun locally: original **256 determinant corners and 12,010 pole-weight derivative values** plus symbolic `t`-varying log-tail PASS. The independently sourced fourth-derivative/zero count is a theorem claim in existing Lean source (not locally kernel replayed). No direct empirical actual-zero numerical census, theorem of RH/GRH or peer-review implied.

**High-alpha next**: attack R2-S0 via **one literal same-source finite signed-near + certified physical tail** and compare it with the *full* terminal `T-S` (or prove R2-S1 via the existing sharpened cone budget), not the weaker `T`. In parallel: R2-F0 original uniform determinant local SymPy math → compatible Lean kernel only when explicitly wanted; Agda-A1 may work independently, and external-E trust is separately gated. Update these two existing roadmaps with every new mathematical receipt.
