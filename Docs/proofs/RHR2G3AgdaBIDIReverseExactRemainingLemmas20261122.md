# RH R2/G3 ↔ Agda BIDI: reverse-solved exact remaining lemmas (22 November 2026)

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
