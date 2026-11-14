# RH A2/G3: Fourier-curvature obstruction, correct paired expansion, and actual-zero boundary

**14 November 2026; owner Agda #1499 and Lean #50/#108.**

This corrects the second attached proposal without discarding its useful
spectral sign argument. It establishes a precise **generic method
obstruction**, NOT the original selected-witness A2 no-go, G3, or RH.

## 1. The Taylor expansion must use the actual horizontal pairing

Let `F(z)=∫_ℝ W(x)e^{zx} dx`, initially with `W∈C_c^∞(ℝ)`
and real horizontal `a`, `z=iγ`. For one horizontal translate,

`Re[F(z+a)-F(z)] = a Re F'(z) + a²/2 Re F''(z)
                   + a³/6 Re F'''(z) + O(a⁴)`.

**The linear and cubic terms do not vanish merely because W is even.**
The claimed even-order-only formula for the *single* translate is
unjustified. Under the actual symmetric pair `a,-a` one has

`Re[(F(z+a)+F(z-a))/2 - F(z)]
   = a²/2 Re F''(z) + R_4(a,z)`,

where for `|a|≤A`,

`|R_4(a,iγ)| ≤ |a|⁴/24 ∫ |x|⁴|W(x)|e^{A|x|} dx`.

Proof: integrate the even Taylor remainder for each `e^{±ax}`
pointwise under the compactly supported integral, or use the fourth
derivative bound on the horizontal segment. This estimate is uniform
in `γ` and is a **mathematical lemma**, not yet the original A2 source
Taylor and normalization identity.

The actual A2 source must identify its selected zero quartet, pole
weights and signed kernel before using this paired formula.

## 2. A valid generic sign-change theorem

Assume `W` is real, even, smooth, compactly supported and `W≥0`,
nonzero away from the origin. Set

`G(γ)=Re F''(iγ)=∫ x²W(x) cos(γx) dx`.

Then:

- `G(0)=∫x²W(x)dx>0`.
- `G` is continuous and absolutely integrable (indeed rapidly
  decreasing because `x²W(x)` is smooth and compactly supported).
- Fourier inversion gives `∫_ℝ G(γ)dγ=2π(x²W(x))|_{x=0}=0`.
- Therefore `G(γ)<0` for **some** real `γ`:
  otherwise a continuous nonnegative integrable function positive
  near 0 would have positive integral.

Thus `Re F''(iγ)>0 for every real γ` is impossible for this
class of W. This is the correct rigorous scope of the Fourier
sign-change obstruction.

More constructively, choose any nonzero even `C_c^∞` bump
`b≥0` supported in `[-1/8,1/8]`, and put
`W(x)=b(x-1)+b(x+1)`. Then `G(0)>0` and `G(π)<0`, since
`cos(πx)<0` throughout both supports. This example makes
the negative frequency explicit but is **not** the selected
original A2 witness or a zeta-zero configuration.

**Important correction:** `F''(iγ)` means the *complex horizontal*
derivative of `F`, while
`d²/dγ² F(iγ)=-F''(iγ)` is the second Fourier-frequency derivative.
The latter differs by a sign; neither can be silently substituted
for the exact original source `CompensationTarget`.

## 3. What this does *not* prove

It is false that failure of global spectral-curvature positivity
automatically implies

`LocalPositiveDebt(W)+FarExact(W,ρ) ≥
  CompensationTarget(W,ρ)+LocalMuGain(W)`

for the **selected original zeta zeros**. Negative `G(γ)`
somewhere on the continuous real axis neither places an actual
zeta zero there nor defeats positive compensation elsewhere;
the far exact sum and smooth-measure gain also matter.
Global curvature positivity is a possible strong *sufficient*
route, not a demonstrated *necessary* condition for A2.

Consequently the attachment's claimed closure of
`originalSelectedA2CompensationNoGo` is **not valid**.
This is a no-go for the stronger all-frequency curvature ansatz,
not a no-go for the selected A2 or for RH.

## 4. Valid general far-frequency estimate, pending original carrier

For `W∈C_c^m` and `|Re z|≤1/2`, repeated integration by parts gives

`|F(a+iγ)| ≤ C_m(W)|γ|^{-m}`, `|γ|≥1`, where

`C_m(W)=Σ_{j=0}^m binom(m,j)(1/2)^(m-j)
           ∫ e^{|x|/2}|W^(j)(x)|dx`.

Combined with the true zeta-zero dyadic count
`N(2T)-N(T)=O(T log(T+2))`, it bounds a shell of *unweighted*
transform values by `O(C_m(W) 2^{-(m-1)k}(k+1))`.
For `m≥3` this is summable. If the repository's
`FarExact` contains extra zero-dependent weights or renormalized
subtractions, they must be transported and bounded individually;
the display is not itself an inhabited
`originalA2FarExactZeroShellBound`.

## 5. Decisive actual-source maximum cut

1. Fetch the literal selected `QuarticFourSignedPolePair` witness and
   verify real evenness, support and weighted derivative norms on the
   selected source (not arbitrary W).
2. Prove `selectedOriginalWitnessFourthLipschitzBound` against the
   already kernel-facing exact threshold in Lean #50.
3. Prove same-carrier quartet Taylor pairing, signed far-horizontal
   curvature and dyadic shell bound with **actual zeta zeros**.
4. Decide the *complete* source inequality with `LocalPositiveDebt`,
   `FarExact`, `CompensationTarget`, `LocalMuGain` together.
   A true selected-source reverse inequality would close the A2
   **method** only. A genuine strict bound would advance G3; neither
   may be inferred solely from the generic curvature no-go.

Status: generic mathematical sign-change and paired remainder derived;
original selected A2/G3 C gate **OPEN**. No Lean/Agda kernel receipt for
new source lemmas here.
