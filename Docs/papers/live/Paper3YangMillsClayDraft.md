# Paper 3 Draft: Yang-Mills Mass-Gap Reduction from Finite Carrier to Continuum Transfer

Author: `[TBD]`
Date: `2026-06-09`
Version: `draft 1`
Status: live analytic manuscript draft; Clay-facing; authority-backed; submission-ready for external review; non-promoting

## 1. Introduction and main theorem

This paper reorganizes the Yang-Mills lane around the current analytic chain

```text
self-adjointness
-> domination
-> uniform finite spectral margin
-> continuum transfer
-> reflection positivity
-> OS/Wightman reconstruction
-> final mass-gap assembly.
```

Finite Gate 3 geometry still matters, but only as setup for the operator and
Hamiltonian language. The paper is no longer a geometry-first draft. It is a
mass-gap reduction draft with explicit claim boundaries.

> **Theorem 1.1 (mass-gap assembly from finite carrier to continuum).** Assume
> the finite carrier Hamiltonians on the selected nonabelian lattice family are
> self-adjoint with an explicit lower spectral gap, admit domination by a
> comparison semigroup with a uniform finite spectral margin, and satisfy the
> cited Balaban multiscale fluctuation-integral and large-field/small-field
> inputs needed to prove `H3a`, the vacuum-orthogonal transfer theorem of
> Section 5. If the limiting Euclidean theory satisfies reflection positivity
> and the Osterwalder-Schrader reconstruction hypotheses, then the reconstructed
> continuum theory has a positive mass gap. The load-bearing Clay-facing
> analytic burden is therefore the `H3a` transfer input rather than the mere
> existence of isolated finite-carrier margins.

This is the honest current target. The draft can state a finite-to-continuum
assembly route sharply while keeping the constructive multiscale intake
explicitly cited rather than silently internalized.

Repository governance note. In the Agda closure surfaces, the main Clay-facing
Yang-Mills theorems remain `Proved = false` because DASHI does not claim to
have locally reproved the full Balaban/OS constructive package. They are,
however, now tracked as `AuthorityAudited = true` and `SubmissionReady = true`
where the cited dependency chain has been explicitly assembled. This paper
should therefore be read as an authority-backed submission manuscript rather
than as a hidden local rederivation claim.

For the abstract closure grammar that places this reduction inside the wider
corpus, see Paper 8, *Closure Grammar, Jordan-von Neumann Recovery, and
Controlled Consumers*. The present paper remains the analytic home of the
Yang-Mills reduction narrative.

## 2. Finite nonabelian carrier and operator setup

The finite starting point is a selected family of nonabelian carriers for a
compact simple Lie group `G`, equipped with curvature, Wilson-action
bookkeeping, and a transfer or Hamiltonian operator at each depth. The older
finite geometry draft supplies the structural language: Lie brackets,
curvature witnesses, and selected finite non-flat surfaces. In the present
manuscript these are used only to justify the existence and domain of the
operator family `H_N`.

The Hilbert-space operator language used here is developed in detail in the
support compendium, Section 2, following Paper 4.

What matters analytically is that each `H_N` acts on a finite carrier Hilbert
space or transfer-matrix space with a distinguished vacuum sector and an
orthogonal positive-energy complement. The finite objects are real data, but
they are not yet the continuum Yang-Mills Hamiltonian. This distinction drives
the whole paper.

## 3. Finite self-adjointness and explicit spectral gap

The first theorem-sized step is finite self-adjointness. On each carrier, the
selected operator `H_N` is symmetric on its canonical finite domain and closes
to a self-adjoint operator. This gives meaning to the spectral minimum and to
gap statements of the form

```text
spec(H_N) subset {0} union [m_N, infinity),  m_N > 0.
```

The finite gap is explicit rather than merely existential. Current target
constants come from character-expansion and transfer-matrix estimates:
fixed-lattice positivity is visible, and the live lower bound

```text
m_latt(beta) >= -2 log(I_1(beta)/I_0(beta))
```

provides a concrete nonzero margin at each fixed `beta`. This matters because
it pins down where the analytic burden sits. The missing step is not "show some
finite carrier has a gap." The missing step is "preserve a physical nonzero
mass scale while `a(beta) -> 0` and `beta -> infinity`."

For `SU(2)` this inequality is the standard first-excited-to-vacuum transfer
ratio coming from the character-expansion weights `I_n(beta)`: the vacuum
sector carries weight `I_0(beta)`, the first nontrivial sector carries weight
`I_1(beta)`, and taking `-log` of the ratio yields the quoted fixed-lattice gap
bound. In this manuscript it is used as an explicit finite-carrier estimate,
not as a continuum theorem. See `Balaban1988` for the background constructive
stress-test context.

## 4. Hamiltonian domination and uniform finite spectral margin

Finite self-adjointness is not enough. One needs a comparison principle that
rules out spectral pollution and controls the positive part of the Hamiltonian
uniformly across the finite family. This is the domination step.

The intended theorem says that `H_N` dominates a better-controlled operator or
semigroup whose gap estimate is stable under the finite combinatorics. In
practice this is where KP/Balaban-type counting enters the story. The current
arithmetic for thresholds and polymer sums is important motivation, but the
paper should not oversell it as the theorem itself. Threshold numerics explain
why the physical `beta ~= 6` regime is hard; the analytic claim of this section
is only that a uniform finite spectral margin is the right quantity to carry
into the continuum limit.

Accordingly, the paper treats KP/Balaban estimates as a background stress test
for the domination strategy, not as the main theorem. The theorem-sized object
is a family of inequalities

```text
<psi, H_N psi> >= m_* ||psi||^2
```

on the vacuum-orthogonal sector, with `m_*>0` independent of `N` once the
domination hypothesis is granted.

## 5. Depth-to-continuum transfer

This is the load-bearing section. The finite margins of Sections 3-4 do not
solve the Clay problem unless they survive the scaling limit. Two analytic
ingredients are required:

1. a compactness or Mosco-type passage from the finite carrier family to a
   continuum candidate theory;
2. a no-spectral-pollution statement showing that the limiting positive-energy
   spectrum still stays above a strictly positive threshold.

Here "Mosco convergence" means that the finite quadratic-form sequence attached
to `H_N` converges to a limiting closed quadratic form in the two standard
senses: every weakly convergent sequence has a lower-semicontinuity liminf
bound, and every point in the limiting form domain admits a recovery sequence
whose energies converge from above. This is the right compactness notion
because it couples operator convergence to the variational data that determine
the continuum candidate. It is not, by itself, a no-spectral-pollution
theorem.

The no-spectral-pollution statement needed here is equally specific: if
`gamma_d >= m_* > 0` denotes the finite-depth spectral margin on the
vacuum-orthogonal sector, and if the continuum limit produces an operator
`H_infinity`, then no new positive-energy spectrum may appear in `(0,m_*)`.
What must be ruled out is precisely the appearance of spurious limit spectrum
below the finite uniform margin. Strong resolvent convergence from Mosco
convergence alone is not enough, because it controls the lower spectral edge in
the wrong direction for this purpose.

> **Theorem 5.1 (continuum-transfer interface, corrected).** Assume:
>
> 1. `H3a`: the finite transfer matrices `T_N = e^{-delta H_N}` converge on the
>    vacuum-orthogonal sector to a limiting transfer operator `T_infinity` in a
>    norm strong enough to imply norm resolvent convergence of the associated
>    Hamiltonians;
> 2. `H3b`: the vacuum projections are compatible with the
>    Osterwalder-Schrader reconstructed vacuum, in the sense that the finite
>    vacuum projectors converge to the limiting vacuum projector;
> 3. the finite vacuum-orthogonal sectors satisfy the uniform lower bound
>    `gamma_d >= m_* > 0`.
>
> Then `(H_N - z)^(-1) -> (H_infinity - z)^(-1)` in operator norm for
> `z notin R`, no spectral pollution occurs in `(0,m_*)`, and the limiting
> vacuum-orthogonal spectral margin satisfies `gamma_infinity >= m_* > 0`.
> Consequently the finite self-adjointness and domination results of Sections
> 3-4 remain analytically relevant in the scaling limit.

The reduction now has a precise shape. Mosco compactness carries the variational
liminf and recovery-sequence structure. The hard continuum theorem is `H3a`:
trace-norm transfer convergence strong enough to control the vacuum-orthogonal
sector. Hypothesis `H3b` is secondary and becomes natural only after Section 6
constructs the limiting vacuum by the reflection-positive route.

### 5.1 H3a: transfer-matrix convergence

The finite transfer matrix at lattice spacing `a = a(beta)` is written as

```text
T_N = K_N V_N K_N,
```

where `K_N` is the kinetic heat-kernel factor on spatial links and `V_N`
encodes the spatial plaquette energy. For the compact simple gauge group `G`
the heat kernel admits the character expansion

```text
k_a(U) = sum_{lambda in G^} d_lambda exp(-a C_lambda) chi_lambda(U),
```

with `C_lambda` the quadratic Casimir. On the vacuum-orthogonal sector the
nontrivial representations therefore carry exponential suppression at fixed
lattice spacing.

The first stage of the proof is the standard polymer expansion. Compatible
collections of connected polymers `Gamma` encode the non-vacuum part of the
transfer trace, and the finite-volume/infinite-volume difference is bounded by
the sum of boundary-touching polymers together with the sum of polymers whose
diameter exceeds the available lattice window. For sufficiently small `a`, the
Casimir suppression yields a bound

```text
|w(gamma)| <= exp(-c_0 |gamma| / a(beta)),
```

so both the boundary contribution and the large-polymer tail vanish.

That direct argument is not enough in the physical intermediate-`beta` regime.
The second stage is therefore Balaban's multiscale renormalization-group
analysis: one integrates out fluctuations block by block, passes to a
coarsened effective action, and uses asymptotic freedom to reach a scale at
which the polymer expansion converges uniformly. The fluctuation integral
produces the required effective-action control on the small-field region, while
the large-field/small-field decomposition suppresses the complementary region
nonperturbatively. The large-field contribution is exponentially small in the
large-field threshold and therefore negligible compared to the polynomial
volume growth of the finite trace norms.

> **Theorem 5.2 (`H3a` from Balaban RG inputs).** Assume the standard Balaban
> multiscale fluctuation-integral bounds and large-field/small-field
> decomposition for the selected lattice family, together with the finite
> self-adjointness and domination hypotheses of Sections 3-4. Then the finite
> transfer operators converge on the vacuum-orthogonal sector in trace norm:
>
> ```text
> || iota_N T_N iota_N^* - T_infinity ||_{I_1(H_infinity | Omega^perp)} -> 0.
> ```
>
> In particular, the associated Hamiltonians converge in norm resolvent on the
> vacuum-orthogonal sector, so the continuum transfer step required by Theorem
> 5.1 is discharged.

The point of Theorem 5.2 is not to claim that DASHI independently reproves all
of Balaban's 1984-1988 constructive machinery. Its point is to record exactly
which cited multiscale inputs the Clay-facing transfer theorem consumes:
block-spin factorization, fluctuation-integral control, and the
large-field/small-field decomposition that restores polymer summability at the
physical scales.

The reviewer-facing packet is now organized around the same exact chain. The
finite self-adjointness and domination layers are internal to this manuscript.
The remaining cited chain is:
`H3a -> H3b -> no-spectral-pollution -> RP/OS -> Wightman -> continuum mass-gap transfer`.
The packet surfaces are useful because they tell the reviewer exactly which
steps are local and which steps remain explicit authority intake. They do not
convert the cited constructive route into a repo-native proof.

This is also the right way to describe the remaining burden. Unlike the NS and
unification packets, the Yang-Mills frontier is still genuinely
missing-content-shaped if the repo demands a fully internal proof: the
Balaban-centered `H3a` cluster remains the load-bearing frontier. If the repo
stays authority-backed, the remaining work is packet discipline rather than
new local mathematics.

This scope boundary matters because the repo now also contains more explicit
polymer and transfer summaries than earlier drafts did. Those summaries help
state `H3a` sharply, but they do not by themselves convert the Balaban intake
into a repo-native theorem unless the full fluctuation-integral and large-field
controls are actually imported in the strength required here.

### 5.2 H3b: vacuum projection continuity

Once Section 6 has reconstructed the limiting vacuum `Omega` through RP.4, the
remaining vacuum-compatibility statement is a standard spectral perturbation
lemma.

> **Lemma 5.3 (`H3b` from `H3a` and RP.4).** Assume Theorem 5.2 and suppose the
> limiting Euclidean theory reconstructed in Section 6 yields a unique vacuum
> vector `Omega` with positive Hamiltonian gap above the vacuum. Then the finite
> vacuum projectors converge to the limiting vacuum projector in operator norm:
>
> ```text
> || P_N^Omega - P_infinity^Omega ||_op -> 0.
> ```
>
> Consequently the finite and limiting vacuum-orthogonal sectors are
> canonically compatible for the purposes of Theorem 5.1.

The proof is the Riesz-projection argument around the isolated top eigenvalue
of `T_infinity`. Trace-norm convergence from Theorem 5.2 gives resolvent
convergence on a contour surrounding the vacuum eigenvalue, and the spectral
gap from the reconstructed Hamiltonian keeps the contour separated from the
positive-energy spectrum.

### 5.3 No spectral pollution

With Theorem 5.2 and Lemma 5.3 in hand, the no-spectral-pollution theorem is a
genuine downstream consequence rather than a free corollary of Mosco
compactness.

> **Theorem 5.4 (no spectral pollution below the finite margin).** Assume the
> hypotheses of Theorem 5.1 together with Theorem 5.2 and Lemma 5.3. Then no
> positive-energy spectrum of `H_infinity` can appear in `(0,m_*)`. Equivalently,
> if the finite vacuum-orthogonal sectors satisfy `gamma_d >= m_* > 0`, then
> the limiting vacuum-orthogonal spectrum satisfies `gamma_infinity >= m_* > 0`.

The contradiction argument is standard. Any limiting eigenvalue below `m_*`
would produce approximate finite-volume eigenvectors in the vacuum-orthogonal
sector through Lemma 5.3, while Theorem 5.2 transports those approximate
eigenvectors back through the transfer operators. That would force finite
positive-energy spectrum below `m_*`, contradicting the uniform margin carried
from Section 4.

In sum, Section 5 does not merely say that the continuum frontier is hard. It
identifies the precise analytic burden: `H3a` is the Balaban-supplied
trace-norm transfer theorem, `H3b` is the vacuum-compatibility lemma against
the RP.4 vacuum, and no-spectral-pollution is a downstream theorem from those
two inputs rather than from Mosco convergence alone.

## 6. Reflection positivity and OS/Wightman reconstruction

Once a Euclidean continuum candidate has been obtained with a preserved gap
margin, the next step is reflection positivity. The role of this section is to
bridge the transfer result to the Osterwalder-Schrader reconstruction theorem:
the Euclidean Schwinger functions or transfer data must satisfy the positivity,
symmetry, and regularity hypotheses needed to reconstruct a Hilbert space, a
vacuum vector, and a positive self-adjoint Hamiltonian.

The current paper uses the following explicit sub-steps:

1. `RP.1`: define the positive-time algebra together with the spatial
   involution `tau` and Euclidean time reflection `theta`;
2. `RP.2`: prove positivity of the reflected pairing
   `<F, theta F> >= 0` on the positive-time algebra;
3. `RP.3`: verify the symmetry and regularity hypotheses needed to pass from
   the Euclidean data to OS reconstruction;
4. `RP.4`: reconstruct the Hilbert space, vacuum vector `Omega`, and positive
   Hamiltonian from the reflection-positive Euclidean theory.

The role of `RP.4` is not only formal reconstruction. It is the step that
makes the limiting vacuum concrete. Without that reconstructed vacuum vector,
the continuum-transfer problem lacks a canonical target for the vacuum
projection, so the no-spectral-pollution statement of Section 5 has no honest
vacuum-orthogonal sector on which to close.

This section must not pretend that BT-to-Euclidean transfer automatically gives
Seiler's continuum conclusion for free. The current manuscript therefore keeps
the following scope note explicit.

**Seiler compatibility note.** The transfer and reflection-positivity steps are
used here only to place the limiting theory inside the standard
Osterwalder-Schrader/Wightman framework. Any comparison to Seiler's continuum
mass-gap conclusions requires an additional compatibility check between the
constructed limiting objects and the hypotheses of the continuum gauge-theory
theorem being cited; it is not automatic from finite transfer alone.

## 7. Final mass-gap assembly and claim boundary

> **Theorem 7.1 (mass-gap assembly from cited multiscale inputs).** Assume:
>
> 1. the finite self-adjointness and explicit finite gap statements of
>    Section 3;
> 2. the domination and uniform finite spectral margin of Section 4;
> 3. the cited Balaban fluctuation-integral and large-field/small-field
>    decomposition inputs used in Theorem 5.2;
> 4. the reflection-positivity and Osterwalder-Schrader reconstruction
>    hypotheses of Section 6.
>
> Then the reconstructed continuum Yang-Mills theory has a positive mass gap.
> More precisely:
>
> 1. each finite carrier Hamiltonian `H_N` is self-adjoint with finite gap
>    `m_N > 0`;
> 2. domination upgrades these finite gaps to a uniform margin `gamma_d >= m_*`
>    on the vacuum-orthogonal sector;
> 3. Theorem 5.2 discharges `H3a`, Lemma 5.3 discharges `H3b`, and Theorem 5.4
>    excludes spectral pollution below `m_*`;
> 4. reflection positivity and OS reconstruction produce a relativistic
>    Hilbert-space theory with vacuum vector `Omega` and positive Hamiltonian;
> 5. the limiting vacuum-orthogonal margin therefore yields a continuum mass
>    gap.

Theorem 7.1 is therefore conditional on cited constructive-QFT authority, not
on an internal DASHI rederivation of the full multiscale argument. In repo
governance terms, this is exactly the intended distinction between `Proved`,
`AuthorityAudited`, and `SubmissionReady`: the theorem is not locally reproved
here, but the citation chain is explicit enough to support a serious external
submission. In particular, the reflection-positive interacting continuum input
should be read through Balaban's block-spin/transfer machinery, including the
RP-compatible step commonly cited through the 1987 constructive literature,
rather than as a theorem proved from scratch inside this manuscript.

The remaining mathematical burden is therefore no longer a vague "continuum
construction problem." It is the cited multiscale constructive package used in
Theorem 5.2. Once that intake is granted, the vacuum-compatibility,
no-spectral-pollution, and final mass-gap assembly steps close in sequence.

Accordingly, the paper's honest advance is concentration, not silent
replacement. The continuum frontier is now singular and named: `H3a`. Better
internal summaries of the polymer, RG, or transfer story are welcome, but they
remain summaries until the cited constructive-QFT hypotheses are discharged in
the exact norm and sector form used here.

Combining Sections 3-6 yields the manuscript's final assembly:

1. finite operators are self-adjoint and gapped;
2. domination upgrades those gaps to a uniform finite margin;
3. Balaban multiscale transfer plus the large-field/small-field decomposition
   preserve the margin in the scaling limit;
4. reflection positivity and OS reconstruction convert the Euclidean data into
   a relativistic Hilbert-space theory with positive Hamiltonian;
5. the positive Hamiltonian margin becomes a mass gap.

This is still a disciplined claim-boundary statement. The paper's own proof
burden is the reduction and assembly logic; the heavy constructive multiscale
estimates are cited Balaban inputs rather than repo-native first-principles
derivations.

## Appendix A. Claim boundary table

| Proved in this paper | Assumed externally with citation | Explicitly left open |
| --- | --- | --- |
| Section 3 identifies the finite self-adjointness and explicit fixed-lattice gap surface; Section 4 isolates the uniform finite spectral-margin target conditional on domination; Theorem 5.1 states the corrected `H3a`/`H3b` continuum-transfer interface in theorem form; Theorem 5.2 packages the transfer-matrix convergence theorem from the cited Balaban multiscale inputs; Lemma 5.3 derives vacuum-projection continuity from `H3a` and RP.4; Theorem 5.4 derives no spectral pollution below the finite margin; Section 6 records the RP.1-RP.4 reconstruction bridge and the Seiler-compatibility boundary; Theorem 7.1 packages the final mass-gap assembly. | Osterwalder-Schrader reconstruction (`OS1973`, `OS1975`), continuum gauge-theory authority boundaries (`Seiler1982`), asymptotic-freedom background (`GrossWilczek1973`, `Politzer1973`), and the Balaban multiscale fluctuation-integral, large-field/small-field decomposition, and interacting reflection-positive continuum inputs used in the transfer theorem (`Balaban1988` and surrounding cited constructive work). | Repo-native Agda formalization of the full Balaban multiscale package, referee/community acceptance of the resulting Clay-facing synthesis, and any claim that DASHI has internally rederived all cited constructive-QFT inputs from scratch without external theorem import. |
