# Paper 3 Draft: Yang-Mills Mass-Gap Reduction from Finite Carrier to Continuum Transfer

Date: `2026-06-09`
Status: live analytic manuscript draft; Clay-facing; non-promoting

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

> **Theorem 1.1 (reduction to continuum transfer and reconstruction).** Assume
> the finite carrier Hamiltonians on the selected nonabelian lattice family are
> self-adjoint with an explicit lower spectral gap, admit domination by a
> comparison semigroup with a uniform finite spectral margin, and satisfy a
> depth-to-continuum transfer principle preserving that margin in the physical
> scaling limit. If the limiting Euclidean theory satisfies reflection
> positivity and the Osterwalder-Schrader reconstruction hypotheses, then the
> reconstructed continuum theory has a positive mass gap. The remaining Clay
> frontier is therefore concentrated in the transfer and reconstruction
> interfaces rather than in the existence of isolated finite-carrier margins.

This is the honest current target. The draft can state a finite-to-continuum
assembly route sharply; it cannot claim that the route has already been fully
discharged.

## 2. Finite nonabelian carrier and operator setup

The finite starting point is a selected family of nonabelian carriers equipped
with curvature, Wilson-action bookkeeping, and a transfer or Hamiltonian
operator at each depth. The older finite geometry draft supplies the structural
language: Lie brackets, curvature witnesses, and selected finite non-flat
surfaces. In the present manuscript these are used only to justify the
existence and domain of the operator family `H_N`.

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

This is the load-bearing frontier. The finite margins of Sections 3-4 do not
solve the Clay problem unless they survive the scaling limit. The transfer step
therefore needs two ingredients:

1. a compactness or Mosco-type passage from the finite carrier family to a
   continuum candidate theory;
2. a no-spectral-pollution statement showing that the limiting positive-energy
   spectrum still stays above a strictly positive threshold.

The current draft should state this as a separate theorem interface rather than
burying it inside motivational prose. The fixed-lattice character bound weakens
as `beta` grows, so it cannot by itself produce a continuum mass gap. The
finite uniform margin must be paired with a scaling argument that converts
lattice units into a physical positive mass.

## 6. Reflection positivity and OS/Wightman reconstruction

Once a Euclidean continuum candidate has been obtained with a preserved gap
margin, the next step is reflection positivity. The role of this section is to
bridge the transfer result to the Osterwalder-Schrader reconstruction theorem:
the Euclidean Schwinger functions or transfer data must satisfy the positivity,
symmetry, and regularity hypotheses needed to reconstruct a Hilbert space, a
vacuum vector, and a positive self-adjoint Hamiltonian.

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

Combining Sections 3-6 yields the manuscript's final assembly:

1. finite operators are self-adjoint and gapped;
2. domination upgrades those gaps to a uniform finite margin;
3. continuum transfer preserves the margin in the scaling limit;
4. reflection positivity and OS reconstruction convert the Euclidean data into
   a relativistic Hilbert-space theory with positive Hamiltonian;
5. the positive Hamiltonian margin becomes a mass gap.

This is a coherent Clay-facing narrative, but it remains a reduction narrative.
The present paper does not claim that the continuum transfer theorem has been
proved, that the OS hypotheses are fully discharged for the constructed limit,
or that the Clay Yang-Mills problem is solved.

## Appendix A. Claim boundary table

| Proved in this paper | Assumed externally with citation | Explicitly left open |
| --- | --- | --- |
| The finite-to-continuum mass-gap route is canonically organized as self-adjointness -> domination -> uniform finite margin -> continuum transfer -> RP -> OS/Wightman -> assembly. | Osterwalder-Schrader reconstruction, standard Wightman consequences, and the continuum gauge-theory authority represented by Seiler and related sources. | The actual depth-to-continuum transfer theorem, a proved continuum interacting Yang-Mills construction with all hypotheses verified, and any claim that the Clay mass-gap problem is solved. |
