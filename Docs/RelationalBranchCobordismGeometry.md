# Relational Branch Cobordism Geometry

This note formalises the “pair of pants” intuition as an exact finite carrier. It complements the process-bearing PNF hyperfabric, the finite attractor-selection ledger, and the integer-pair double-/\(n\)-slit algebra.

The implementation separates three levels:

1. **branch topology:** one coarse boundary splitting into \(n\) fine boundaries;
2. **branch dynamics:** phase-sensitive recombination and pairwise interference;
3. **branch direction:** signed transport toward, orthogonal to, or away from a desired attractor.

The carrier is combinatorial. It does not claim a smooth cobordism, TQFT, Hilbert space, Born rule, or literal quantum cognition.

## 1. The finite \(1\to n\) pants object

A branching junction is represented by

\[
\mathcal P_{1\to n}
=
(c;f_1,\ldots,f_n),
\]

where \(c\) is one coarse input channel and \(f_i\) are fine output channels.

Each channel carries:

\[
(\text{proposition type},
\text{scale label},
\text{capacity},
\text{phase},
\text{open status},
\text{provenance},
\text{wave},
\text{destination basin}).
\]

The names `j-coarse` and `j-fine` denote scale levels in this relational model. They do not assert identity with the modular \(j\)-invariant.

## 2. Capacity and wave conservation are different

For a junction \(P\), define

\[
C_{\rm in}(P)=C(c),
\qquad
C_{\rm out}(P)=\sum_i C(f_i).
\]

Capacity conservation is

\[
C_{\rm out}(P)=C_{\rm in}(P).
\]

Wave recombination is

\[
\mu(P)=\sum_i \psi(f_i).
\]

Wave conservation is the separate condition

\[
\mu(P)=\psi(c).
\]

A system can conserve nominal capacity while changing phase, provenance, or the reconstructed coarse state.

The split/recombine residual is

\[
R(P)=\mu(P)-\psi(c).
\]

This residual is a finite memory defect: it records how the state after traversing the branch structure differs from the state before splitting.

The canonical phase-changing witness conserves capacity but has

\[
R(P)=(-1,1).
\]

Thus

\[
\boxed{
\text{same total capacity}
\not\Rightarrow
\text{same recombined state}.
}
\]

## 3. Composition by boundary gluing

A fine output of one junction may be replaced by another \(1\to m\) junction when their interfaces match.

The matching witness requires equality of:

- proposition type;
- capacity;
- phase;
- wave state;
- open status.

If

\[
P:c\to(f_1,\ldots,f_k,\ldots,f_n)
\]

and

\[
Q:f_k\to(g_1,\ldots,g_m),
\]

then substitution gives

\[
P\circ_kQ:
 c\to(f_1,\ldots,f_{k-1},g_1,\ldots,g_m,f_{k+1},\ldots,f_n).
\]

The canonical Agda witness composes two \(1\to2\) junctions to obtain an exact \(1\to3\) junction. It proves:

\[
N_{\rm outputs}=3,
\]

\[
C_{\rm out}=C_{\rm in}=3,
\]

and

\[
R(P\circ Q)=0.
\]

This is the finite analogue of gluing pants-like pieces into a larger branching surface.

## 4. Input alignment and attractor alignment

The attachments distinguish two geometrically different questions:

1. Does a branch faithfully continue the incoming proposition?
2. Does it move toward the desired attractor?

In a continuous model these would be measured by

\[
\cos\theta_i^{\rm in}
=
\frac{\langle p,v_i\rangle}{\|p\|\|v_i\|},
\]

and

\[
\cos\theta_i^{\rm att}
=
\frac{\langle -\nabla V_{A^*},v_i\rangle}
{\|\nabla V_{A^*}\|\|v_i\|}.
\]

The present exact carrier uses the balanced discretisation

\[
\cos\theta_i^{\rm att}
\in\{-1,0,+1\}.
\]

These values mean:

\[
+1=\text{toward},
\qquad
0=\text{orthogonal},
\qquad
-1=\text{away}.
\]

No continuous angle is inferred from the trit.

## 5. Attractor-projected amplitude

For branch wave \(\psi_i\) and alignment trit \(g_i\), define

\[
\widetilde\psi_i=g_i\psi_i.
\]

The attractor-projected resultant is

\[
\Psi_{A^*}=\sum_i\widetilde\psi_i.
\]

The coherent magnitude is

\[
I_{A^*}=\|\Psi_{A^*}\|^2.
\]

But squaring erases direction. Therefore the formalisation also retains signed flux along a fixed attractor axis \(e_{A^*}\):

\[
F_{A^*}=\langle e_{A^*},\Psi_{A^*}\rangle.
\]

Exact witnesses show:

- two aligned unit branches have \(I_{A^*}=4\) and \(F_{A^*}=+2\);
- two opposed unit branches also have \(I_{A^*}=4\), but \(F_{A^*}=-2\);
- one aligned and one opposed branch cancel to zero;
- an orthogonal branch contributes no projected flux.

Therefore

\[
\boxed{
\text{coherent magnitude alone does not determine attractor direction}.
}
\]

## 6. Exact branch marginality

For one branch \(\psi\) and the family of remaining branches \(\Psi_R\), the exact double-slit identity gives

\[
\|\psi+\Psi_R\|^2
=
\|\psi\|^2
+
\|\Psi_R\|^2
+
2\langle\psi,\Psi_R\rangle.
\]

The implementation proves the list form

\[
I(\psi::R)
=
\|\psi\|^2+I(R)
+
\sum_{\chi\in R}2\langle\psi,\chi\rangle.
\]

Closing one slit therefore removes:

1. the branch’s diagonal term;
2. every cross term connecting it to the remaining family.

So branch value is contextual:

\[
\boxed{
\Delta I_\psi
\neq
\|\psi\|^2
\quad\text{in general}.
}
\]

The same branch may add constructive mass in one family and destructive mass in another.

## 7. Pair-count complexity

For \(n\) branches, the pair relation count satisfies the recurrence

\[
P(0)=0,
\qquad
P(n+1)=n+P(n).
\]

The finite regressions compute:

\[
P(3)=3,
\qquad
P(4)=6.
\]

This is the exact recursive form of

\[
P(n)=\binom n2.
\]

Even before higher-order contextual structure is added, branch-interaction bookkeeping grows quadratically.

## 8. Which-path memory

A path marker can suppress an interference term when two histories remain distinguishable.

The finite marker relation has two states:

\[
M=\mathsf{indistinguishable}
\quad\text{or}\quad
M=\mathsf{distinguishable}.
\]

The retained cross term is

\[
I_{12}^{M}
=
\begin{cases}
2\langle\psi_1,\psi_2\rangle,
& M=\mathsf{indistinguishable},\\
0,
& M=\mathsf{distinguishable}.
\end{cases}
\]

For two in-phase unit branches:

\[
I_{\rm indistinguishable}=4,
\qquad
I_{\rm distinguishable}=2.
\]

For opposite unit branches:

\[
I_{\rm indistinguishable}=0,
\qquad
I_{\rm distinguishable}=2.
\]

Thus path separation suppresses both constructive and destructive interference.

This produces two opposite PNF errors.

### Excessive path erasure

Distinct histories are compressed as interchangeable. In the canonical in-phase witness, this creates two units of spurious constructive mass.

### Excessive path separation

Reusable common structure is stored as completely unrelated. In the same witness, this destroys two units of constructive mass.

The memory invariant is therefore:

\[
\boxed{
\text{preserve exactly the path distinctions that change future composition}.
}
\]

## 9. Trauma-sensitive path transport

A traumatic history may attach a persistent marker to a later route. The formal object records:

- historical route;
- current route;
- transported marker relation;
- whether current context was checked;
- a provenance receipt.

The carrier does not infer that:

- path difference always means trauma;
- a strong marker proves current danger;
- a present branch is automatically unsafe;
- a person has a diagnosis.

The relevant distinction remains:

\[
\Delta_e(i,j,\Gamma)
\quad\text{versus}\quad
\Delta_e(i,j),
\]

that is, context-sensitive transport versus overgeneralised transport.

## 10. Two distinct ternary geometries

The attachments identify two mathematically different three-way arrangements.

### Ordered relational geometry

For aligned, open/orthogonal, and opposed states, use

\[
0,\frac\pi2,\pi.
\]

The existing integer-pair phase carrier represents these exactly as

\[
(1,0),
(0,1),
(-1,0).
\]

Their total is

\[
(0,1),
\]

so the intensity is

\[
1.
\]

This geometry is ordered relative to an input direction and does not symmetrically cancel.

### Symmetric ternary geometry

For three structurally symmetric alternatives, use the cubic roots of unity

\[
1,\omega,\omega^2,
\qquad
\omega^2+\omega+1=0.
\]

These are represented exactly in the Eisenstein lattice

\[
\mathbb Z[\omega].
\]

The norm is

\[
N(a+b\omega)=a^2-ab+b^2.
\]

The pair-interference form is

\[
B((a,b),(c,d))
=
2ac-ad-bc+2bd.
\]

The formalisation proves the polarization identity

\[
N(x+y)=N(x)+N(y)+B(x,y).
\]

For the three roots:

\[
N(1)=N(\omega)=N(\omega^2)=1,
\]

while every pair contributes

\[
B=-1.
\]

Hence

\[
3+(-1-1-1)=0,
\]

and

\[
\boxed{
1+\omega+\omega^2=0
}
\]

is realised exactly, without irrational floating-point approximations.

The ordered and symmetric geometries must not be conflated.

## 11. PNF geometric refinement

A qualitative process family is not silently converted into geometry. A geometric refinement must supply:

- the process-bearing branch family;
- the quantitative selection portfolio;
- the \(1\to n\) junction;
- attractor-projected branches;
- path markers;
- the selected ternary geometry;
- an exact split/recombine residual;
- empirical-calibration flags;
- provenance receipts.

A sound PNF projection preserves:

\[
\text{coarse boundary}
+
\text{live fine boundaries}
+
\text{zero kind}
+
\text{path markers}
+
\text{reusable overlap}
+
\text{capacity/deadline provenance}
+
\text{split/recombine residual}.
\]

It does not infer continuous angles, numerical utilities, or physical phases from prose.

## 12. Source boundaries

The geometry source atlas records:

- Michael F. Atiyah, *Topological quantum field theory*, DOI `10.1007/BF02698547`;
- Michael V. Berry, *Quantal phase factors accompanying adiabatic changes*, DOI `10.1098/rspa.1984.0023`;
- Berthold-Georg Englert, *Fringe Visibility and Which-Way Information: An Inequality*, DOI `10.1103/PhysRevLett.77.2154`.

Their imported roles are deliberately bounded:

- Atiyah supplies boundary, gluing, and composition vocabulary;
- Berry supplies path-dependent phase provenance;
- Englert supplies which-path distinguishability provenance.

None establishes that a relational process is a physical quantum system.

## 13. Strong synthesis

The resulting architecture is

\[
\boxed{
\begin{aligned}
&\text{coarse proposition boundary}\\
\to{}&\text{finite }1\to n\text{ branch junction}\\
\to{}&\text{fine channels with capacity, phase, basin, and provenance}\\
\to{}&\text{pairwise interference and contextual marginal value}\\
\to{}&\text{attractor-projected resultant and signed flux}\\
\to{}&\text{path-sensitive recombination}\\
\to{}&\text{PNF memory retaining the residual needed for later composition}.
\end{aligned}
}
\]

The pants geometry supplies the branching topology. The wave carrier supplies non-additive interaction. The attractor projection supplies direction. The path marker supplies memory-sensitive coherence. The PNF layer determines which distinctions survive compression.
