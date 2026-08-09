# Attractor-Aligned Branch Selection and Finite Interference

This note is the quantitative continuation of the relational process-bearing
hyperfabric.  It separates five questions which a raw count of options cannot
answer:

1. Can the branch be serviced?
2. Does it tend toward the desired attractor?
3. Does it provide useful information even without direct progress?
4. Does it reinforce or obstruct the other live branches?
5. Does it reach a genuinely distinct basin?

The central law is

\[
\boxed{
\text{additional optionality is beneficial only when its marginal
attractor value exceeds its service, diversion, and interference burden.}
}
\]

## 1. Benefit and burden ledgers

For branch \(B_i\), retain:

\[
(g_i,u_i,c_i,d_i,b_i,r_i),
\]

where:

- \(g_i\) is signed drift relative to the desired attractor;
- \(u_i\) is information gain;
- \(c_i\) is servicing cost;
- \(d_i\) is diversion cost;
- \(b_i\) is its destination basin;
- \(r_i\) records reversibility.

For a portfolio \(P\), define non-negative ledgers

\[
\operatorname{Benefit}(P)
=
\sum_{i\in P} g_i^+
+
\sum_{i\in P}u_i
+
\sum_{i<j}I_{ij}^+,
\]

\[
\operatorname{Burden}(P)
=
\sum_{i\in P} g_i^-
+
\sum_{i\in P}c_i
+
\sum_{i\in P}d_i
+
\sum_{i<j}I_{ij}^-.
\]

Here

\[
g_i^+=\max(g_i,0),
\qquad
g_i^-=\max(-g_i,0),
\]

and similarly for positive and negative interaction mass.

The Agda implementation avoids assuming a canonical subtraction operation over
all relational values.  It compares two portfolios constructively by
cross-addition:

\[
P\succ Q
\iff
\operatorname{Benefit}(P)+\operatorname{Burden}(Q)
>
\operatorname{Benefit}(Q)+\operatorname{Burden}(P).
\]

When ordinary subtraction is available, this is equivalent to

\[
\operatorname{Benefit}(P)-\operatorname{Burden}(P)
>
\operatorname{Benefit}(Q)-\operatorname{Burden}(Q).
\]

The witness records the exact positive margin.

## 2. Exact finite counterexamples to branch monotonicity

The canonical finite family contains branches \(A\), \(B\), a noise branch
\(N\), an exploration branch \(E\), and a trap branch \(T\).

### Individually useful branches can combine badly

The individual ledgers are:

\[
A:(5,2),
\qquad
B:(4,2),
\]

where each pair is `(benefit, burden)`.

Both dominate the empty portfolio.  With constructive interaction of magnitude
\(2\),

\[
A\cup B:(11,4),
\]

and the pair dominates \(A\).

With destructive interaction of magnitude \(8\),

\[
A\cup B:(9,12).
\]

Then \(A\) alone strictly dominates the pair.  Therefore:

\[
\boxed{
A\succ\varnothing
\land
B\succ\varnothing
\not\Rightarrow
A\cup B\succ A.
}
\]

This is a concrete non-additivity theorem, not merely an advisory comment.

### Option noise can increase labels without increasing reachable structure

Three branches are assigned distinct labels but the same destination basin:

\[
b_1=b_2=b_3=7.
\]

The implementation computes:

\[
N_{\mathrm{nominal}}=3,
\qquad
N_{\mathrm{effective}}=1.
\]

Thus:

\[
\boxed{
\text{nominal option count}
\neq
\text{number of distinct reachable basins}.
}
\]

### Exploration can be useful without direct drift

The exploration branch has

\[
g_E=0,
\qquad
u_E=4,
\qquad
c_E=1.
\]

It strictly dominates doing nothing because information can prune an
infeasible region or establish a reusable constraint.

### Immediate utility can lead into a bad basin

The trap branch has:

\[
r_T^{\mathrm{local}}=5,
\qquad
g_T^{\mathrm{global}}=-3.
\]

It is locally attractive while moving away from the desired attractor:

\[
\boxed{
\operatorname{ImmediateUtility}(T)>0
\not\Rightarrow
\operatorname{GlobalAttractorProgress}(T)>0.
}
\]

## 3. Finite branch selection

The implemented candidate family compares:

- the empty portfolio;
- \(A\) alone;
- \(A\) plus option noise;
- \(A+B\) with constructive interaction;
- \(A+B\) with destructive interaction.

The constructive pair has the exact ledger:

\[
(11,4)
\]

and is certified to dominate the other named candidates while remaining within
capacity:

\[
c_A+c_B=4\le 10.
\]

This is deliberately a finite candidate-family theorem.  It is not promoted to
a claim that an empirical person's complete choice space has been measured or
that one scalarization is morally canonical.

## 4. Geometric reading

Let \(V_{A^\ast}\) be a value or Lyapunov-like function whose lower values are
closer to the intended attractor.  A local branch direction \(v_i\) has drift

\[
g_i
=
-\nabla V_{A^\ast}(S_t)\cdot v_i.
\]

Then:

- \(g_i>0\): approach;
- \(g_i=0\): circulation or neutral direct drift;
- \(g_i<0\): repulsion.

The viability filter is separate.  A branch may be geometrically nameable but
outside the agent's viable cone because of institutional, economic, temporal,
or capacity constraints.

The `one waist to n legs` picture is a branching junction:

\[
j_{\mathrm{coarse}}
\longrightarrow
\{j_{\mathrm{fine},1},\ldots,j_{\mathrm{fine},n}\}.
\]

The waist carries the coarse proposition or goal.  Each leg carries a
context-specific continuation.  Leg width can represent allocated service
capacity, while its tangent and eventual basin represent local and global
alignment.

## 5. Exact double-slit law

The repository already contains a finite wave carrier

\[
\psi=(x_r,x_i)\in\mathbb Z^2
\]

with superposition by componentwise addition and intensity

\[
\|\psi\|^2=x_r^2+x_i^2.
\]

For two branch waves \(\psi,\chi\), define

\[
\langle\psi,\chi\rangle
=
x_ry_r+x_iy_i
\]

and

\[
I(\psi,\chi)=2\langle\psi,\chi\rangle.
\]

The Agda theorem proves for arbitrary integer-pair waves:

\[
\boxed{
\|\psi+\chi\|^2
=
\|\psi\|^2
+
\|\chi\|^2
+
2\langle\psi,\chi\rangle.
}
\]

The cross term is the exact branch-interference contribution.

Canonical witnesses include:

\[
\|(1,0)+(1,0)\|^2=4,
\]

\[
\|(1,0)+(-1,0)\|^2=0,
\]

\[
\|(1,0)+(0,1)\|^2=2.
\]

These correspond respectively to constructive, destructive, and quadrature
relations on the finite four-phase carrier.

## 6. Exact n-slit law

For a finite list of branch waves

\[
\Psi=\{\psi_1,\ldots,\psi_n\},
\]

define

\[
\operatorname{Sum}(\Psi)=\sum_{i=1}^n\psi_i,
\]

\[
D(\Psi)=\sum_{i=1}^n\|\psi_i\|^2,
\]

and

\[
P(\Psi)=
2\sum_{1\le i<j\le n}
\langle\psi_i,\psi_j\rangle.
\]

The generic Agda induction proves:

\[
\boxed{
\left\|
\sum_{i=1}^n\psi_i
\right\|^2
=
D(\Psi)+P(\Psi).
}
\]

The proof is not a stored receipt.  It uses:

1. the exact double-slit polarization identity;
2. distributivity of pair interference over a sum;
3. induction over the finite branch list;
4. an integer-ring rearrangement theorem.

Consequently the contribution of a branch is contextual:

\[
\Delta_k
=
\|\Psi+\psi_k\|^2-\|\Psi\|^2
=
\|\psi_k\|^2
+
2\sum_{i\in\Psi}
\langle\psi_i,\psi_k\rangle.
\]

Closing one slit removes both its diagonal term and every cross term involving
that slit.

## 7. Three-slit residual

Define the third-order residual

\[
\begin{aligned}
I_3(\psi,\chi,\omega)
={}&
I(\psi,\chi,\omega)
-I(\psi,\chi)
-I(\psi,\omega)
-I(\chi,\omega)\\
&+I(\psi)+I(\chi)+I(\omega).
\end{aligned}
\]

The integer-ring theorem proves:

\[
\boxed{
I_3(\psi,\chi,\omega)=0
}
\]

for all waves on this amplitude-squared carrier.  Therefore the finite carrier
has diagonal and pairwise cross terms but no irreducible third-order term.

This is the appropriate boundary for the relational analogy: branch
interactions can be non-additive and pairwise phase-sensitive without claiming
that cognition or family relationships are physical quantum systems.

## 8. Integration with PNF memory and trauma

A PNF branch memory should retain:

\[
(\text{drift},\text{information},\text{cost},\text{basin},
\text{phase},\text{cross terms},\text{expiry},\text{provenance}).
\]

A terminal label such as `failed` loses whether the branch:

- moved in the wrong direction;
- duplicated an existing basin;
- yielded useful constraint information;
- was destroyed by interference;
- exceeded service capacity;
- expired before selection;
- entered a locally rewarding trap.

Trauma can deform branch selection in two opposite directions:

\[
\text{past branch loss}
\to
\text{branch hoarding},
\]

or

\[
\text{past branch harm}
\to
\text{premature pruning}.
\]

The correction is not `keep every option open`.  It is context-sensitive
estimation of:

\[
\text{viability}
+
\text{attractor drift}
+
\text{information value}
+
\text{interaction}
+
\text{reversibility}
-
\text{service and diversion burden}.
\]

## 9. Source boundaries

The associated source atlas records:

| Source | Bounded use |
|---|---|
| Joseph P. LaSalle, *Some Extensions of Liapunov's Second Method*, DOI `10.1109/TCT.1960.1086720` | Value-function and region-of-attraction provenance |
| Jean-Pierre Aubin, *A Survey of Viability Theory*, DOI `10.1137/0328044` | State- and control-constrained feasible trajectories |
| Richard Bellman, *Dynamic Programming*, DOI `10.1515/9781400835386` | State-indexed continuation and finite policy comparison |
| Rafael D. Sorkin, *Quantum Mechanics as Quantum Measure Theory*, DOI `10.1142/S021773239400294X` | Diagonal, pairwise, and higher-order interference hierarchy |

None of these sources proves the empirical branch values assigned to a person.
The exact theorems concern finite carriers and explicitly supplied weights.
