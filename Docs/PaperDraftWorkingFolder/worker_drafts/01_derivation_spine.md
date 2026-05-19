# Worker 1 Draft: Early Derivation Spine

Status: manuscript replacement draft for pages 3-5; non-promoting. This text
derives the carrier grammar used by Paper 1. It does not claim completed
physics, empirical validation, non-flat GR recovery, or final unification.

## Theorem Map

| Stage | Object introduced | Spine statement | Manuscript role |
|---|---|---|---|
| 1 | Primitive ternary state | Signed evidence with an unresolved residue requires at least three local statuses. | Explains why trit-like coordinates are structural bookkeeping, not numerology. |
| 2 | Traversal | Coordinate-local updates turn primitive states into paths in a finite state graph. | Replaces static inventory with a derivation of state change. |
| 3 | Voxel / hypercube cell | A finite block of ternary coordinates is a \(3^k\)-cell with coordinate-wall adjacency. | Gives the cube, voxel, and hypercube language a bounded formal reading. |
| 4 | Trie and ultrametric | Recursive refinement of cells is represented by prefix addresses, whose natural distance is ultrametric. | Connects traversal to UFT / sparse-voxel-trie refinement. |
| 5 | `FactorVec` | Prime-lane valuation counts refine addresses into a `Vec15 Nat` carrier over tracked supersingular-prime lanes. | Connects refinement depth to the repo-native `FactorVec` surface. |
| 6 | Projection-defect | Every surface-visible reading is a projection together with a residual defect. | Makes obstruction part of the mathematical object rather than a status note. |
| 7 | Filtration | Depth, valuation, and admissibility organize surfaces into \(F_0 \subseteq F_1 \subseteq \cdots\). | Prepares the G3 associated-graded and quotient-law boundary without claiming it is closed. |
| 8 | Derivation theorem | The above steps force the paper-facing grammar: state, traversal, refinement, valuation, projection, defect, filtration. | Supplies the early derivation spine for the constructive physics-unification architecture. |

## 1. Primitive State

**Definition 1.1 (Primitive local state).** Let
\[
T=\{-1,0,+1\}.
\]
A primitive local state is an element \(t \in T\). The values \(+1\) and
\(-1\) record oriented alternatives. The value \(0\) records unresolved
residue: structure that has not been discharged by the current surface.

**Definition 1.2 (Primitive finite state).** For a finite coordinate set
\(I\), a primitive state is a function
\[
x:I \to T.
\]
The support of resolved coordinates is
\[
\operatorname{supp}(x)=\{i\in I \mid x_i \neq 0\}.
\]

**Lemma 1.3 (Ternary minimality).** Any local carrier that distinguishes a
positive orientation, a negative orientation, and unresolved residue needs at
least three local values.

**Proof.** A two-valued carrier can distinguish at most two equivalence
classes. If it identifies the unresolved case with \(+1\), then unresolved
residue is promoted as positive evidence. If it identifies unresolved residue
with \(-1\), then unresolved residue is promoted as negative evidence. If it
identifies \(+1\) with \(-1\), then orientation is lost. Hence the three
roles require three values. This proves minimality at the bookkeeping level,
not a physical law. \(\square\)

## 2. Traversal

**Definition 2.1 (Coordinate update).** A coordinate update on \(I\) is a map
\[
u_{i,\phi}:T^I\to T^I
\]
that changes only coordinate \(i\), using a local rule \(\phi:T\to T\), and
leaves every \(j\neq i\) fixed.

**Definition 2.2 (Traversal).** A traversal is a finite sequence
\[
x_0 \xrightarrow{u_1} x_1 \xrightarrow{u_2} \cdots
\xrightarrow{u_n} x_n
\]
where each \(u_m\) is a coordinate update and \(x_m=u_m(x_{m-1})\).

**Lemma 2.3 (Traversal as address word).** Every traversal determines a word
in the update alphabet
\[
\Sigma=\{(i,\phi)\mid i\in I,\ \phi:T\to T\}.
\]

**Proof.** Record the label \((i_m,\phi_m)\) of each update \(u_m\). The
traversal is then represented by the word
\[
(i_1,\phi_1)(i_2,\phi_2)\cdots(i_n,\phi_n)\in\Sigma^\ast.
\]
This word need not determine a unique physical history; it determines the
formal update trace relative to the chosen primitive carrier. \(\square\)

## 3. Voxel and Hypercube Cells

**Definition 3.1 (Ternary cell).** For a finite block \(B\subseteq I\) with
\(|B|=k\), the local cell is
\[
C_B=T^B.
\]
It has \(3^k\) vertices. Two vertices are coordinate-adjacent when they differ
in exactly one coordinate.

**Definition 3.2 (Voxel refinement).** A voxel refinement replaces a
coordinate \(i\) by a finite child block \(B_i\). The refined local state
space replaces the factor \(T\) at \(i\) by \(T^{B_i}\). Iterating this
operation gives a nested family of finite ternary cells.

**Lemma 3.3 (Traversal embeds in the cell graph).** A traversal that updates
one coordinate at a time is a path in the coordinate-adjacency graph of
\(T^I\).

**Proof.** Each update changes at most one coordinate. Therefore consecutive
states are either equal or adjacent in the coordinate graph. A finite sequence
of such steps is a graph path. \(\square\)

**Lemma 3.4 (Hypercube language is finite-coordinate language).** The cube,
voxel, and hypercube terms used in the early manuscript can be read as finite
coordinate cells and their refinements.

**Proof.** A block \(T^B\) is a finite product of local coordinate carriers.
Its coordinate-adjacency graph is the ternary analogue of a cubical graph:
faces are obtained by fixing coordinates, and refinements replace a coordinate
by a child product. Thus the geometric language refers to finite-coordinate
movement and refinement, not to an assertion that a physical spacetime cube
has been derived. \(\square\)

## 4. Trie Refinement and Ultrametric Distance

**Definition 4.1 (Refinement trie).** Let \(\Sigma\) be a finite refinement
alphabet. A trie address is a finite or infinite word in \(\Sigma\). The
prefix order is
\[
w\preceq v
\]
when \(w\) is an initial segment of \(v\). A node \(w\) represents all
descendants with prefix \(w\).

**Definition 4.2 (Common-prefix depth).** For two infinite addresses \(a,b\),
let
\[
\lambda(a,b)
\]
be the length of their longest common prefix, with \(\lambda(a,a)=\infty\).
Fix \(0<\alpha<1\). Define
\[
\rho(a,b)=
\begin{cases}
0, & a=b,\\
\alpha^{\lambda(a,b)}, & a\neq b.
\end{cases}
\]

**Lemma 4.3 (Trie distance is ultrametric).** The distance \(\rho\) satisfies
\[
\rho(a,c)\leq \max(\rho(a,b),\rho(b,c)).
\]

**Proof.** If \(a\) and \(b\) agree for \(m\) symbols, and \(b\) and \(c\)
agree for \(m\) symbols, then \(a\) and \(c\) also agree for \(m\) symbols.
Hence
\[
\lambda(a,c)\geq \min(\lambda(a,b),\lambda(b,c)).
\]
Since \(0<\alpha<1\), increasing prefix depth decreases distance, so
\[
\alpha^{\lambda(a,c)}
\leq
\max(\alpha^{\lambda(a,b)},\alpha^{\lambda(b,c)}).
\]
The cases with equality of addresses are immediate. \(\square\)

**Lemma 4.4 (Refinement forces prefix geometry).** If observation proceeds by
successive finite refinements, then the natural comparison between two states
is the first depth at which their refinement addresses disagree.

**Proof.** At any finite depth, a surface can only inspect the prefix exposed
at that depth. Two states with the same prefix are indistinguishable to that
surface; two states with different prefixes have a first incompatible
refinement decision. This is exactly the prefix comparison used by the
ultrametric above. \(\square\)

## 5. Prime-Lane Valuation and `FactorVec`

**Definition 5.1 (`FactorVec`).** Let
\[
P=\{2,3,5,7,11,13,17,19,23,29,31,41,47,59,71\}
\]
be the tracked supersingular-prime lane set used by the repo-native carrier.
A `FactorVec` is a function
\[
\nu:P\to \mathbb{N},
\]
equivalently the `Vec15 Nat` record with one exponent coordinate for each
tracked prime lane.

**Definition 5.2 (Prime-lane bump).** For \(p\in P\), define
\[
B_p(\nu)(q)=
\begin{cases}
\nu(q)+1, & q=p,\\
\nu(q), & q\neq p.
\end{cases}
\]

**Lemma 5.3 (Coordinate bumps commute).** For all \(p,q\in P\),
\[
B_p(B_q(\nu))=B_q(B_p(\nu)).
\]

**Proof.** Check each coordinate \(r\in P\). If \(r\) is neither \(p\) nor
\(q\), both sides equal \(\nu(r)\). If \(r=p\neq q\), both sides equal
\(\nu(p)+1\). If \(r=q\neq p\), both sides equal \(\nu(q)+1\). If
\(p=q=r\), both sides equal \(\nu(p)+2\). Therefore the vectors are equal
coordinatewise. \(\square\)

**Definition 5.4 (Valuation projection of a traversal).** Given a traversal
whose update labels include prime lanes in \(P\), its valuation projection is
the `FactorVec`
\[
\nu_\gamma(p)=\text{the number of \(p\)-lane updates in the traversal
\(\gamma\),}
\]
or a more refined signed/transported variant when the owning surface supplies
that structure.

**Lemma 5.5 (From trie depth to prime valuation).** A refinement trace with
prime-lane labels has both a prefix address and a `FactorVec` valuation.

**Proof.** The prefix address records the ordered word of refinement labels.
Counting occurrences of each tracked prime label gives the valuation vector.
The address preserves order; the valuation forgets order but preserves
lane-wise exponent content. These are complementary projections of the same
trace. \(\square\)

**Boundary note.** Lemma 5.3 is a carrier-coordinate fact. Paper 1 may use the
official tracked G6 theorem for tracked cross-lane commuting claims. The
coordinate lemma alone is not a universal physical independence result.

## 6. Projection-Defect Structure

**Definition 6.1 (Surface projection).** A surface \(s\) consists of a visible
carrier \(Y_s\), an admissibility gate \(G_s\), and a projection
\[
P_s:X\to Y_s
\]
from the richer carrier \(X\) to the visible surface.

**Definition 6.2 (Defect).** The defect of \(x\in X\) relative to \(s\) is
the residual information not promoted by \(P_s\). Formally, it may be recorded
as the fiber datum
\[
D_s(x)=(x,P_s(x),G_s(x),\text{unmet obligations}),
\]
or, when the carrier has an additive split, as a residual term satisfying
\[
x=P_s(x)+D_s(x).
\]

**Lemma 6.3 (Projection without defect forgets obligations).** If two states
\(x,x'\in X\) satisfy \(P_s(x)=P_s(x')\) but differ in gate status or unmet
obligations, then the projection alone cannot distinguish them.

**Proof.** The projection value is equal by assumption. Any distinction based
on gate status, residual content, or missing proof obligations lies outside
\(Y_s\). Therefore it is lost unless recorded in \(D_s\). \(\square\)

**Lemma 6.4 (Defect makes non-closure visible).** Recording
\((P_s(x),D_s(x))\) keeps the promoted component and the unpromoted residual
in the same formal account.

**Proof.** The first component is exactly the surface-visible projection. The
second component records why that projection is not the whole carrier state:
untransported structure, failed gate status, missing quotient laws, missing
authority tokens, or other unmet obligations. Hence non-closure is represented
as residual structure, not as an informal caveat. \(\square\)

## 7. Filtration

**Definition 7.1 (Filtration).** A filtration on \(X\) is an increasing
sequence of subcarriers or predicates
\[
F_0\subseteq F_1\subseteq F_2\subseteq \cdots.
\]
In this manuscript, \(F_n\) may represent bounded refinement depth, bounded
valuation complexity, selected finite support, admissible defect grade, or
another owned surface-specific bound.

**Definition 7.2 (Associated graded target).** When quotient structure is
available, the \(n\)-th graded piece is
\[
\operatorname{gr}_n F = F_n/F_{n-1}.
\]
This notation is a target unless the equivalence relation, quotient carrier,
projection-respects-equivalence law, and descended operations are supplied.

**Definition 7.3 (Filtered operator).** An operator \(A:X\to X\) is
filtration-preserving when
\[
A(F_n)\subseteq F_n
\]
for every \(n\). It descends to \(\operatorname{gr}_nF\) only when it also
respects the equivalence relation modulo \(F_{n-1}\).

**Lemma 7.4 (Descent requires equivalence preservation).** Suppose \(A\) is
filtration-preserving and \(x\sim_n y\) means \(x-y\in F_{n-1}\). If
\[
x\sim_n y \Rightarrow A(x)\sim_n A(y),
\]
then \(A\) induces an operator on \(F_n/F_{n-1}\).

**Proof.** Define the induced map by \([x]\mapsto[A(x)]\). If \([x]=[y]\),
then \(x\sim_n y\). By equivalence preservation, \(A(x)\sim_n A(y)\), so
\([A(x)]=[A(y)]\). Thus the definition is independent of representative.
\(\square\)

**Boundary note.** This is the abstract reason G3 cannot be presented as
closed merely from selected finite-support subtraction. The quotient carrier,
kernel or equivalence law, projection-respects-equivalence law, and descended
norm/product/bracket laws are substantive obligations.

## 8. Derivation Theorem

**Theorem 8.1 (Early DASHI carrier spine).** Starting from primitive signed
state with unresolved residue, the paper-facing carrier grammar is forced in
the following restricted sense:
\[
\text{primitive state}
\to
\text{traversal}
\to
\text{voxel / hypercube cell}
\to
\text{trie / ultrametric refinement}
\to
\text{`FactorVec` valuation}
\to
\text{projection-defect}
\to
\text{filtration}.
\]

**Proof.** By Lemma 1.3, a carrier that preserves positive, negative, and
unresolved local roles requires ternary local state. By Definitions 2.1 and
2.2, changes of such state are coordinate-local traversals, and by Lemma 2.3
these traversals have update-word addresses. By Definitions 3.1 and 3.2, any
finite block of coordinates forms a \(3^k\) cell, and Lemmas 3.3 and 3.4 give
the bounded reading of voxel and hypercube traversal. Recursive refinement of
those cells is prefix refinement, so Definitions 4.1 and 4.2 and Lemma 4.3
give the ultrametric geometry. When refinement labels include tracked
prime-lane information, Definition 5.1 and Lemma 5.5 produce the `FactorVec`
valuation projection, with Lemma 5.3 giving the underlying coordinate
commutation fact. Once a surface observes only part of the richer state,
Definitions 6.1 and 6.2 require a projection-defect split, and Lemmas 6.3 and
6.4 explain why the defect must be retained. Finally, when traversal becomes
operator language, Definitions 7.1-7.3 and Lemma 7.4 show that filtration and
quotient descent are the required path to theorem-facing dynamics.

Thus the early manuscript should present DASHI as a constructive derivation of
a carrier-and-closure grammar. The theorem does not assert that the grammar
completes physics. It asserts that the listed structures are not an inventory:
they arise as successive obligations once signed unresolved state, traversal,
recursive refinement, prime-lane valuation, surface projection, and filtered
operator descent are all kept visible. \(\square\)

## Manuscript Integration Paragraph

The central object of Paper 1 is therefore not a finished physical equation
but a typed carrier grammar for a physics-unification program. A primitive
state begins with oriented alternatives and unresolved residue. Traversal
turns such states into coordinate-local paths. Finite coordinate blocks give
the disciplined meaning of cube, voxel, and hypercube language. Recursive
refinement gives a trie, and the first incompatible prefix gives the
ultrametric. Prime-lane counting gives the `FactorVec` valuation carrier.
Every theorem, observation, compression motif, or empirical comparison then
sees only a projection of that richer carrier, so the residual defect must be
kept. Filtration is the final discipline that asks whether those projected
actions descend to quotient-correct operator surfaces. This is the derivation
spine of the manuscript's constructive physics-unification architecture; its
claim is coherence of the carrier route and exact visibility of remaining
obligations, not completed validation or final unification.
