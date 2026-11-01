# SSP prime-lane 369 depth-wheel / Cantor / PNF-memory bridge

## Scope

This note records the checked interpretation implemented across:

- `DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge`;
- `DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel`;
- `DASHI.Geometry.SSP369DepthWheelUltrametric`;
- `DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric`.

It reuses, rather than replaces:

- `DASHI.Biology.TernaryCantorWheelDiffusionExact`;
- `DASHI.Foundations.SSPPrimeLane369Refinement`;
- `DASHI.Foundations.SSPPrimeLaneUnitAction`;
- `DASHI.Geometry.SSP369TreeAutomorphism`;
- `DASHI.Geometry.SSP369Ultrametric`;
- `DASHI.Cognition.PNF.EventAlgebra`;
- `DASHI.Cognition.PNF.MemoryFibre`;
- `DASHI.Cognition.PNF.LearningAlgebra`;
- `DASHI.Cognition.PNF.FibreLearningDynamics`;
- `DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge`.

The exact C3/depth-wheel synthesis is repository-internal mathematics. External memory-learning papers listed below are motivation for keeping retrieval/update, extinction, context and retained memory distinct; they are not proof authority for a C3 biological mechanism.

## 1. Depthwise wheel

Define three refinement phases

\[
C_3=\{0,1,2\}
\]

and recursively define the phase of depth `n`. The implementation proves

\[
\phi(n+3)=\phi(n)
\]

for every finite depth. In particular

\[
\phi(3)=\phi(6)=\phi(9)=0.
\]

For a carrier `X`, a `DepthWheelSystem X` consists of three endomorphisms

\[
F_0,F_1,F_2:X\to X,
\]

and the one-wheel composite is

\[
W=F_2\circ F_1\circ F_0.
\]

The first three depth-indexed steps are checked to equal one application of `W`.

## 2. Quotient/remainder coordinate

`SSPPrimeLane369DepthAddressWheel` upgrades the three special examples to an all-depth coordinate

\[
n\longmapsto(q,r),\qquad r\in C_3,
\]

implemented recursively as `WheelDepthCoordinate`.

`completedWheels` is the number of complete traversals and `residualPhase` is the unresolved phase. The executable law is

\[
(q,r)\xrightarrow{+3}(q+1,r).
\]

For

\[
3q=\underbrace{3+\cdots+3}_{q\text{ times}},
\]

Agda proves

\[
\phi(3q)=0
\]

and

\[
\operatorname{coordinate}(3q)=(q,0).
\]

Thus `3,6,9,...` are the finite stroboscopic sections of the period-three process, not isolated privileged numerals.

## 3. 3 / 6 / 9 fibres and 8 / 27 one-wheel branching

Let

\[
T=\{-1,0,+1\},\qquad P=\{-1,+1\}\subset T.
\]

The local phase carriers are

\[
C_3,\qquad P\times C_3,\qquad T\times C_3,
\]

with checked exhaustive cardinalities

\[
3,\qquad6,\qquad9.
\]

The canonical structural maps are

\[
P\times C_3\hookrightarrow T\times C_3\to C_3.
\]

A total canonical `9 -> 6` retraction is not asserted. Instead, the new residual-bearing projection is

\[
T\times C_3\to (P\times C_3)+R_0,
\]

where a zero trit returns `zeroBranchResidual phase`. On the embedded polar subcarrier the projection is proved to be a left inverse.

At one complete three-level refinement wheel, the existing Cantor counts become macro-branch multiplicities:

\[
2^3=8,
\qquad
3^3=27.
\]

These are distinct from the local `6` and `9` state-phase fibres.

## 4. The second C3: address wheel

The existing prime-lane unit action already rotates refinement digits

\[
3\to6\to9\to3.
\]

The new module proves that the canonical `p7` generator has order three on every finite `Lane369Address`, preserves refinement depth, and commutes with prefix truncation through the pre-existing tree-automorphism theorem.

At the local level there are therefore two independent actions:

\[
C_3^{\mathrm{depth}}
\quad\text{and}\quad
C_3^{\mathrm{address}}.
\]

Their product carrier

\[
\{3,6,9\}\times C_3
\]

has nine cells, and the two local actions commute definitionally because each acts on a different coordinate.

This proves the direct-product law for the checked local action only. A future state-dependent cocycle or semidirect action is a stronger object and is not inferred automatically.

## 5. Refinement equivariance and ultrametric geometry

The existing refinement and ultrametric modules use distinct address types. `SSP369DepthWheelUltrametric` therefore supplies an explicit depth-preserving adapter

\[
\iota_d:\operatorname{Lane369Address}(d)\to\operatorname{SSP369Ultrametric.Address}(d).
\]

It also defines the corresponding digitwise `3 -> 6 -> 9 -> 3` wheel on the metric carrier and proves

\[
\iota(Aa)=\widehat A\,\iota(a).
\]

The hard geometric theorem is exact preservation of common-prefix agreement:

\[
\operatorname{agreementDepth}(\widehat A x,\widehat A y)
=
\operatorname{agreementDepth}(x,y).
\]

Because the pre-existing metric is

\[
d(x,y)=D-\operatorname{agreementDepth}(x,y),
\]

the wheel is an isometry:

\[
d(\widehat A x,\widehat A y)=d(x,y).
\]

Pulling this metric back along `iota` proves that the actual `p7` refinement-address wheel is an ultrametric isometry. This closes the symmetry branch of the earlier `isometry vs contraction` question. It does **not** prove that the depth-evolution composite `W=F2 F1 F0` is contractive; that remains a separate dynamical question.

## 6. PNF: phase is provenance-relevant when it changes future evolution

The repository PNF algebra is pre-quotient and witness-preserving. The depth-wheel interpretation therefore treats a phase coordinate as provenance-relevant whenever forgetting it can change the next admissible transition.

A coarse public projection may satisfy

\[
\pi(M)=\pi(M')
\]

while the full memory fibres differ. The new memory module makes this executable rather than merely descriptive.

`WheelMemoryFibre` wraps the existing `MemoryFibre.phase : Nat` with a proof that

\[
\texttt{phase}=\operatorname{ordinal}(\phi(n))
\]

for a stated refinement depth `n`. This avoids breaking the existing API while introducing a genuinely typed C3 grading.

## 7. Learning wheel

A `MemoryPreservingUpdate` is an actual endomorphism of `MemoryFibre` together with the theorem

\[
\operatorname{rememberedEvent}(U(M))
=
\operatorname{rememberedEvent}(M).
\]

The module instantiates this interface using existing operations:

- revaluation;
- habituation;
- reinforcement;
- extinction/action inhibition.

A graded step first applies one of those operations and then aligns the existing Nat phase with the next depth-wheel grade. Agda proves simultaneously

\[
E_{n+1}=E_n,
\]

\[
n_{n+1}=n_n+1,
\]

and

\[
\phi_{n+1}=\phi_n+1\pmod3.
\]

A `ThreePhaseLearningProgram` contains three potentially different memory-preserving updates. Its composite is a complete learning wheel. The checked laws are

\[
\operatorname{depth}(W_M M)=\operatorname{depth}(M)+3,
\]

\[
\phi(W_M M)=\phi(M),
\]

and

\[
\operatorname{rememberedEvent}(W_M M)
=
\operatorname{rememberedEvent}(M).
\]

Thus the wheel grades the existing learning algebra; it does not replace it or identify the three phases with any fixed psychological labels.

## 8. Extinction and terminalisation

The existing memory implementation already keeps the remembered event while setting action weight to zero. The graded bridge proves the same relation after phase alignment:

\[
\text{actionWeight}=0
\]

while

\[
E_{\mathrm{after}}=E_{\mathrm{before}}.
\]

There is also an executable non-injectivity witness. Starting from depth zero, one graded learning step preserves the public `EventPNF`, but the full `MemoryFibre` cannot equal its source because the phase projection changes from `0` to `1`.

Hence

\[
\boxed{
\pi_{\mathrm{public}}(M')=\pi_{\mathrm{public}}(M)
\not\Rightarrow M'=M.
}
\]

This is the finite formal core of the terminalisation point: unchanged public/semantic content does not imply unchanged provenance-conditioned transition state.

## 9. Trauma/body-memory hyperfabric

`TraumaMemoryHypervoxelBridge` already supplies body-memory channels, versioned PNF memory, learning updates, 369 addresses, residuals and a guarded authority boundary.

The new bridge does not rename those channels as storage sites for propositions. Instead each channel may carry a wheel-graded learned state over the shared semantic/provenance layer.

For channel states `i,j`, define the finite C3 mismatch distance

\[
\Delta_{ij}=
\begin{cases}
0,&\phi_i=\phi_j,\\
1,&\phi_i\ne\phi_j.
\end{cases}
\]

For a coupling of weight `J_ij`, the executable pair cost is

\[
F_{ij}=J_{ij}\Delta_{ij},
\]

and a finite fabric cost is the sum over an explicit list of couplings:

\[
\mathcal F=\sum F_{ij}.
\]

This is an abstract cross-fibre phase-frustration functional. It is **not** a claim of biological spin physics and it is **not** a trauma diagnostic. It gives a precise candidate geometry for the pre-existing idea that trauma-like persistence may involve cross-fibre mismatch and path-dependent transition structure.

A `DepthWheelHypervoxelSite` ties the new learning fibre back to an actual site in the existing `PNFMemoryHypervoxel`. Learning depth and spatial hypervoxel depth remain distinct; only an explicit `learningDepth <= spatialDepth` witness relates them.

## 10. Current mathematical status

The checked structure now contains:

1. a period-three depth wheel;
2. a quotient/remainder-style `(completed wheels, residual phase)` coordinate;
3. typed `3/6/9` state-phase fibres;
4. residual-bearing rather than destructive `9 -> 6` polar projection;
5. an independent order-three address wheel;
6. a commuting local `C3 x C3` phase torus;
7. an explicit refinement-to-ultrametric address adapter;
8. an exact ultrametric-isometry theorem for the address wheel;
9. a C3-graded PNF memory wrapper;
10. executable memory-preserving learning steps;
11. a three-step learning-wheel invariant;
12. an explicit same-public-PNF/different-full-memory witness;
13. an extinction-without-erasure theorem surface;
14. a finite cross-fibre phase-frustration functional;
15. a typed bridge back into the existing trauma-memory hypervoxel.

The main remaining frontier is no longer the finite carrier. It is the dynamics of the **depth-evolution** wheel: contraction/non-expansion conditions for `W`, phase-dependent continuous scale factors, analytic self-similarity, and any empirical model that would identify particular biological/psychological processes with particular wheel phases.

## Empirical motivation references

- Nader, K., Schafe, G. E. & LeDoux, J. E. (2000). *Fear memories require protein synthesis in the amygdala for reconsolidation after retrieval*. Nature 406, 722-726. DOI: `10.1038/35021052`.
- Bouton, M. E. (2004). *Context and behavioral processes in extinction*. Learning & Memory 11, 485-494. DOI: `10.1101/lm.78804`.
- Schiller, D., Monfils, M.-H., Raio, C. M., Johnson, D. C., LeDoux, J. E. & Phelps, E. A. (2010). *Preventing the return of fear in humans using reconsolidation update mechanisms*. Nature 463, 49-53. DOI: `10.1038/nature08637`. An addendum was published in 2018; this reference is motivation only, not authority for the formal C3 construction.
