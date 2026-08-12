# SSP prime-lane 369 depth-wheel / Cantor bridge

## Scope

This note records the finite, checked interpretation implemented in
`DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge`.

It reuses, rather than replaces:

- `DASHI.Biology.TernaryCantorWheelDiffusionExact` for the balanced-ternary carrier and the polar Cantor restriction;
- `DASHI.Foundations.SSPPrimeLane369Refinement` for the depth-indexed 3/6/9 address tree;
- `DASHI.Physics.Closure.SSPPrimeLane369DepthPhaseBridge` for the existing prime-lane/depth/stage bridge.

No external paper is being claimed as the source of this exact construction, so no DOI is attached. The result is an internal synthesis of existing repository objects.

## Depthwise wheel

The crucial distinction is between rotating a trit value at one fixed depth and cycling the *role of successive refinement morphisms*.

Define three refinement phases

\[
C_3=\{0,1,2\}
\]

and the depth phase

\[
\phi(n)=n\bmod 3.
\]

The Agda implementation avoids an additional modulo dependency by defining the same map recursively through the three-cycle. It proves

\[
\phi(n+3)=\phi(n)
\]

for every finite depth, and in particular

\[
\phi(3)=\phi(6)=\phi(9)=0.
\]

Hence depths 3, 6 and 9 are distinguished stopping depths of a period-three refinement process: one, two and three complete wheel traversals.

## Phase-dependent refinement and renormalisation

For a carrier `X`, a `DepthWheelSystem X` consists of three endomorphisms

\[
F_0,F_1,F_2:X\to X.
\]

The elementary refinement at depth `n` is `F_{phi(n)}`. One full wheel is the composite

\[
W=F_2\circ F_1\circ F_0.
\]

The checked theorem `firstThreeDepthStepsAreOneWheel` identifies the first three depth-indexed steps with this composite exactly. This is the finite algebraic core of a period-three renormalisation picture; no analytic fixed-point, convergence, or scale-invariance theorem is inferred from it.

## Phase-coloured refinement addresses

Every existing `Lane369Address d` can be lifted to a `PhaseTagged369Address d` carrying the proof that its phase is exactly the phase determined by its depth. The existing canonical `3 -> 6 -> 9` address has depth three and therefore closes at phase zero.

This gives a literal finite version of a phase-coloured cylinder/refinement stratum: an address has both its structural prefix and a depth residue class modulo three.

## Typed 3 / 6 / 9 fibre interpretation

Let

\[
T=\{-1,0,+1\}
\]

be the full balanced-ternary state carrier, let

\[
P=\{-1,+1\}\subset T
\]

be the polar Cantor restriction, and let `C3` be the three depth phases.

The checked finite carriers are:

\[
C_3,\qquad P\times C_3,\qquad T\times C_3.
\]

Explicit exhaustive atlases in Agda have lengths

\[
3,\qquad 6,\qquad 9
\]

respectively. Thus the interpretation is not merely `6 = 2*3` and `9 = 3*3`: the two factors have typed meanings.

The canonical maps are

\[
P\times C_3 \hookrightarrow T\times C_3 \to C_3.
\]

The first map embeds the polar/Cantor state while preserving the depth phase; the second forgets the state coordinate. The implementation proves the corresponding commuting equation.

A canonical map in the opposite direction

\[
T\times C_3\to P\times C_3
\]

is deliberately *not* asserted, because the zero trit has no canonical polar image without an additional policy. The boundary record pins this non-promotion explicitly.

## Relation to the previous wheel

`TernaryCantorWheelDiffusionExact` already contains the fixed-depth trit cycle

\[
-1\to0\to+1\to-1.
\]

The new construction does not identify that value rotation with the depthwise wheel. They are independent ternary structures:

\[
\text{state ternarity}\quad x_n\in T,
\]

and

\[
\text{depth-phase ternarity}\quad \phi(n)\in C_3.
\]

Their product is exactly the nine-state full phase fibre, while restricting state ternarity to the polar Cantor boundary gives the six-state phase fibre.

## Analytic continuation boundary

A future continuous/self-similar instance may choose three contraction factors or refinement operators and study the three-step scale

\[
\Lambda=\lambda_0\lambda_1\lambda_2.
\]

That would connect naturally to `BalancedTernaryContinuousEnvelope`, where the phase-symmetric special case has a single depth scale. This PR intentionally stops before claiming contraction, fractal dimension, fixed-point existence, or a renormalisation-group theorem; those require separate analytic hypotheses and receipts.
