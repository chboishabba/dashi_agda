# X369 P0 — C3 gauge versus consumer-sufficient compression (17 Nov 2026)

**Owner:** DASHI finite formalism. **Companion:** LeechTransformer PR #5.
**Proof file:** `DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda`.
**Status:** Agda source committed; no Agda executable/kernel runner available in
the present environment. These are *proof terms proposed for kernel checking*,
not a claim of Agda 2.9 acceptance. Do not merge into Golden TOE imports
before checking. No Python implementation or new GPU experiment was added.

## Correction to the research claim

A full three-channel C3 action `T(Rx,h)=P T(x,h)` with an
unrestricted full-channel head has a change-of-basis gauge:
`head'(Pt)=head(t)`. Therefore **fixed rotation by itself adds no
unrestricted-head expressivity**. This says NOTHING about:

1. a smaller or quantised source code `E : X -> Q`;
2. preservation of a particular consumer `C : X -> Y`;
3. preservation of a future consumer after original state transition;
4. actual description length, bit width, runtime, bandwidth or energy;
5. restricted/structured heads with fewer independent weights;
6. independent semantic action and original trained model refinement.

The exact consumer-relative acceptance gate is already in
`DASHI/Core/ConsumerDescentMinimalObserverExact.agda`:

    E(x) = E(y)  ->  C(x) = C(y).

This is distinct from lossless reconstruction `decode(E(x))=x`.
With a section, fibre constancy gives explicit factorisation; the
canonical consumer itself is the least informative sufficient observer
in the existing observer refinement order.

## New proof targets and source bodies

### G0: full-channel gauge equivalence
A `Triple A` with explicit `rotate`/`unrotate`, two inverse laws,
`rotateCubed` and bidirectional **all-head** transport.
Every full-channel linear head is included; the result does not
say a constrained, low-rank, quantised or cheap head is unchanged.

### C0: exact non-injective C3 compression witness
`TaggedPhase=(phase in Z3, tag in Bool)`. `phaseCodec` retains only
the phase, discarding the tag. `codecSufficientForPhase` proves
that the phase consumer is exactly preserved. `rawWitnessesNotEqual`
shows that two different original states really collide in the code.
`phaseCodecIntertwinesC3` proves that this *non-injective* code still
retains the nontrivial phase action. It is a finite cardinality witness
(6 explicit fine combinations versus 3 coarse phase labels), NOT
a real packet byte count or universal 2:1 physical compression gain.

### N0: invariant-only no-go, correctly scoped
For any actual witness state `x`, an encoding invariant under an
action is not sufficient for a consumer whose output advances
by a fixed-point-free C3 permutation. The generic
`invariantCodecNotSufficientForChangingConsumer` is specialised
to the EXISTING grokking nine-pair task with
`modularGrokkingInvariantCodeNoGo`.

This does not contradict C0: the phase codec **transforms
equivariantly**, it is not invariant. A lossless phase in a
small carrier can be sufficient. Discarding the phase while
requiring the consumer to distinguish the three phases cannot.

### F0: current and future consumer exactness
`fullReconstructionImpliesConsumerSufficiency` proves full raw
round-trip sufficient for every consumer, while C0 proves it is
not necessary for a *specified present* consumer.

`futureConsumerSufficiency` proves an exact induction:
if the encoding is consumer-sufficient now AND the encoding
fibres are stable under the original transition, the encoding
is sufficient for the consumer after every finite number
of transitions. This does not pretend that one-time readout
equivalence implies transition stability.

`encodedTransitionWeldImpliesFibreStability` and
`compressedTransitionPreservesEveryFutureConsumer`
close the POSITIVE same-state diagram:
`E(step(x)) = stepCode(E(x))` together with current
consumer-sufficiency implies sufficiency after every
finite iterate. The exact source Leech/FFN/History MoE
transition-to-code weld is still an independent obligation.

`tagSensitiveStepBreaksPhaseFibre` and
`presentConsumerSufficientFutureConsumerNot` construct a
counterexample: the dropped tag changes the next phase,
so the currently lossless phase quotient is now insufficient
for the future phase consumer. The correct repair is a retained
history/tag residual, a state-dependent transition codec,
or a proof the chosen consumer never observes the lost fibre.

## P0 fixed-width quantization is now an exact finite theorem target

The new module also defines `oneBitCannotPreserveThreePhaseConsumer`
using an exhaustive Agda distinction of all three independently
observable phases: an encoder into ONE Bool bit must collide on two
different required output labels and therefore cannot be
consumer-sufficient. In contrast, `phaseToTwoBits` and
`twoBitsToPhase` give an exact zero-error roundtrip for all
three values using TWO Bool bits; `twoBitsSufficientForPhase`
retains consumer sufficiency on the full six tagged input states
while `twoBitsDiscardTheIrrelevantTag` demonstrates real
non-injectivity on the raw carrier. Hence the MINIMUM FIXED
ZERO-ERROR BIT WIDTH of this finite three-label consumer is 2.
This is not a universal Shannon-rate theorem, source-bit codec,
model quantisation benchmark, or 2:1 measured Leech compression.

## Existing owners to reuse rather than duplicate

- `DASHI/Core/ConsumerDescentMinimalObserverExact.agda`:
  fibre constancy, factorisation, least consumer-sufficient observer.
- `DASHI/Core/SectionedProjectionProvenanceBridgeExact.agda`:
  section and residual reopening, consumer vs full reconstruction.
- `DASHI/Core/ConsumerQuotientBaseChangeExact.agda`:
  consumer preservation under context/restriction changes.
- `DASHI/Reasoning/LeechJointStateConsumerQuotientExact.agda`:
  selected expert/history sufficient consumer, inactive-state boundary.
- `DASHI/Reasoning/FibreRoutingCompressionLadderExact.agda`:
  admission before MDL/Pareto comparisons, local relation-fibre repair.
- `DASHI/Core/ConsumerRelativeApproximateFidelityBridgeExact.agda`:
  approximation margins; do not equate approximate state error
  with classification safety.
- `DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda` and
  `GrokkingEquivarianceDefectGeometryExact.agda`: action 0-vs-2
  rule/memorizer exact finite regression.
- `DASHI/Reasoning/TrialecticBoundaryFaceNonfactorabilityExact.agda`:
  missing triadic face cannot be reconstructed from three edge labels.
- `DASHI/Cognition/PNF/X369OriginalDirectedTriadC3PolynomialCandidate.agda`:
  source directed 2q(x)q(h), mixed mask identities (candidate,
  separate selected-leaf Agda kernel receipt still needed).

## Operational proof check (NOT executed in this context)

From the existing repo clone with its pinned Agda 2.9 toolchain:

```sh
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda
```

Check imported original Agda modules and all referenced declarations
with the exact repository toolchain; fix any elaboration errors in
this original branch, then record exact SHA, checker version, logs
and selected import closure before golden promotion.

## Highest-alpha remaining proof obligations

1. **Costed minimal sufficient codec:** instantiate existing
   consumer-MDL and Pareto owners with a *real original LILA*
   codec/precision/capacity cost, rather than synthetic tag count.
2. **Restricted-head rank:** prove conditions under which a
   compressed/equivariant readout retains *specific consumer*
   decisions while reducing parameter/bit cost; unrestricted
   gauge is an insufficient comparator.
3. **Finite-precision margin:** instantiate existing approximate
   fidelity theorem on the selected source top-k and output
   decision margins with actual roundoff/quantization bounds.
4. **Future recurrent state:** weld the abstract transition
   stability premise to selected expert histories, routing
   ties, source reactivation and inactive-history owner; provide
   counterexample where a discarded fibre is future relevant.
5. **Grokking/semantic phase:** independent learned input/label
   action and heldout composition; the finite task no-go alone
   is not a trained model theorem.
6. **Proof acceptance:** run the pinned checker; no kernel
   result is fabricated here.

**Research decision:** preserve consumer-relevant invariant amplitude,
equivariant phase and necessary face/history residuals. Minimise
the *entire admitted code+decoder+state-transition cost*, not raw
activation dimension or a formally equivalent change of basis.
No original LILA performance, codec ratio or semantic steering is
claimed before source-backed evidence.


## P0 original Leech router: a *conditional* 3-to-2 directed-channel code

New proposed proof module:
`DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda`.

It uses the ORIGINAL source owner
`X369OriginalDirectedTriadC3PolynomialCandidate` for
`originalSelf`, `originalCyclic`, `originalAnticyclic`.
The three directed channels of x=(a,b,c), h=(A,B,C) obey

    self + forward + reverse
      = (a+b+c)(A+B+C).

A 6-variable `Data.Integer.Solver` proof is supplied;
the inverse reconstruction is a 3-variable solver proof.
Consequently **if the consumer already knows the sourceDC
product**, two directed scalars plus THAT externally
supplied side information exactly reconstruct all three.
The code `encodeDirectedTwo` and decoder
`decodeDirectedWithKnownDC` form a constructive
full-channel recovery under that precondition.

The essential counterexample is ALSO ORIGINAL SOURCE, not
a synthetic arbitrary triple: x=(1,0,0) with h=(0,0,0)
vs h=(0,0,1) produces directed (0,0,0) vs (0,0,1).
The retained first two scalars collide, while an original
consumer observing reverse distinguishes them. The
`twoDirectedWithoutDCNotSufficient` proof prohibits an
unqualified 3→2 data-loss claim. Conversely, every
consumer that factors through the two kept channels is
exactly sufficient.

This exhibits the real research boundary:
an already-available shared DC/summary enables a
relative-channel reduction; paying to COMPUTE or STORE
one extra side scalar per expert could erase the savings.
It does NOT certify an original memory/compute/latency
benefit. Compare exact source tensor reuse, per-expert
history availability, quantizer precision, provenance,
decoding arithmetic and future-state admission.

Check this additional new head with pinned Agda:

```sh
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda
```

Both new files are unverified proof-source proposals in
this environment, not kernel-accepted theorems.


## 17 Nov continuation: executable SymPy CI stand-in and original-source score/MDL cuts

`scripts/check_x369_p0_sympy_standin.sh` now verifies the
**actual integer polynomial identities**, original-source
counterexamples and finite quotient properties under SymPy
1.14.0. The only Python introduced is this symbolic/finite
validation harness: the proof owners and source semantics remain
Agda, not a Python model implementation. CI owner:
`.github/workflows/x369-p0-sympy-standin.yml`.
The local identical symbolic suite returned
`X369_SYMPY_STANDIN_PASS 27 symbolic/finite checks`;
the GitHub workflow's own execution remains independent and must
be observed before reporting cloud CI green.

The source-directed codec now also supplies:
- `originalFeatureRealizesEveryDirectedTriple`:
  the actual feature (T((1,0,0),(A,B,C))=(A,B,C))
  reaches all integer triples; a universal arbitrary-source
  three-to-two **coordinate-drop** theorem is false.
- `rawWeightedScoreFactorization` /
  `originalWeightedScoreTwoPlusSourceDC`:
  the ACTUAL learned linear head with weights
  `ws,wf,wr` can be evaluated as
  `(ws-wr)*self+(wf-wr)*forward+wr*sourceDC`.
  No third directed feature needs to be materialised if
  source DC is already admitted.
- `zeroDCWeightedScoreNeedsOnlyTwo`:
  with an independently certified sourceDC=0,
  a two-channel weighted original head is exact.
- `rawTwoChannelQuantizationError`: for quantization
  residuals `es,ef,eD`, the exact score error is
  `(ws-wr)*es+(wf-wr)*ef+wr*eD`.
  This is NOT a magnitude/decision bound until actual
  quantizer tolerances and top-k margins are supplied.

A new finite **costed consumer-MDL** source adapter is
`DASHI/Cognition/PNF/X369CenteredDirectedConsumerMDLExact.agda`.
It reuses `AdmissibleConsumerMDLHyperfabricExact` rather
than creating a new MDL algebra. It restricts the original
source to certified zero-DC triads, and compares ONLY
the explicitly declared portfolio of original-coordinate
projections: first alone (cost=1), first+forward (cost=2),
full three channels (cost=3). The first-only candidate
has an actual centered-source collision:
`x=(1,0,0)`, `h0=(0,0,0)`,
`h1=(0,1,-1)`; reverse differs.
The two-channel decoder reconstructs reverse exactly
for all certified zero-DC states. The resulting
`centeredTwoIsMinimalInDeclaredPortfolio` theorem
is *portfolio-relative*, in number of retained original
fixed-width feature scalars. It is NOT minimum storage
bits over arbitrary nonlinear encodings, total runtime
or full recurrent future-state sufficiency.

**Important further no-go:** for the unrestricted original
feature map, two-channel coding without the DC
or a source restriction cannot reconstruct every
reverse-sensitive consumer, even though all three
integer channels are attainable. Do not promote centered
subspace results to unconstrained original checkpoint data.

### Next proof/release gates, ordered

1. **Agda kernel:** validate the THREE new Agda modules
   and their selected import closures with pinned Agda 2.9,
   inspect actual errors and preserve exact head logs.
   A static parentheses audit fixed two provisional
   `Data.Integer.Solver` lambda-grouping errors; only
   the Agda kernel can certify elaboration.
2. **Quantizer-to-router margin:** reuse the existing
   `ConsumerRelativeApproximateFidelityBridgeExact`
   and source top-k proof gate; instantiate certified
   `|delta s_e| <= |ws-wr|*eps_s + |wf-wr|*eps_f +
   |wr|*eps_D` with real original precision/readout
   and a strict gap certificate. The existing source
   contribution is only an EXACT error identity.
3. **Source DC availability:** audit whether DC(x) and
   DC(h_e) are available/reusable before scoring, the
   cost of recomputation/transport and whether input
   or expert histories are *actually* centered.
4. **Future-state:** obtain a source-bound commuting
   compressed-history transition (or exhibit collision)
   for all selected and reactivated histories.
5. **Scientific release:** only compare actual
   total code+metadata+decoder+transition cost against
   an equally admitted full feature implementation,
   with independently held-out task and semantic consumers.
6. **TOE:** avoid injecting unverified candidate import
   dependencies into Golden `Unifier`/`EverythingTOE`.
   New-head Agda acceptance is still OPEN.

Reproducible symbolic stand-in:
```bash
bash scripts/check_x369_p0_sympy_standin.sh
```
Agda proof gates (NOT run here):
```bash
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369ConsumerSufficientCompressionNoGoExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369DirectedRouterConditionalCodecExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Cognition/PNF/X369CenteredDirectedConsumerMDLExact.agda
```


### P0 refinement: exact 2D C3 action survives compression

The original three directed channels satisfy the rotation
`(s,f,r) -> (r,s,f)`. On certified `s+f+r=0`, the compact
two-channel code `(s,f)` has the **exact** action

    M(s,f) = (-s-f, s),
    M = [[-1,-1],[1,0]],
    M^3 = I.

This is not an invariant-only phase erasure: the small code
retains the FULL nontrivial C3 transformation. Agda now
supplies `rotateCenteredTwoSquared`,
`rotateCenteredTwoCubed`,
`sourceCenteredC3TwoChannelIntertwines`, and
`centeredTwoCodeIntertwinesOriginalC3` on the typed
certified-zero-DC original-source domain. The source
full-three action, costed two-coordinate model, and
C3 action form a commuting square.

SymPy 1.14.0 local stand-in now returns
`X369_SYMPY_STANDIN_PASS 29 symbolic/finite checks`,
including matrix-cubed identity and source algebraic
semiconjugacy. It checks the POLYNOMIALS and finite
fixtures only, not the Agda proof terms or actual
source checkpoint centeredness.

This advances the original research interpretation:
**we are seeking a smaller consumer-sufficient
EQUIVARIANT realization**, not an expanded unrestricted
three-channel hypothesis class. The phase action
survives exactly on the admitted subspace; whether
the trained model's histories live there remains open.
No bit/compute savings or neural-semantic C3 theorem
is implied by this structural result.


## 17 Nov second P0 cut: quantized top-k margin and common-DC router quotient

**New finite decision proof file:**
`DASHI/Cognition/PNF/X369QuantizedRouterDecisionMarginExact.agda`.

It reuses the source weighted-score/quantization-error owner
and the existing approximate consumer-fidelity owner.
For every finite expert index `e : Fin E`, a score
certificate explicitly supplies its admitted original
source score, quantized score and enclosing interval
`[lowerEnvelope(e),upperEnvelope(e)]`.
It also supplies the original admitted TopK selection mask.
If, for every selected `i` and unselected `j`,

    upperEnvelope(j) < lowerEnvelope(i),

then the quantized score of `i` remains STRICTLY above
that of `j`. The same certificate also protects the
original scores' cross-boundary ordering. This is
an interval/sort theorem only: its sufficient inequality
does not imply identical mixture weights, intermediate
expert outputs, retained histories, future semantics
or the availability of an actual quantizer bound.
Finite witness (original scores 1,0, quantized 0,1)
shows ranking can reverse without strict margins.

The original source weight-error law already proved
symbolically is

    error_e = (ws-wr)*es_e + (wf-wr)*ef_e + wr*eD_e.

For admitted scalar absolute errors, the triangle
envelope is

    B_e = |ws-wr| eps_s_e + |wf-wr| eps_f_e
          + |wr| eps_D_e.

The current Agda interval theorem expects an actual
checked envelope as input. Supplying this bound for
the source model (floating point, rounding, and all
real expert candidates) remains OPEN; it must not
be inferred from the algebraic identity alone.

**Stronger exact consumer-relative compression.**
The original shared-head router score factors as
`L_e=(ws-wr)*s_e+(wf-wr)*f_e+wr*D_e`.
When `D_i=D_j` across candidates, their relative
score equals

    L_i - L_j = (ws-wr)*(s_i-s_j)
                + (wf-wr)*(f_i-f_j).

This holds for nonzero DC too: the *shared* DC term
cancels. Hence the two-channel code can suffice for
ranking/softmax relative scores without reconstructing
each full triple; the encoder still must prove equal DC
across original experts. Different DC is a decisive
original-source counterexample: two identical retained
(s,f)=(0,0) may have r=0 versus r=1, and a DC-sensitive
head distinguishes them. Shared learned weights
alone do NOT imply shared expert-history DC.

The new exact Agda declarations in
`X369DirectedRouterConditionalCodecExact` are
`twoChannelRelativeScore`,
`rawCommonDCCancels`, and
`originalSameDCRelativeScoreFactors`.
No change to the original Leech/PyTorch model was made.

**SymPy stand-in continuation.**
`scripts/check_x369_p0_sympy_standin.sh` adds exhaustive
finite checking of 2- and 3-expert strict score envelopes,
coefficient-weighted quantization-error triangle bounds,
and source common-DC score cancellation plus negative
control. Independent local SymPy validation in this
session checked 141 strict 2-expert cases, 207 strict
three-expert top-1 cases, 3375 coefficient/error cases,
plus exact original DC-score polynomial identities.
The complete updated GitHub shell/workflow remains
pending an actual current-head CI run; those smaller
local checks are not an Agda kernel receipt.

**Remaining P0:** typed source quantizer error-to-Nat
interval weld, all top-k (not just top1) source tie/slot
semantics, softmax/retained-history consumer discrepancy,
and actual source-history DC admission. Reuse existing
`ConsumerRelativeApproximateFidelityBridgeExact`,
`LeechJointStateConsumerQuotientExact` and
`FibreRoutingCompressionLadderExact`, rather than
recreating their generic carriers. Remain blocked on
Agda 2.9 kernel until external proof runner available.
