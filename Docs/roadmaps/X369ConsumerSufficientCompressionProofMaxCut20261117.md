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

`tagSensitiveStepBreaksPhaseFibre` and
`presentConsumerSufficientFutureConsumerNot` construct a
counterexample: the dropped tag changes the next phase,
so the currently lossless phase quotient is now insufficient
for the future phase consumer. The correct repair is a retained
history/tag residual, a state-dependent transition codec,
or a proof the chosen consumer never observes the lost fibre.

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
