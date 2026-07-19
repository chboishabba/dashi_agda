# DASHI quantum computation programme

This slice turns the quantum-computation discussion into four typed, falsifiable downstream interfaces. It assumes the repository's contraction, quadratic/signature, Clifford, spin, and wave-lift prerequisites are already certified; it does not restate those results as new postulates.

## A. DASHI on quantum hardware

`DASHIQuantumBridge.agda` packages the certified bridge from a DASHI descent system into a reversible wave carrier. `DASHIHybridExecution.agda` then separates:

1. unitary wave transport;
2. observation back to a DASHI state; and
3. the certified semantic contraction step.

The bridge law `observedTransportIsStep` yields `hybrid-codeLength-descent`: the hardware-facing round agrees with the existing DASHI step and therefore inherits its MDL descent theorem.

## B. Classical DASHI emulation of structured quantum states

`DASHIStructuredStateCompression.agda` deliberately targets a named structured state class, not arbitrary Hilbert space. A certified model must provide:

- encoding and reconstruction;
- an explicit approximation predicate;
- honest source and description costs;
- reconstruction soundness; and
- non-inflation of description cost.

A genuine advantage requires `StrictCompressionWitness`. Operational usefulness is stated separately through `ObservableAdequacy`, so approximate state reconstruction may still preserve every selected observable exactly.

## C. Classical/quantum bridge

`DASHIQuantumBridge.agda` carries the proved Clifford data and axioms, an even/spinorial carrier, a wave lift, an observation map, and state-indexed unitary transports. This is the formal seam between contractive semantic state and reversible quantum transport.

## D. DASHI-normalized quantum computation

`DASHIQuantumNormalForm.agda` defines operational equivalence by equality of program outputs on every input. A `DASHINormalizer` must be:

- operationally sound;
- complexity non-increasing;
- defect non-increasing; and
- idempotent.

A claimed optimization advantage requires an explicit `StrictNormalFormGain`; no unconditional complexity-class separation is encoded.

## Assembly

`DASHIQuantumComputationProgram.agda` assembles all four lanes and requires separate evidence for:

- bridge round-trip;
- strict structured-state compression;
- observable adequacy; and
- strict quantum-program normal-form gain.

This keeps the claims independent. Success in the hybrid execution lane does not silently promote a classical emulation or asymptotic complexity claim.

## Focused validation

```bash
scripts/run_agda29_parallel_check.sh \
  DASHI/Algebra/Quantum/DASHIQuantumBridge.agda \
  DASHI/Algebra/Quantum/DASHIHybridExecution.agda \
  DASHI/Algebra/Quantum/DASHIStructuredStateCompression.agda \
  DASHI/Algebra/Quantum/DASHIQuantumNormalForm.agda \
  DASHI/Algebra/Quantum/DASHIQuantumComputationProgram.agda
```
