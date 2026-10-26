# NV spin-one / C3 cross-PR max-cut (2026-10-26)

## Ownership and attribution
- Original finite C3 group action: `DASHI/Core/FiniteC3OrbitStabilizerExact.agda` (Dixon & Mortimer 1996, as credited in owner).
- Existing spin-one representation dimension: `DASHI/Physics/QFT/NonAbelianFusionFromSpin.agda`. This is a dimension receipt, not a physical Hamiltonian realisation.
- Exact roots of unity and Fourier: `DASHI/Algebra/TriadicDepthOneCharacters.agda`, `DASHI/Moonshine/C3FourierConjugationExact.agda` (Terras, Serre and separate Monster source preserved in owner).
- Order-three action and failure-to-promote contract: `DASHI/Core/ThreeChannelC3EquivarianceGateExact.agda`.
- Quantum bridge: `DASHI/Algebra/Quantum/DASHIQuantumBridge.agda`.
- Architecture dimensions 16x8: source-attributed manufacturer specification from supplied discussion; do not treat as native quantum connectivity evidence.
- New contribution in PR #1262: finite chosen-label C3 chart and exact non-invariance of the Sz² energy profile under the 3-cycle. No original spin-one theory is claimed.

## New bounded exact result
In basis-label convention `c0 -> +1`, `c1 -> 0`, `c2 -> -1`, the diagonal `Sz²` profile is `(1,0,1)`. Because the canonical C3 cycle sends `c0` to `c1`, energy preservation would imply `0 = 1`. The new finite proof discharges this contradiction by empty pattern.

This says nothing about Hamiltonians other than the stated symbolic profile, or a special zero splitting coefficient `D = 0`; it does not prove a physical commutator equation over complex operators.

## Cross-PR reuse map
- dashi_agda #1260 (Eisenstein lambda^9 / C3): phase arithmetics and CRT are richer than required for a one-spin obstruction; do not vendor duplicative arithmetic.
- dashi_lean4 #76 (quantum mereology): existing partial-trace/g-TPS infrastructure is the candidate owner for subsystem reductions and register locality proofs.
- dashi_lean4 #85 (Fock parity / quantum channels): channel and superselection techniques can guide optical readout contracts, but fermionic Fock parity does not equal NV spin-1.
- dashiQ #3 (experiment receipts) and #2 (MDL promotion): candidate owner for hardware evidence and measured claims; do not promote source claims automatically.
- dashi_agda #1263 (causal identifiability): distinguish device readout, physical mechanism and independent confirmation.

## Remaining proof cut
1. Agda focused typecheck of all three NV files (not run here).
2. Physical spin-1 operator basis and complex/unitary representation, then show explicit noncommutation for D != 0.
3. Optical preparation/measurement CPTP or instrument contracts, with source-bearing measured parameters.
4. Explicit gate graph (within core and any physical inter-core link), and certified gate-to-topology compiler.
5. Test fixture using actual experimental or vendor-reported data with provenance and claim stages.
6. Cross-prover correspondence with Lean #76 only after same-object carrier, basis convention and parameter match.

No hardware performance or quantum advantage is established by these symbolic finite results.
