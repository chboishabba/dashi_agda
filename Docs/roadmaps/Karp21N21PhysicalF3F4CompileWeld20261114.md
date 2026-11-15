# Karp-21 F3/F4 physical compiler: exact remaining same-original weld (14 Nov 2026)

Owner: PR #1502, using the original N21 program on #1474 and Karp-21 #1445.
This document is a **compiler implementation contract**, not an NP certificate.

## 1. What must be reused (already source-written, not assumed kernel accepted)

1. `Karp21NativeGammaAllLengthFiniteTablePhysicalExact.agda`:
   one-input/one-work tape, 3-state finite table, literal per-cell moves.
   `Karp21NativeGammaAllLength{PrefixSimulation,PayloadSimulation,SeparatorAndHalt}Exact.agda`:
   physical token-by-token positive stage proofs.
   `Karp21NativeGammaAllLengthCompositePhysicalExact.agda`:
   `physicalAllLengthGammaRunSameOriginalPositive` is a single
   source-written run, positive k>=1, with physical fuel `2k+2`.
   For k=0 the original separator/halt consumes one step.
   No all-malformed-word physical acceptance/rejection theorem yet.
2. `Karp21FractranOriginalRawListMachineExact.agda`:
   `karpFractranFirstEnabledSameRawCursorStep` is **already a true
   source original first-enabled step correspondence** for the complete
   raw edge/certificate cursor; do not recreate a bogus source oracle.
3. `Karp21NativeBinaryToOriginalRawMachineStepExact.agda`:
   `nativeBinaryFirstEnabledNonterminalSameOriginalRawStep` is already
   genuine cross-machine simulation for the bit-native binary graph
   against the source original Nat graph, including short/malformed
   certificate and history conflicts.
4. `Karp21NativeWholeBinaryFiniteRunExact.agda`:
   `binaryRunTerminatesWithinOriginalEdgeCountPlusOne` proves a
   source-level rule count (≤edges+1), **not** bit-time.
5. `Karp21NativeFirstEnabledLedgerWordBoundExact.agda`:
   original same-word signed ledger bit-width bound using selected
   event subsequence. Not the whole heap.

## 2. Exact gamma instruction/resource accounting

For a positive gamma payload of length k>=1, original token bit length
`ℓ=2k+1` and the literal table uses
`k + 1 + k + 1 = 2k+2 = ℓ+1 ≤ 2ℓ` instructions.
For k=0, `ℓ=1` and `fuel=1≤2ℓ`.

For a *sequential* list of gamma tokens with original total token
bit length `n=Σℓ_i`, the **sum of payload-stage instruction counts**
is `Σ fuel_i ≤ 2n`. This is exact combinatorial arithmetic; it does
not count reinitialization of work tape, duplicated source buffers,
graph/threshold/ledger operations or the physical machine's head
repositioning. Any actual compiler that restarts a tape must charge
those steps separately. In particular, this sum alone does **not**
prove `karpFractranBitMachineClockPolynomial`.

The `Tape.machineRunCellBudget` source gives per-literal-instruction
growth ≤2 cells, so a *single* positive gamma token run consumes at
most `initialCells+2(ℓ+1)`. This likewise is not a whole-heap budget.

## 3. Correct F3 simulation relation: strict phases differ at the end

Write `s` for the original raw-list state and `c` for the physical
bit-tape state. Define `Rel(s,c)` by:

- the same original **input and certificate bit words** (with cursors);
- gamma fields decode to original n,m, endpoints and signed tokens;
- the physical history is a binary encoding of the original
  chronological endpoint history, with no omitted conflicting entry;
- two signed-magnitude ledger registers decode to the original signed
  cut numerator, including all carry and normalization;
- physical threshold word is the original W, not a fresh bound;
- a *semantic observation* quotient for terminal states.

**Terminal caveat:** the original raw-list cursor marks `finished`
before the whole-graph positive W test; the bit-native whole graph
chooses `accepted`/ `rejected` on the threshold. Literal phase
equality on every terminal is false, as the existing W=1
empty-ledger negative control demonstrates. The theorem must compare
`originalRawFinishedThresholdObservationSameBinaryTerminal`
(or an equivalent final decision quotient), not force false equality.

Proposed **physical** theorem:

`originalBitTapeStepSimulatesN21Rule :
   Rel(s,c) → originalFirstEnabled(s)=just(s') →
   ∃ t,c', physicalRun(t,c)=c' ∧ Rel(s',c')
       ∧ t≤CostPrimitive(s,c)`

with a separate genuine no-enabled-rule/halting clause. `Rel` must
handle every malformed code, short/extra certificate, conflicting
history, sign and threshold branch. No abstract Nat macro may count as
a constant-time physical operation.

## 4. F2/F4 whole-machine cost certificate

Define explicit `N=length originalWord + length certificate`.
Establish, for **every** compiled instruction and all reachable states:

- `B_input(N),B_graph(N),B_history(N),B_ledger(N),B_threshold(N)`:
  the persistent physical tape/buffer bit lengths;
- `B_tmp(N),B_stack(N),B_copies(N),B_heads(N)`:
  maximal transient scratch, recursion/iteration stack, copied
  source words and head positions; no unbounded decoded native Nat
  hidden in the implementation;
- `T_gamma(N),T_compare(N),T_add(N),T_history(N),T_threshold(N)`:
  actual physical primitive instruction counts, charging carry scans,
  copied records, branch lookup, work erasure and tape movement;
- ≤`m+1≤N+1` first-enabled source transitions, previously proved
  in the executable source; then sum the compiled per-transition
  costs to a single explicit polynomial `P(N)`.

Only after F3 and F2 establish these estimates can
`karpFractranBitMachineClockPolynomial` and
`originalN21InNP` be inhabited without laundering a source-language
rule into a physical unit-time instruction.

## 5. Exact acceptance checklist

- A: `physicalGammaAllInputsMatchesOriginalParser`;
  `nativeN21PhysicalFieldStreamSameOriginal`;
  `nativeN21PhysicalLedgerThresholdStepExact`.
- A: `originalBitTapeStepSimulatesN21Rule` on all phases,
  preserving first-enabled priority and original word.
- A: `nativeN21CompleteLiveHeapPolynomial` with all intermediates.
- A: `karpFractranDecodePreservesAcceptance`,
  `karpFractranBitMachineClockPolynomial` and type-correct
  `PR.polynomialTimeVerifier`.
- A: `originalN21InNP`; P0–P2 original Karp network/costed
  Cook–Levin remains independently pending.
- C (separate): `SATNotInP` is not implied by NP membership or
  Karp completeness.

Status: existing true source semantics and literal positive gamma
physical table are **reused**; the original full physical N21 compiler
and global bit-cost induction remain **OPEN**. Requires pinned Agda
2.9 kernel and transitive trust acceptance; no CI claim is made.
