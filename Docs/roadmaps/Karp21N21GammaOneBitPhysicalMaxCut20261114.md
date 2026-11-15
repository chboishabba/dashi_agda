# Karp-21 F1/F3: first full gamma-token physical trace, 14 Nov 2026

## Source owners

- Karp21NativeBitTapePhysicalMachineExact.agda:
  literal finite-control, bounded-head-movement two-tape machine
  and machineRunCellBudget.
- Karp21NativeGammaPrefixPhysicalSimulationExact.agda:
  ALL prefix-zero scans and first separator observation, exact
  original source scanZeros correspondence, but NO payload bits.
- Karp21GammaBinaryNativePayloadExact.agda:
  full original source readGammaBinary, structural readPayload,
  all-bit inspection bound without physical machine compilation.

NEW: Karp21NativeGammaOneBitPayloadPhysicalExact.agda
uses an explicitly stored 2-state × 4-input × 4-work-head
local instruction table. For original k=1 codeword
  0 1 b ++ suffix,
it:
1. scans B0, marks work tally;
2. observes B1 separator and advances input;
3. reads exactly one payload bit b to work head and halts.

It proves with finite Agda definitional cases that
  machineRun 3 physicalProgram initialTape
  = finalTape(payload=b, 1 Mark, remaining input suffix)
and that ACTUAL Gamma.readGammaBinary on the identical
source word is
  just ([true,b],suffix).

It also transports the existing one-new-cell-per-head-step
physical budget: with one work tape and one input tape,
the 3-step trace adds at most 3*(1+1)=6 represented cells.

The source is a concrete finite physical table and a genuine
one-token source-parser join; it is NOT a higher-order N21
instruction oracle or an assumed Gamma-Nat-cost equivalence.

## Local tests

python3 scripts/check_karp21_gamma_one_bit_physical.py
  exhausts all 2*sum_(k=0)^8 2^k = 1022 k=1
  codewords, including suffixes of lengths 0..8.
  Both k=0 and k=2 are explicit negative controls; this
  literal 3-step table does NOT handle arbitrary gamma lengths.

bash scripts/check_karp21_gamma_one_bit_physical_local.sh
  fail-closes without an actual pinned Agda 2.9 kernel.

## Exact remaining original F1–F4 / G2–G4 max-cut

F1: extend the 2-state machine to all k via an actual unary
tally read/decrement or bit-count tape and native binary payload.
No fixed k or unbounded source Nat decode.
F2: bound ALL live heap/copies/stacks and tape cells, not
just machineRunCellBudget for one token.
F3: compile original readRawGraphWord, signed edge ledger,
endpoint history, threshold and original first-enabled rule
into a finite transition table, with same-word trace simulation.
F4: count each real physical step and prove the *original*
N21 verifier polynomial-time bound. The earlier cubic
weighted comparison schedule is not yet a machine clock.
G2–G4: typed original certificate/cost receipts and
original PR.InNP require the actual F1–F4 compiler.

The universal SAT lower bound and P≠NP remain independent
open mathematics. No claim of Clay P≠NP or kernel acceptance.
