# Filsinger J29–J32 integrated maximum-cut execution packet

**Scope:** one source-pinned, checkpointed, fail-closed attempt to finish the original nine-state, driver-OFF source-only nominal hybrid trajectory from J28B's certified stage-75 checkpoint through V-diode OFF, U-diode OFF, and the exact forcing period `tau=20*pi/11`.

This is a candidate implementation **not yet executed end-to-end**. The native repository must supply the pinned J25–J29A dependencies. Compiling and running `test_full_period_algebra.py` pays only the independent symbolic/mathematical algebra gates; it does **not** prove the remaining hybrid event enclosures or periodic orbit.

## Installation and one campaign

In your `chboishabba/dashi_agda` checkout at PR #1537's source branch:

```bash
# Run the independent algebra checks first (SymPy required).
python test_full_period_algebra.py

# Install the single campaign runner into the checkout.
cp check_filsinger_full_period_maxcut.py /path/to/dashi_agda/scripts/
cd /path/to/dashi_agda

python scripts/check_filsinger_full_period_maxcut.py \
  --checkpoint Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json \
  --out-dir Artifacts/smith-filsinger/full-period-maxcut \
  --budget 90

# Resume a saved checkpoint (does not rerun accepted stages).
python scripts/check_filsinger_full_period_maxcut.py \
  --checkpoint Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json \
  --out-dir Artifacts/smith-filsinger/full-period-maxcut \
  --budget 90 --resume
```

All source hashes are strictly checked. A drifted file refuses to start. Output is `full_period_progress.json` or `failed_gate.json` in the chosen output directory. Status `CHECKPOINT_BUDGET_EXHAUSTED` is **not a PASS**, and `FAIL_CLOSED_UNPAID_OBLIGATION` means an enclosure failed. There is **no** GitHub Actions/CI step and **no** external field measurement.

## What is and is not established

- Inherited: J26–J28B actually certified first **4/6** guard crossings; native J28 did **3/6** original full J24 nine-coordinate state-box admissions; J29A certified a conservative physical U-on right-endpoint handoff (exact quadratic perturbation bound 189/61100000).
- New campaign attempts: source pinning, 52nd-order source-equation Taylor, signed order-8 Peano–Baker error propagation, mode-specific Jacobians, V OFF and U OFF root isolation, conditional J24 original nine-coordinate admission, physical diode-right-endpoint comparison, exact rational Machin enclosure of source period, complete terminal state enclosure and defect.
- Still missing from any outcome of this candidate: a rigorous **nonzero initial-state ball** covering the full itinerary, its 9×9 **hybrid return derivative including spark saltation on that entire ball**, and actual rational Banach/Krawczyk self-map/uniqueness inequalities. A centre trajectory alone cannot certify a periodic fixed point. Therefore the code explicitly sets `periodic_orbit_proved=False`.
- Independently open: original J18 numerical source byte replay, original Filsinger physical netlist (0/4 verified edges), calibrated source/load metering (0/24 work samples), XC+1 Maxwell receiver startup/impedance Pareto, and any environmental/natural-source/biological/gravity claim.

## Repo integration and next proof closing gate

Existing original PR: https://github.com/chboishabba/dashi_agda/pull/1537

Canonical merged-free roadmap entry: `Docs/roadmaps/FilsingerSixEventFullPeriodPhysicalAdmissionMaximumCut20261123.md`. The runner is supplied as a **downloadable candidate local file**, not claimed to have been merged or committed to GitHub. After executing, preserve its exact source SHA, error checkpoint, full interval witnesses and the *first failing* condition; do not turn an incomplete event into a new roadmap milestone. The programme should only publish a new theorem headline once **all six ordered original events plus the true nonzero-ball return-map inclusion** are paid.
