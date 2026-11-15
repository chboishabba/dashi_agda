# R846–R848 max-cut repair: original output-zero fibre is not empty

Date: 13 November 2026. Scope: existing master R436/R834/R836/R837/R840/R841/R844/R845/R846/R848/R849/R850/R853 and the same literal 3–4–5 radius-four velocity snapshot.

## Exact source contradiction

The **old R846** statement `InactiveActiveFibreEmpty` says every mode with `Snapshot.forcingActive mode ≡ false` has `Sparse.filterSelected Snapshot.mixedCellActive (Output.physicalOutputFiber 4 mode) ≡ []`. This is FALSE at `mode = Z3.zeroMode`.

The original source six-mode velocity support is `k1=(-3,-4,0), k2=(-3,0,0), k4=(0,-4,0), k5=(0,4,0), k7=(3,0,0), k8=(3,4,0)`. In particular `Z3.addMode k1 k8 ≡ zeroMode`; the actual `Physical.pairTriad (Cube.pair k1 k8)` belongs to `Physical.physicalTriadEnumeration 4` and `Output.physicalOutputFiber 4 zeroMode`; its original `Snapshot.mixedCellActive` is `true`. Nonetheless `Snapshot.forcingActive zeroMode ≡ false`. 

New `NSTriadKNR650Rational345ZeroOutputSupportCounterexampleRound847Exact.agda` constructs these exact original membership proofs and proves the old all-mode predicate implies bottom. No fake modal function or approximate projection.

Independent integer enumeration:
- 36 ordered six-seed input pairs;
- 22 cutoff-retained output pairs;
- 6 pairs have selected output zero;
- 16 pairs have a nonzero output, exactly two per each of the eight selected force modes;
- full original 729×729 cutoff input enumerator has 226981 output-admissible ordered triads (including zero).

The correct physics is **NOT** that no zero-output incidence exists. The physical projected nonlinear contribution at zero vanishes by transversality before summation. `NSTriadKNProjectedNonlinearityZeroOutputRound436Exact.projectedNonlinearityAtZeroIsZero` already proves it.

## Exact repairs implemented

1. Correct `NSTriadKNR650Rational345ForcingSupportMaxCutRound846Exact.InactiveActiveFibreEmpty` to require the original `Output.modeEqual mode zeroMode ≡ false` in addition to inactive forcing.
2. In `R846.Evaluate.inactiveProjectedZero`, case-split on this **same original executable modeEqual**. If zero, invoke original `R436.projectedNonlinearityAtZeroIsZero` using `Direct.snapshotVelocityTransverse E`. Otherwise use its original sparse R840 fold, but with the corrected nonzero support witness.
3. New `NSTriadKNR650Rational345NonzeroSupportRound848Exact.agda` converts original Boolean `modeEqual!=true` into the existing `Z3.NonZeroMode` record, and supplies the source-correct nonzero support theorem from **ALREADY EXISTING** `NSTriadKNR650Rational345MixedOutputSupportRound848Exact.mixedFilterEmptyAtInactiveNonzero`. No duplicate 36-case proof. This actually inhabits the corrected `R846.InactiveActiveFibreEmpty` and constructs the original R837 direct physical modal same-object record through `R846.Evaluate`.

## Critical reuse / what is not missing anymore

- Existing R848 has **already** proved the 36 seed-pair output Minkowski support classification on the literal Z³ source.
- Existing R849 **already** proves exact original R692 global coherent work from source-matched active rows, using nonzero output support.
- Existing R850 **already** instantiates real physical snapshot coherent-work, production and dissipation and proves the *instantaneous* R829 canonical signed rate strictly negative.
- Existing R853 **already** derives the general same-source R815 signed-rate pointwise normal form.
- Therefore claiming "R829D vector table is the last NS finite obstacle" is stale. No need to redo R829B/C, original 36-case support or R849 global aggregation.

The decisive remaining **finite NS lane** is R833/R853's original real finite ODE/trajectory/time integration: source Round71 RHS to a true complete-real solution, selected R828/R829 physical rate identity along that same trajectory, and a strict negative time integral. The R823 reserve relationship must still be checked as an actual necessary implication for the physical global-regularity target. This is NOT a proof of the Clay regularity theorem for all 3D data.

## Authority and local commands

```bash
python3 scripts/check_ns_r846_zero_mode_and_nonzero_support.py
bash scripts/check_ns_r846_r848_zero_mode_local.sh
# Pinned Agda 2.9, AGDA_BIN or Nix as configured by the repository.
```

The exact integer test was independently reproduced and PASS. The new Agda code is SOURCE-WRITTEN only. No Agda/Nix executable exists in this tool container; exact-head kernel, transitive import and safety receipt remain OPEN. Do not use CI to infer local acceptance. Do not promote NS B global regularity or NS external C/D from this local repair.

Attribution: original DASHI R436 and R848 support/zero-output proofs and finite physical triad compiler; this new work only constructs a sourced false-premise counterexample, corrected zero/nonzero disjunction, Boolean-to-NonZeroMode transport, and R837 modal same-object consumer.
