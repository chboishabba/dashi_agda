# Clay Sprint 43 NS 3D Truth Bridge Repair

Date: 2026-06-04

This records the repair of the Sprint 43 Navier-Stokes 3D truth evidence lane.
The prior N32 run consumed the new dashiCFD 3D truth artifact, but the harness
used its default dyadic shell convention and therefore reported `k_star = 0`
instead of the generator metadata value `k_star = 7`.

The repaired harness now records:

- `shell_convention`
- `velocity_source`
- `k_star_source`
- `bridge_ratio_status`
- live progress/ETA from `--progress-every`

The dashiCFD truth generator progress line now also reports ETA.

## Artifact Roots

- pre-repair N32 run:
  `Docs/Images/clay-analytic-sprint/sprint43_ns3d_seed0/`
- repaired N32 run:
  `Docs/Images/clay-analytic-sprint/sprint43_ns3d_seed0_repaired/`
- repaired N64 seed 0 run:
  `Docs/Images/clay-analytic-sprint/sprint43_ns3d_N64_seed0_repaired/`
- repaired N64 seed 1 run:
  `Docs/Images/clay-analytic-sprint/sprint43_ns3d_N64_seed1_repaired/`

Sibling dashiCFD truth artifacts:

- `../dashiCFD/outputs/truth3d/ns3d_N32_seed0.npz`
- `../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz`
- `../dashiCFD/outputs/truth3d/ns3d_N64_seed1.npz`

## Commands

```bash
python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N32_seed0.npz \
  --out-dir Docs/Images/clay-analytic-sprint/sprint43_ns3d_seed0_repaired

python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz \
  --progress-every 100 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint43_ns3d_N64_seed0_repaired

python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed1.npz \
  --progress-every 100 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint43_ns3d_N64_seed1_repaired
```

The N64 truth generator commands were:

```bash
python3 scripts/make_truth_3d.py \
  --N 64 --steps 120 --save-every 10 --dt 0.001 --nu0 0.001 \
  --seed 0 --out outputs/truth3d/ns3d_N64_seed0.npz \
  --update-manifest --progress-every 40

python3 scripts/make_truth_3d.py \
  --N 64 --steps 120 --save-every 10 --dt 0.001 --nu0 0.001 \
  --seed 1 --out outputs/truth3d/ns3d_N64_seed1.npz \
  --update-manifest --progress-every 40
```

## Results

| run | shell convention | velocity source | K_star | high shells | sup C_K | inf budget | verdict |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| pre-repair N32 seed0 | unset/dyadic default | reconstructed | 0 | 5 | `1.3824440948122683e12` | `-0.14626118467981306` | `NO_PROMOTION_DIAGNOSTIC_ONLY` |
| repaired N32 seed0 | `integer-radius` | `velocity_snapshots` | 7 | 21 | `2.5866198098439114e11` | `-0.025720401595074865` | `NO_PROMOTION_BUDGET_FAIL` |
| repaired N64 seed0 | `integer-radius` | `velocity_snapshots` | 7 | 49 | `1.8439088483009247e11` | `-0.0009951511974450934` | `NO_PROMOTION_BUDGET_FAIL` |
| repaired N64 seed1 | `integer-radius` | `velocity_snapshots` | 7 | 49 | `1.4923579402546648e10` | `-0.0017769118671760108` | `NO_PROMOTION_BUDGET_FAIL` |

The repaired runs clear the prior shell metadata blocker: `k_star_source` is
`meta_json.k_star`, `K_star = 7`, and high-shell support passes.  They do not
promote.  The measured high-shell budget remains below the required `> 1/2`
threshold, and the current residue classifier often leaves `R_plus_K = 0`,
making the adjusted bridge ratio unavailable on those rows.

## Boundary

This is a diagnostic evidence repair and scale-up only.  It does not prove the
physical bridge

```text
Q_K <= C * R_K^+ * concentration_K^theta
```

and does not supply actual ternary particle lineage estimates.  No NS, Gate3,
YM, terminal theorem, or Clay promotion flag changes.

## Follow-Up Audit

The next residue-definition pass is recorded in
`Docs/ClaySprintFortyThreeNSResidueSemanticsAudit.md`.  It shows that relaxed
positive-stretch semantics make adjusted bridge ratios finite on most repaired
N32/N64 rows, but those semantics are diagnostic-only and all audited budgets
still fail the required `> 1/2` gate.
