# Clay Sprint Sixty Four NS Source-Budget Exhaustion / CKN Route

Sprint 64 records the post-Sprint 63 governance state for the NS lane.

## Verdict

The tested DASHI NS source-budget route is diagnostically exhausted on current
artifacts:

```text
normalized packet action: non-additive, Jensen-inflated
raw action shell summability: flat
action-preserving shell reassignment: flat
raw-red direction coherence proxy: incoherent
cross-shell parent-budget contractivity: noncontractive
```

This is a negative diagnostic closure only. It does not prove blowup,
regularity, or any Clay/NS claim.

## Norm Switch

The next NS route is CKN/ESS-aligned local critical concentration.  The CFD
preflight producer computes the velocity component:

```text
r^-2 integral_Q |u|^3 dx dt
```

over parabolic block windows.  Current truth artifacts do not contain pressure
snapshots, so the compatible `|p|^(3/2)` term is missing and no CKN
epsilon-regularity certificate follows.

## dashiCFD Artifact

```bash
cd ../dashiCFD
python3 scripts/ns_sprint64_ckn_local_critical_concentration_audit.py \
  --inputs outputs/truth3d/ns3d_N32_seed0_gpu.npz \
           outputs/truth3d/ns3d_N32_seed1_gpu.npz \
           outputs/truth3d/ns3d_N32_seed2_gpu.npz \
           outputs/truth3d/ns3d_N32_seed3_gpu.npz \
           outputs/truth3d/ns3d_N64_seed0_gpu.npz \
           outputs/truth3d/ns3d_N64_seed1_gpu.npz \
  --out-dir outputs/sprint64_ckn_local_critical_concentration_gpu_audit \
  --scales 8 16 \
  --epsilon-critical 0.01 \
  --plateau-fraction 0.5
```

Observed route:

```text
LOCAL_CRITICAL_CONCENTRATION_PRESSURE_RECONSTRUCTION_MISSING
```

The N32/N64 six-run surface reports:

```text
row_count = 18720
ascended_fraction = 0.9642628205128205
max_local_concentration_ratio = 53.704773818909864
```

N128 seed0 and dense N64 seed0 also route as pressure-missing.

## Governance

No Clay/NS promotion follows.  The open gates are pressure reconstruction,
epsilon-threshold calibration, the local critical quantity bridge, the suitable
weak solution bridge, and no-finite-time-blowup.
