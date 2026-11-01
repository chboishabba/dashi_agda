# W5 T45 Correction Receipt Template

Date: `2026-05-06`
Status: `template; gated; non-promoting`
Owner: `W5 t45 PDF-correction lane`

This template prepares the W5 t45 correction receipt after an accepted
Drell-Yan luminosity convention exists.  It does not close W5 and it does not
turn the local CT18 probes into authority.

## Gate

The runner is:

```text
scripts/run_w5_t45_pdf_correction.py
```

It requires a provider JSON packet.  If the packet is absent or invalid, the
runner fails closed before computing a target claim.

## Provider Packet Shape

```json
{
  "status": "accepted",
  "accepted_dy_luminosity_convention": {
    "pdf_set": "CT18NLO or accepted replacement",
    "lhapdf_id": "14400/member 0 or accepted replacement",
    "grid_checksum": "sha256:...",
    "factorization_scale": "Q = M or accepted replacement",
    "rapidity_window": "accepted Y/eta convention",
    "mass_bin_integration": "accepted CMS-SMP-20-003 50-76, 76-106, 106-170 GeV rule",
    "flavour_weight_rule": "accepted DY charge/flavour rule",
    "source": "DOI/arXiv/manual/collaboration source",
    "provenance": "provider, command/API, inputs, checksums, timestamp"
  },
  "luminosities": {
    "L_M45_Y45": 0.0,
    "L_M43_Y43": 0.0
  },
  "tolerance": 1e-10
}
```

`status` may be `accepted` or `replacement`.  Any other value is rejected.
`L_M43_Y43` must be nonzero.

## Computation

```text
R45/R43 = L(M45,Y45) / L(M43,Y43)
target = 0.8804486068
pass = abs(R45/R43 - target) <= tolerance
```

The success surface is an emitted `W5T45Correction` receipt with `pass: true`.
The negative surface is an emitted receipt with `result:
negative_obstruction`, naming the accepted convention and the numeric gap.

## Rejected Local Probes

These remain rejected diagnostics, not authority:

| Probe | Result | Target |
|---|---:|---:|
| fixed-`x` CT18 candidate | `1.0506681065158017` | `0.8804486068` |
| `t45/z_peak` rapidity-window candidate | `0.7514043986785174` | `0.8804486068` |
| `t45/t43` denominator hypothesis | `0.3348750784006896` | `0.8804486068` |

## Governance

No W5 promotion is made here.  No target pass claim is valid without accepted
convention provenance, provider luminosity method, and tolerance.

The exact remaining gap in canonical local state is:

```text
missingAcceptedDYLuminosityConventionAuthority
missing provider luminosity method for L(M45,Y45) and L(M43,Y43)
```
