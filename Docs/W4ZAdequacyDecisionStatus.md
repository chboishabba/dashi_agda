# W4 Z-Peak Adequacy Decision Status

Date: `2026-05-06`
Status: `blocked; non-promoting`
Owner: `Laplace / W4 adequacy first decision`

## Decision

W4 Z-peak adequacy cannot be decided from the current local repository state.
No real accepted or replacement Drell-Yan luminosity authority packet exists
locally, and no adapter output from such a packet exists locally.

The exact gate is:

```text
missingAcceptedDYLuminosityConventionAuthority
missing accepted luminosity vector ell_i per bin from a real accepted provider packet
```

## Inspected Surfaces

- `scripts/run_w4_z_peak_adequacy.py`
- `scripts/dy_luminosity_from_authority_packet.py`
- `Docs/W4ZAdequacyReceiptTemplate.md`
- `Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md`
- `Docs/AcceptedDYLuminosityConventionAuthorityResponse.md`
- `Docs/AcceptedDYLuminosityConventionAuthoritySubmission.md`
- `Docs/DYAuthorityProviderResponseChecklist.md`
- `Docs/DYAuthorityProviderResponseStatus.md`
- `logs/research/dy_authority_adapter_smoke.json`
- `scripts/data/authority_packet.example.json`

## Local Evidence

The t21/t22 public-route and local payload binding audit is:

```text
logs/research/w4_z_peak_t21_t22_public_intake_20260513.json
```

It records DOI JSON-LD success for t21/t22, HTTP 403 from this environment for
the tested HEPData title/numeric JSON/CSV download routes, and checksum-bound
use of the existing local t21/t22 CSV payloads.

The dirty Z-peak anchor runner artifact is:

```text
logs/research/w4_z_peak_anchor_dirty_run_20260513.json
```

It records `chi2/dof = 298.8462841768543`, projection digest
`7fa002539fef1dc9bd51b22c1d512b4ed7be85417a3afb6f1e9992bbdc3dbdc1`, and no W4
promotion.

Euler's 2026-05-13 shared PDF preflight also emitted:

```text
logs/research/w4w5_pdf_ct18_candidate_run_20260513.json
logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json
```

Their SHA-256 digests are respectively
`7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f` and
`a67318e71b4c18fde71597874f93aa28ab020557f230dd3843f807e40545b88d`. The
preflight found no real LHAPDF runtime and no local MSHT20 grid, so no W4
accepted per-bin luminosity vector could be emitted from a real LHAPDF/MSHT
run.

The only local authority-shaped packet is:

```text
scripts/data/authority_packet.example.json
```

It has `status: insufficient`, empty W4 per-bin luminosities, and an explicit
governance note saying it is a fail-closed example packet, not accepted
authority.

The only local adapter artifact is:

```text
logs/research/dy_authority_adapter_smoke.json
```

That artifact records smoke behavior only. Its accepted-shaped success case
uses temporary `/tmp` fixtures and states that a real external/provider
authority packet is still missing.

## Probe Results

Adapter probe:

```text
python scripts/dy_luminosity_from_authority_packet.py --authority-packet scripts/data/authority_packet.example.json
```

Result:

```text
exit 51
authority packet invalid: authority status must be accepted or replacement
```

W4 adequacy harness probe:

```text
python scripts/run_w4_z_peak_adequacy.py \
  --accepted-dy-authority scripts/data/authority_packet.example.json \
  --measurement-csv scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv \
  --measurement-column Ratio \
  --prediction-csv scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv \
  --prediction-column Ratio \
  --luminosity-csv scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv \
  --luminosity-column Ratio \
  --sigma-csv scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv \
  --sigma-column Ratio \
  --output /tmp/w4_z_peak_adequacy_probe.json
```

Result:

```text
exit 40
blocked: missing accepted DY luminosity convention authority: authority file is missing required fields: pdfSet, lhapdfId, gridChecksum, scaleConvention, rapidityConvention, massBinRule, flavourWeights, interpolationIntegration, source, provenance
```

The W4 harness correctly stops before adequacy calculation.

## Consequence

No `logs/research/w4_z_peak_adequacy_decision*.json` artifact was emitted
because there is no real accepted DY adapter output to consume.

`DASHI/Physics/Closure/W4ZAdequacyReceipt.agda` was not edited because the
receipt cannot be honestly populated under the current gate.

No W4 promotion is available.
