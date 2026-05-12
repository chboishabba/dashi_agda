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
