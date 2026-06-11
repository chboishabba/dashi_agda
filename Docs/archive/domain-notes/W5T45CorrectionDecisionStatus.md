# W5 T45 Correction Decision Status

Date: `2026-05-06`
Lane: `W5 t45 correction first decision`
Status: `blocked-no-accepted-dy-adapter-output`
Promotion: `none`

## Decision

No W5 t45 correction receipt can be emitted locally.

The required upstream gate is not satisfied:

```text
missingAcceptedDYLuminosityConventionAuthority
missing accepted/replacement DY adapter output compatible with W5
missing provider luminosity method for L(M45,Y45) and L(M43,Y43)
```

## Evidence Inspected

- `scripts/run_w5_t45_pdf_correction.py` requires a provider packet with
  `status = accepted` or `status = replacement`, a complete
  `accepted_dy_luminosity_convention`, and finite `L_M45_Y45` / `L_M43_Y43`.
- `Docs/W5T45CorrectionReceiptTemplate.md` states the same gate and preserves
  local CT18 probes as rejected diagnostics, not authority.
- `scripts/dy_luminosity_from_authority_packet.py` is only an adapter from an
  already accepted/replacement authority packet to downstream W4/W5 artifacts.
- `logs/research/dy_authority_adapter_smoke.json` is smoke evidence only.  Its
  accepted-shaped output came from temporary `/tmp` fixtures and explicitly
  says a real external/provider authority packet is still missing.
- `logs/research/accepted_dy_authority_adapter_blocked.json` records that no
  real local accepted/replacement DY authority packet was found.
- `Docs/DYAuthorityProviderResponseStatus.md` records the current canonical
  response as awaiting provider response and non-promoting.
- `DASHI/Physics/Closure/AcceptedDYLuminosityConventionAuthorityReceipt.agda`
  remains constructorless for accepted authority in the canonical local state.
- Euler's 2026-05-13 W4/W5 PDF preflight now records that system LHAPDF runtime
  is available (`/usr/bin/lhapdf`, `/usr/bin/lhapdf-config`, and system Python
  `lhapdf` at `6.5.5`) and repo-local CT18NLO resolves with
  `LHAPDF_DATA_PATH=/usr/share/lhapdf/LHAPDF:$PWD/scripts/data/pdf`. The repo
  `.venv` still lacks Python `lhapdf`, and no local MSHT20 grid was found. The
  provider-authority obstruction artifact is
  `logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json`
  SHA-256 `082448674db69767aff1897f7fb66054a6dbc3a70b86f31813185a6a2c10fd41`.
  The fresh CT18 equivalent-table candidate run is
  `logs/research/w4w5_pdf_ct18_candidate_run_20260513.json`
  SHA-256 `7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f`.

## Commands Run

```text
sed -n '1,260p' scripts/run_w5_t45_pdf_correction.py
sed -n '1,240p' Docs/W5T45CorrectionReceiptTemplate.md
rg -n "DY|Drell|luminosity|accepted|authority|adapter|W5|t45|T45" Docs scripts logs DASHI/Physics/Closure -g '!monster/**'
sed -n '1,280p' scripts/dy_luminosity_from_authority_packet.py
sed -n '1,220p' logs/research/dy_authority_adapter_smoke.json
sed -n '1,220p' scripts/data/authority_packet.example.json
sed -n '1,240p' Docs/DYAuthorityProviderResponseStatus.md
sed -n '1,220p' Docs/AcceptedDYLuminosityConventionAuthorityResponse.md
sed -n '1,220p' DASHI/Physics/Closure/AcceptedDYLuminosityConventionAuthorityReceipt.agda
sed -n '1,220p' DASHI/Physics/Closure/W4W5AcceptedDYLuminosityConventionDiagnostic.agda
sed -n '1,240p' logs/research/accepted_dy_authority_adapter_blocked.json
rg -n '"status"\s*:\s*"(accepted|replacement)"|"authorityStatus"\s*:\s*"(accepted|replacement)"|"w5ProviderPacket"|"accepted_example"|sourcePacket|smoke-recorded-not-promoted|computed-not-promoted|insufficient|awaiting provider response' logs scripts/data Docs -g '*.json' -g '*.md'
find logs/research scripts/data -type f \( -name '*w5*provider*json' -o -name '*dy*adapter*.json' -o -name '*authority*.json' -o -name '*t45*correction*.json' \) -print
python scripts/dy_luminosity_from_authority_packet.py --authority-packet scripts/data/authority_packet.example.json
python scripts/run_w5_t45_pdf_correction.py --provider-packet scripts/data/authority_packet.example.json
```

Observed fail-closed exits:

```text
dy_luminosity_from_authority_packet.py on scripts/data/authority_packet.example.json -> exit 51
run_w5_t45_pdf_correction.py on scripts/data/authority_packet.example.json -> exit 45
```

## Consequence

No `logs/research/w5_t45_correction_decision*.json` artifact was written,
because no real accepted DY adapter output exists locally.  No
`DASHI/Physics/Closure/W5T45CorrectionReceipt.agda` edit is permitted under
this state.

The 2026-05-13 system-LHAPDF CT18 candidate rerun remains non-promoting:
fixed-`x` ratio `1.0506160645962357`, rapidity-window `t45/z_peak`
`0.7513909431520515`, and rapidity-window `t45/t43`
`0.33485771276970683`; none is an accepted correction receipt.
