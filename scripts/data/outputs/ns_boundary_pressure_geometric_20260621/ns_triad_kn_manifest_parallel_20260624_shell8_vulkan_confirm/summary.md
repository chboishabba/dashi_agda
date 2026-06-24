# NS Triad K_N Manifest Summary

- status: `ok`
- c0: `0.25`
- rows: `4`
- missing/failed rows: `0`

## Branch Counts

- `finite_anchor_mixed_low_frame`: `3`
- `tail_internal_low_frame`: `1`

## Rows

| backend | N | K | eta | branch | lambda | R_full | R_finite | R_tail | D | worst shell | tail worst |
|---|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| vulkan-matvec | 8 | 5 | 0.25 | finite_anchor_mixed_low_frame | 0.210015 | 0.210015 | 0.215732 | 0.467434 | 12.8425 | 1 | 8 |
| vulkan-matvec | 8 | 6 | 0.25 | finite_anchor_mixed_low_frame | 0.198968 | 0.198968 | 0.205609 | 0.452393 | 13.8244 | 8 | 8 |
| vulkan-matvec | 8 | 7 | 0.25 | finite_anchor_mixed_low_frame | 0.167402 | 0.167402 | 0.175018 | 0.436222 | 15.1235 | 8 | 8 |
| vulkan-matvec | 8 | 7 | 0.4 | tail_internal_low_frame | 0.195442 | 0.195442 | 0.391223 | 0.195607 | 23.5976 | 8 | 8 |
