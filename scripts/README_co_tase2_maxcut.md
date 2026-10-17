# Co1/4TaSe2 max-cut executable sequence

1. Install `requirements-co-tase2.txt`.
2. Run `python3 scripts/co_tase2_bloch_symmetry.py` for covariance/cocycle/nodal receipts.
3. Acquire an independent BNS 194.268 operation JSON and run `python3 scripts/co_tase2_bns_operation_audit.py <json>`.
4. Probe or externally acquire the UCF dataset.  Once `.ibw` files are available, run `python3 scripts/co_tase2_arpes_ibw_ingest.py <dir> --manifest <json>`.
5. Bind channel/calibration metadata before using `co_tase2_arpes_peak_fit.py`; do not infer spin channels or kz from wave position alone.
6. Run `scripts/check_co_tase2_maxcut.sh` in an environment with Agda + stdlib for the umbrella kernel receipt.
