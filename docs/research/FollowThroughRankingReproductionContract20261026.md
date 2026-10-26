# Follow Through — source-bound ranking sensitivity executable

2026-10-26. Independent Follow Through research by Johl Brown (direction) with OpenAI ChatGPT (AI-assisted code). Original historical findings attributed to original evaluators, critics and reporters. No ESD team integration.

Tool: `scripts/follow_through_source_bound_sensitivity.py`; regression: `tests/test_follow_through_source_bound_sensitivity.py`.

Run:
```
python scripts/follow_through_source_bound_sensitivity.py sourced_original_effects.csv
python -m unittest discover -s tests -p 'test_follow_through_source_bound_sensitivity.py'
```

Expected columns: `source_id,page,model,site,cohort,domain,instrument,specification,effect,weight,status`. Use decimal effect and strictly positive weight. `status` only `inspected-original` or `verified-transcription`. Missing cells, duplicate keys, unsupported status and invalid numbers are rejected, not converted to zero. No historical CSV or invented effect estimates are included.

The script separates reliability-uncorrected and reliability-corrected ANCOVA specifications and only compares model means on an intersection of site/cohort pairs with identical outcome instrument/domain/specification. It reports rankings as *descriptive-only*, not significance tests, causal treatment effects, or reproduced Abt statistics.

Caution: even common sites/cohorts and a common outcome are insufficient for equal estimands when model-specific analysis weights, selection, attrition, demographics or follow-up differ. An actual comparison must inspect the original weights and covariance adjustment and compute uncertainty. The two-site synthetic fixture is only a regression guard, not Follow Through evidence.

Latest original-author sources: St. Pierre (1978), doi:10.1177/0193841X7800200303, reports that pretest reliability correction changed some conclusions, not necessarily DI rank; Becker and Gersten (1982), doi:10.3102/00028312019001075, report five-site later academic outcomes. APM (2026) basic-skills ranking is based on chart tracing without published values; do not use it as a numerical table.

The highest-value remaining evidence payment is the source-inspected original 1977 site×model×instrument×specification results. This tool makes the *lack* of those results observable instead of disguising it with plausible numbers. Optional Alice/LOOM/ESD one-way prior-art reuse remains allowed; adoption by collaborative ESD team requires approval.
