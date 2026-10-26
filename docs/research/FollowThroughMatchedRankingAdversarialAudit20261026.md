# Follow Through matched-ranking audit correction

2026-10-26. Independent research direction Johl Brown; OpenAI ChatGPT AI-assisted implementation. Original Follow Through findings remain owned by Abt Associates, House et al., Engelmann/Becker/St. Pierre and other named original researchers; APM and derivative Instagram reporting separate.

## What was fixed
Earlier `follow_through_source_bound_sensitivity.py` matched site/cohort across model rows but allowed different weights at the same site/cohort, so two programmes' means could target different sample mixes even with identical site labels. The tool now rejects these combinations and reports all exactly tied leaders rather than a single arbitrary rank winner. Two synthetic fixtures check the failures.

## Crucial limits
Even equal weights and matching site/cohort labels do **not** establish exchangeable model assignment, baseline equivalence, an unbiased comparison, or preservation of the original Abt estimator. A model can be assigned to different schools within a nominal site. Measurement times, instrument forms, adjustment variables, grade/curricular exposure and source-specific missingness matter. The current script's positive rankings are descriptive only and require independent statistical reproduction, not proof of efficacy.

## Next original-source gates
- Extract the Abt IV-A and IV-B/C original numerical tables with exact analysis unit, site/model assignment, cohort/test/wave, grayout flag, preschool imbalance, reliability adjustment and standard errors.
- Distinguish the exact 1977 aggregate analytic estimand from later House/Becker/St. Pierre alternative reanalyses; do not treat the no-data demo regression as an empirical sensitivity result.
- Preserve each programme model-count scope (22 selected, 17 detailed-report, 13 evaluated according to House) without forcing the figures to agree.
- Run a policy-source audit independently from treatment-effect ranking: documents, decisions, publication/withholding, allocations and specific dates; no national causal-decline promotion.
- Alice Brown/LOOM/ESD reusable as prior art only; no unapproved collaborative ESD integration.

No CI requested. New test cases are source-written, not executed here. Agda kernel remains unverified. No original historical numerical observations have been admitted.
