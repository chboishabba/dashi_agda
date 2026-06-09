# ns_sprint119_alignment_persistence_budget

Deterministic alignment persistence budget calculator.

Formula surface:

- alignment integral = integral_0^T compressive_alignment_strength(t) dt
- constant-strength model: alignment_integral = strength * duration
- kstar_support_threshold = 1
- clay_support_threshold = 2

Kstar budget met rows: 4.
Clay budget met rows: 1.
Non-circular source established: false.
Persistent alignment existence closed: false.
Clay promoted: false.

| strength | duration | alignment integral | kstar budget met | clay budget met | classification |
| --- | --- | --- | --- | --- | --- |
| 0.1 | 0.1 | 0.01 | false | false | support_budget_not_met |
| 0.1 | 0.25 | 0.025 | false | false | support_budget_not_met |
| 0.1 | 0.5 | 0.05 | false | false | support_budget_not_met |
| 0.1 | 1 | 0.1 | false | false | support_budget_not_met |
| 0.1 | 2 | 0.2 | false | false | support_budget_not_met |
| 0.25 | 0.1 | 0.025 | false | false | support_budget_not_met |
| 0.25 | 0.25 | 0.0625 | false | false | support_budget_not_met |
| 0.25 | 0.5 | 0.125 | false | false | support_budget_not_met |
| 0.25 | 1 | 0.25 | false | false | support_budget_not_met |
| 0.25 | 2 | 0.5 | false | false | support_budget_not_met |
| 0.5 | 0.1 | 0.05 | false | false | support_budget_not_met |
| 0.5 | 0.25 | 0.125 | false | false | support_budget_not_met |
| 0.5 | 0.5 | 0.25 | false | false | support_budget_not_met |
| 0.5 | 1 | 0.5 | false | false | support_budget_not_met |
| 0.5 | 2 | 1 | true | false | kstar_support_budget_met |
| 0.75 | 0.1 | 0.075 | false | false | support_budget_not_met |
| 0.75 | 0.25 | 0.1875 | false | false | support_budget_not_met |
| 0.75 | 0.5 | 0.375 | false | false | support_budget_not_met |
| 0.75 | 1 | 0.75 | false | false | support_budget_not_met |
| 0.75 | 2 | 1.5 | true | false | kstar_support_budget_met |
| 1 | 0.1 | 0.1 | false | false | support_budget_not_met |
| 1 | 0.25 | 0.25 | false | false | support_budget_not_met |
| 1 | 0.5 | 0.5 | false | false | support_budget_not_met |
| 1 | 1 | 1 | true | false | kstar_support_budget_met |
| 1 | 2 | 2 | true | true | clay_support_budget_met |
