# ns_sprint116_crow_obstruction_scaling

Deterministic Crow-route obstruction scaling calculator.

Formula surface:

- obstruction_ratio = (delta_over_b ** 2) / log(1 / delta_over_b)
- reference_flux_budget_over_e0 values are supplied comparison ratios
- normalized columns divide by the delta_over_b = 0.40 row

Limit-to-zero check: true.
Option B Crow route obstructed: true.
Clay promoted: false.

| delta/b | obstruction ratio | reference flux budget / e0 | obstruction normalized | reference normalized |
| --- | --- | --- | --- | --- |
| 0.4 | 0.17461706687 | 0.175 | 1 | 1 |
| 0.3 | 0.0747525190574 | 0.075 | 0.428094002479 | 0.428571428571 |
| 0.2 | 0.0248533973824 | 0.025 | 0.142330860482 | 0.142857142857 |
| 0.1 | 0.00434294481903 | 0.004 | 0.024871250542 | 0.0228571428571 |
| 0.05 | 0.000834520501738 | 0.0008 | 0.00477914625814 | 0.00457142857143 |
