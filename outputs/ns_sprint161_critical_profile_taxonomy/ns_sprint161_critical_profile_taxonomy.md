# Sprint 161 Critical Profile Taxonomy

- Decision: `critical_profile_taxonomy_inventory_with_closed_rows_separated_from_open_rows`
- Row count: `8`
- Known closed rows: `2`
- Symmetric closed rows: `2`
- Open rows: `4`
- FullClay: `False`
- Profile exhaustion for full Clay: `False`
- Validation passed: `True`

## Closed Rows

| profile_id | profile_class | closure_group | taxonomy_status |
| --- | --- | --- | --- |
| zero | zero | KNOWN_CLOSED | closed_known_trivial_profile |
| type_i_self_similar | Type-I self-similar | KNOWN_CLOSED | closed_known_type_i_self_similar_obstruction |
| axisymmetric_no_swirl | axisymmetric no swirl | SYMMETRIC_CLOSED | closed_symmetric_no_swirl_regular_class |
| axisymmetric_with_swirl_gamma_bounded_symmetric | axisymmetric with swirl Gamma-bounded/symmetric | SYMMETRIC_CLOSED | closed_symmetric_gamma_bounded_swirl_class |

## Open Rows

| profile_id | profile_class | closure_group | taxonomy_status |
| --- | --- | --- | --- |
| non_axisymmetric_type_i | non-axisymmetric Type-I | OPEN | open_non_axisymmetric_type_i_profile_class |
| non_axisymmetric_type_ii | non-axisymmetric Type-II | OPEN | open_non_axisymmetric_type_ii_profile_class |
| discretely_self_similar | discretely self-similar | OPEN | open_discrete_self_similarity_profile_class |
| ancient_bounded_non_symmetric | ancient bounded non-symmetric | OPEN | open_ancient_bounded_non_symmetric_profile_class |

## O/R/C/S/L/P/G/F

- O: Worker 4 owns the Sprint161 critical-profile taxonomy emitter.
- R: Separate closed profile classes from open critical-profile classes without promoting full Clay NS.
- C: Python stdlib emitter writes normalized rows, summary, CSV, Markdown, and manifest.
- S: Sprint160 governance keeps full Clay false while scoped symmetric classes may be isolated as closed.
- L: profile class -> closure group -> evidence boundary -> Full Clay false guard.
- P: Use this artifact as the lane 4 taxonomy for critical-profile accounting.
- G: Validation requires exactly eight profile classes, closed/open separation, and every Full Clay flag false.
- F: Open non-symmetric and Type-II/DSS profile classes remain non-exhausted for full Clay.
