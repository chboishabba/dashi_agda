# NS Sprint 131 Localized Viscous Comparison Audit

- audit_id: `ns_sprint131_localized_viscous_comparison_audit`
- lemma: `LocalizedViscousLowerComparison`
- scaling_window: `1 < alpha < 3/2`
- beta_rule: `beta=alpha-1`
- delta_rule: `delta=tau^beta`
- omega_rule: `Omega=tau^-alpha`
- viscous_term: `nu*Omega/delta^2`
- source_upper_bound: `source<=C_src*tau^-1`
- ratio_lower_bound: `viscous/source>=C*nu*tau^(-3*beta)`
- exact_ratio_exponent: `-3*beta`
- viscous_lower_comparison_closed: `true`
- ratio_diverges: `true`
- supports_hou_luo_ns_obstruction: `true`
- clay_navier_stokes_promoted: `false`
- complete: `true`
- exit_code: `0`

## Algebra

With alpha = 1 + beta and delta = tau^beta:

`nu*Omega/delta^2 = nu*tau^(-alpha-2*beta) = nu*tau^(-1-3*beta)`.

Using the Worker1 source upper form `source <= C_src*tau^-1`, the normalized lower comparison is:

`viscous/source >= C*nu*tau^(-3*beta)`.

For beta > 0 and nu > 0 this lower bound diverges as tau approaches 0.

## Rows

| row | alpha | beta | tau | nu | viscous | source | ratio lower | diverges | closed |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | 11/10 | 1/10 | 1/10 | 1 | tau^-(13/10) | tau^-(1) | 1.99526231497 | true | true |
| r001 | 11/10 | 1/10 | 1/10 | 1/10 | tau^-(13/10) | tau^-(1) | 0.199526231497 | true | true |
| r002 | 11/10 | 1/10 | 1/10 | 1/100 | tau^-(13/10) | tau^-(1) | 0.0199526231497 | true | true |
| r003 | 11/10 | 1/10 | 1/100 | 1 | tau^-(13/10) | tau^-(1) | 3.98107170553 | true | true |
| r004 | 11/10 | 1/10 | 1/100 | 1/10 | tau^-(13/10) | tau^-(1) | 0.398107170553 | true | true |
| r005 | 11/10 | 1/10 | 1/100 | 1/100 | tau^-(13/10) | tau^-(1) | 0.0398107170553 | true | true |
| r006 | 11/10 | 1/10 | 1/1000 | 1 | tau^-(13/10) | tau^-(1) | 7.94328234724 | true | true |
| r007 | 11/10 | 1/10 | 1/1000 | 1/10 | tau^-(13/10) | tau^-(1) | 0.794328234724 | true | true |
| r008 | 11/10 | 1/10 | 1/1000 | 1/100 | tau^-(13/10) | tau^-(1) | 0.0794328234724 | true | true |
| r009 | 11/10 | 1/10 | 1/10000 | 1 | tau^-(13/10) | tau^-(1) | 15.8489319246 | true | true |
| r010 | 11/10 | 1/10 | 1/10000 | 1/10 | tau^-(13/10) | tau^-(1) | 1.58489319246 | true | true |
| r011 | 11/10 | 1/10 | 1/10000 | 1/100 | tau^-(13/10) | tau^-(1) | 0.158489319246 | true | true |
| r012 | 5/4 | 1/4 | 1/10 | 1 | tau^-(7/4) | tau^-(1) | 5.6234132519 | true | true |
| r013 | 5/4 | 1/4 | 1/10 | 1/10 | tau^-(7/4) | tau^-(1) | 0.56234132519 | true | true |
| r014 | 5/4 | 1/4 | 1/10 | 1/100 | tau^-(7/4) | tau^-(1) | 0.056234132519 | true | true |
| r015 | 5/4 | 1/4 | 1/100 | 1 | tau^-(7/4) | tau^-(1) | 31.6227766017 | true | true |
| r016 | 5/4 | 1/4 | 1/100 | 1/10 | tau^-(7/4) | tau^-(1) | 3.16227766017 | true | true |
| r017 | 5/4 | 1/4 | 1/100 | 1/100 | tau^-(7/4) | tau^-(1) | 0.316227766017 | true | true |
| r018 | 5/4 | 1/4 | 1/1000 | 1 | tau^-(7/4) | tau^-(1) | 177.827941004 | true | true |
| r019 | 5/4 | 1/4 | 1/1000 | 1/10 | tau^-(7/4) | tau^-(1) | 17.7827941004 | true | true |
| r020 | 5/4 | 1/4 | 1/1000 | 1/100 | tau^-(7/4) | tau^-(1) | 1.77827941004 | true | true |
| r021 | 5/4 | 1/4 | 1/10000 | 1 | tau^-(7/4) | tau^-(1) | 1000 | true | true |
| r022 | 5/4 | 1/4 | 1/10000 | 1/10 | tau^-(7/4) | tau^-(1) | 100 | true | true |
| r023 | 5/4 | 1/4 | 1/10000 | 1/100 | tau^-(7/4) | tau^-(1) | 10 | true | true |
| r024 | 7/5 | 2/5 | 1/10 | 1 | tau^-(11/5) | tau^-(1) | 15.8489319246 | true | true |
| r025 | 7/5 | 2/5 | 1/10 | 1/10 | tau^-(11/5) | tau^-(1) | 1.58489319246 | true | true |
| r026 | 7/5 | 2/5 | 1/10 | 1/100 | tau^-(11/5) | tau^-(1) | 0.158489319246 | true | true |
| r027 | 7/5 | 2/5 | 1/100 | 1 | tau^-(11/5) | tau^-(1) | 251.188643151 | true | true |
| r028 | 7/5 | 2/5 | 1/100 | 1/10 | tau^-(11/5) | tau^-(1) | 25.1188643151 | true | true |
| r029 | 7/5 | 2/5 | 1/100 | 1/100 | tau^-(11/5) | tau^-(1) | 2.51188643151 | true | true |
| r030 | 7/5 | 2/5 | 1/1000 | 1 | tau^-(11/5) | tau^-(1) | 3981.07170553 | true | true |
| r031 | 7/5 | 2/5 | 1/1000 | 1/10 | tau^-(11/5) | tau^-(1) | 398.107170553 | true | true |
| r032 | 7/5 | 2/5 | 1/1000 | 1/100 | tau^-(11/5) | tau^-(1) | 39.8107170553 | true | true |
| r033 | 7/5 | 2/5 | 1/10000 | 1 | tau^-(11/5) | tau^-(1) | 63095.734448 | true | true |
| r034 | 7/5 | 2/5 | 1/10000 | 1/10 | tau^-(11/5) | tau^-(1) | 6309.5734448 | true | true |
| r035 | 7/5 | 2/5 | 1/10000 | 1/100 | tau^-(11/5) | tau^-(1) | 630.95734448 | true | true |

## Control Card

- O: Worker 2 owns only the localized viscous comparison audit script and generated output directory.
- R: Check the 1<alpha<3/2, beta=alpha-1, delta=tau^beta scaling relation for LocalizedViscousLowerComparison.
- C: Deterministic Python audit emits rows JSON, summary JSON, and Markdown report.
- S: Rows are generated from fixed rational alpha, tau, and nu grids; no external state is read.
- L: Omega=tau^-alpha and nu*Omega/delta^2 give tau^-(alpha+2*beta)=tau^-(1+3*beta).
- P: Against Worker1 source<=C_src*tau^-1, record viscous/source>=C*nu*tau^(-3*beta).
- G: The ratio diverges as tau->0 for every beta>0 and nu>0, supporting the Hou-Luo NS obstruction.
- F: The audit does not promote Clay Navier-Stokes; it closes only this localized comparison ledger.
