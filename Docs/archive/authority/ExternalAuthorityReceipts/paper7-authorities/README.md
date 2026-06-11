# Paper 7 External Authority Receipt Bundle

Last refreshed: 2026-05-20.

This bundle records external authority surfaces for Paper 7. These artifacts
are authority receipts only; they do not promote internal DASHI proofs.

## Local PDFs

| Authority | Local file | Source URL | SHA256 |
|---|---|---|---|
| `Authority.Clay` | `clay-yangmills-jaffe-witten.pdf` | `https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf` | `3558403ca14c11e382f73a09e548222708540bfdf478cf96aa11c52d43e23e09` |
| `Authority.ContinuumGR` | `ambrose-singer-1953-holonomy.pdf` | `https://www.ams.org/journals/tran/1953-075-03/S0002-9947-1953-0063739-1/S0002-9947-1953-0063739-1.pdf` | `377a56b2c1fd6141ad556e80bf7af4a53c688682b80cc73460ce9bed64227edc` |
| `Authority.W4` Higgs | `pdg-2025-higgs-boson.pdf` | `https://pdg.lbl.gov/2025/reviews/rpp2025-rev-higgs-boson.pdf` | `7a94228faa2bd277199de57428528d0ae280609320d4fe997d04876d77cf3407` |
| `Authority.W4` CKM | `pdg-2025-ckm-matrix.pdf` | `https://pdg.lbl.gov/2025/reviews/rpp2025-rev-ckm-matrix.pdf` | `a0a78578971f38ff89c6fc5579bc608de41ec383a205dc25cba1d26f7145610a` |
| `Authority.W4` constants | `pdg-2025-physical-constants.pdf` | `https://pdg.lbl.gov/2025/reviews/rpp2025-rev-phys-constants.pdf` | `596a9ed34c582e92a13c1fff7263a498844ea7e301511417587ecfb191516e6f` |

## DOI-backed Authority Targets

| Authority | Citation target | Stable locator | Receipt role |
|---|---|---|---|
| `Authority.DHR` / DR duality | Sergio Doplicher and John E. Roberts, "Endomorphisms of C*-algebras, cross products and duality for compact groups", Annals of Mathematics 130 (1989), 75-119. | `https://doi.org/10.2307/1971477` | Compact group duality/reconstruction authority. |
| `Authority.DHR` / field algebra | Sergio Doplicher and John E. Roberts, "Why there is a field algebra with a compact gauge group describing the superselection structure in particle physics", Communications in Mathematical Physics 131 (1990), 51-107. | `https://doi.org/10.1007/BF02097680` | Field-algebra/gauge-group reconstruction authority for DHR sectors. |
| `Authority.ContinuumGR` | W. Ambrose and I. M. Singer, "A theorem on holonomy", Transactions of the American Mathematical Society 75 (1953), 428-443. | `https://doi.org/10.1090/S0002-9947-1953-0063739-1` | Continuum holonomy algebra / curvature-form authority. |
| `FunctionalAnalysisAuthority` | T. Kato, *Perturbation Theory for Linear Operators*. | `https://doi.org/10.1007/978-3-662-12678-3` | Functional-analysis and operator-perturbation authority. |
| `AQFTModularAuthority` | R. Haag, *Local Quantum Physics*. | `https://doi.org/10.1007/978-3-642-61458-3` | AQFT and modular-theory authority. |
| `WaldStressEnergyAuthority` | R. M. Wald, *General Relativity*. | `https://doi.org/10.7208/chicago/9780226870373.001.0001` | GR curvature/stress-energy convention authority. |

## Search Terms For Missing Full-Text Acquisition

- `Doplicher Roberts Endomorphisms of C*-algebras cross products duality compact groups PDF`
- `Doplicher Roberts why there is a field algebra compact gauge group PDF`
- `Doplicher Roberts 10.1007/BF02097680`
- `Kobayashi Nomizu Foundations of Differential Geometry infinitesimal holonomy curvature`
- `parallel transport infinitesimal parallelogram curvature holonomy expansion O(epsilon^3)`
- `Hairer Lubich Wanner Geometric Numerical Integration Lie group methods holonomy curvature`

The active frozen `Authority.ContinuumGR` source is now Ambrose-Singer 1953.

## Receipt Boundaries

- `Authority.DHR` may justify importing the DR/Tannaka reconstruction theorem, not
  the DASHI-specific verification of DR hypotheses.
- `Authority.ContinuumGR` may justify the continuum small-loop/holonomy limit,
  not the DASHI discrete carrier's convergence into that limit.
- `Authority.W4` may supply empirical constants, units, CKM phases, and PDG
  value surfaces, not internal derivation of those values.
- `Authority.Clay` records the official Yang-Mills mass-gap problem and rules;
  it does not discharge the mass gap.
