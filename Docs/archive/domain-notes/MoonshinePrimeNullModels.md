## Moonshine Prime Null Models (Lane 2)

This lane defines the **non-accident** baseline tests that demonstrate the observed empirical correlation between the moonshine primes (`SSP`) and the attractor structure is not explained by simple random effects.

### Null model suite

1. **Random partition nulls**  
   - Redistribute the 15 primes into random bins that preserve the marginal counts per bin size but not the original ordering or prime identity.  
   - Re-run the Hecke scan and basin graph extraction using these synthetic partitions.  
   - Collect the `Sig15` statistics and compare towards the real arrangement via permutation p-values over the basin severity distribution.

2. **Random ternary-state nulls**  
   - Swap Monte Carlo initialization states with random ternary vectors of equal length while keeping the MDL pipeline parameters unchanged.  
   - Track whether the resulting attractors still concentrate on the canonical prime signatures; null success requires no significant peak both in lifespan and PCA distance from the real prime-centers.

3. **Matched basin graph nulls**  
   - Shuffle adjacency connections in the inferred attractor graph while preserving each node's degree sequence.  
   - Use this matched graph to recompute the eigen/motif pipeline; null success is defined as the random graph failing to produce the same motif partition overlap as the real graph (statistically significant divergence measured via KL-divergence of motif frequencies).

4. **PCA/control pipelines**  
   - Apply PCA to the normalized prime exponent lattice and rerun the MDL heuristic on the projected components instead of the raw exponents.  
   - Compare the MDL descent profiles (length drops, plateau durations) between the true data and randomized PCA rotations; null failure is declared when randomized PCA retains the same sharp dropping/plateau signature as the real program.

### First executable harness contract

The first implementation surface for this lane is narrower than the full
research target. It should operate on one normalized
`MoonshinePrimeState`/`MoonshinePrimeObservable` payload and compute
schema-level nulls:

- random partition over the 15-prime support,
- random ternary carrier states with matched length,
- matched support-count / basin-label controls,
- randomized carrier rotations as a surrogate control for later PCA lanes.

For each null, the harness should report:

- the observed target-prime score,
- the null distribution summary,
- an empirical `p`-value,
- and a boolean `passes_null`.

### Stop condition

If any null model passes (i.e., a randomized version reproduces the observed prime-specific basin concentration, motif overlap, or MDL descent signature at better than `p = 0.05`), stop the current proof lane and report the failure upstream. The null should pass first before any downstream moonshine claim can proceed; in the failure case, the lane must supply the randomized seed and summary measurements so the global story can be adjusted (either by refining the null or by downgrading the claim). 
