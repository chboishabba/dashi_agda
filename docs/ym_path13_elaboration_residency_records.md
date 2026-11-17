# Yang–Mills Path-13 Elaboration Residency and Ring-Solver Records

**Date:** 2026-09-11  
**Target:** `DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda`  
**Related Pull Request:** PR #849 (`agent/ym-path13-fibre-oom-followup`)  
**Historical Precursor:** PR #839 (`agent/ym-path13-fibre-native-lift`)

---

## 1. Provenance and Source Attribution

This empirical elaboration investigation tracks the formal machine certification
of the scalar coercivity and Poincaré floor for four-dimensional Yang–Mills
lattice gauge theory on block size $L = 13$:

1. **Primary Physical Sources:**
   - Tadeusz Bałaban, *"Propagators and Renormalization Transformations for
     Lattice Gauge Theories. I"*, Communications in Mathematical Physics **95**
     (1984), 17–40. DOI: [10.1007/BF01240221](https://doi.org/10.1007/BF01240221).
   - Tadeusz Bałaban, *"Renormalization Group Approach to Lattice Gauge Field
     Theories. I. Generation of Effective Actions in a Small Field Approximation
     and a Coupling Constant Renormalization in Four Dimensions"*,
     Communications in Mathematical Physics **109** (1987), 249–301.
     DOI: [10.1007/BF01215223](https://doi.org/10.1007/BF01215223).
2. **Matrix Analysis and LDL^T Decomposition Method:**
   - Roger A. Horn and Charles R. Johnson, *"Matrix Analysis"*, 2nd edition,
     Cambridge University Press, 2012.
     DOI: [10.1017/CBO9781139020411](https://doi.org/10.1017/CBO9781139020411).
3. **Repository Architecture:**
   - Formalization lane: Fibre-native relation lift (`AtomicGlobalFibreLiftExact`,
     `BalabanFiniteSumRelationFibreLiftExact`,
     `BalabanPath13ZeroMeanFibrePoincareLiftExact`).
   - Scalar algebra isolation: `BalabanOpaqueGlobalAlgebraExact`.

---

## 2. Executive Summary of Findings

Across the Yang–Mills Path-13 elaboration profiling tranches on Agda 2.9:

1. **The Out-Of-Memory (OOM) Failure Has Been Resolved:**
   - The previous runs suffered fatal OOM crashes (>32 GB RAM ceiling) caused
     by unbounded metavariable constraint search and ring-solver reflection over
     transverse-coordinate lists and four-axis torus sums.
   - Decoupling list recursion into pre-proved relation observers
     (`SumLift.sumRationalMonotoneViaFibre`), isolating scalar identities into
     carrier-free lemmas (`OpaqueAlgebra.scaleFourSum`, `scaleSumSubtractCommutes`,
     `subtractShiftCancel`), and renaming shadowing parameters reduced heap
     allocation dramatically.
   - **Directional Energy Contraction (`ym-path13-directional`):**
     Completed with **Exit 0** in **261.8 seconds**, max heap residency of
     **5.72 GB**, 425 metas, and max open constraints = 2.
2. **The Residual Bottleneck is a Pure CPU Ring-Solver Reflection Loop:**
   - Two consecutive long-running jobs on `BalabanPath13FourAxisPhysicalPoincareExact.agda`
     exhibited flat, stable memory (~1.1 to 1.7 GB RSS, no leaks), but spent
     **12h 58m** and **20h+** respectively at 98–99% CPU inside
     `DASHI/Physics/YangMills/BalabanPath13GeneratedLDLCertificate.agda`.
   - The culprit is `path13LDLDecompositionRaw = ℚRing.solve-∀`, which attempts
     to verify a 12-variable rational quadratic polynomial identity with large
     fractional pivots (up to 18-digit integers) via Horner tree reflection.

---

## 3. Detailed Profile Records

### Record 1: The 13-Hour Run (2026-09-09 to 2026-09-10)

* **Run Directory:** `.cache/dashi-agda29/elaboration-profiles/20260909-214722-poincare-13/`
* **Log File:** `agda-20260909-214729-DASHI__Physics__YangMills__BalabanPath13FourAxisPhysicalPoincareExact.agda.log`
* **Target File:** `DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda`
* **Command Line:**
  ```bash
  /nix/store/jv7cagyh8wm4cw8j94z5s2ffqmjv10dq-Agda-2.9.0-bin/bin/agda \
    +RTS -s -RTS --no-libraries --no-default-libraries -j1 \
    -i . -i DCHoTT-Agda -i vendor/bishop -i cubical \
    -i /home/c/.cache/dashi-agda29/agda-stdlib-experimental/src \
    -WnoUnsupportedIndexedMatch --profile=all \
    DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda
  ```
* **Start Time:** 2026-09-09 21:47:29
* **Termination Time:** 2026-09-10 10:45:49
* **Elapsed Time:** **12:58:20** (12 hours, 58 minutes, 20 seconds)
* **Exit Status:** `Dead` (terminated before `time.txt` / `summary.tsv` writeout)
* **OS / Hardware Metrics:**
  - IO Read: 4.76 GiB; IO Write: 213 KiB
  - User: `c`; Threads: 2; Nice: -4
  - Memory: Flat, bounded around ~1.1 to 1.4 GB
* **Elaboration Sequence:**
  1. `DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact`: Checked (843 metas, 0 open constraints).
  2. `DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact`: Checked (564 metas, 2 open constraints).
  3. `DASHI.Physics.YangMills.BalabanNormalizedFourAxisMartingaleExact`: Checked (280 metas, 2 open constraints).
  4. `DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate`: Entered at line 87 of log; remained computing `ℚRing.solve-∀` for the full ~13 hours until termination.

---

### Record 2: The 20-Hour+ Run (2026-09-10 to Present)

* **Run Directory:** `.cache/dashi-agda29/elaboration-profiles/20260910-113028-ym-poincare-13/`
* **Log File:** `agda-20260910-113038-DASHI__Physics__YangMills__BalabanPath13FourAxisPhysicalPoincareExact.agda.log`
* **Target File:** `DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda`
* **PID:** 1335235 (orchestrated by `scripts/profile_agda_elaboration_residency.sh`)
* **Start Time:** 2026-09-10 11:30:38
* **Elapsed Wall Time (as of 2026-09-11 07:51):** **20:20:42** (20 hours, 20 minutes, 42 seconds)
* **Elapsed CPU Time:** **20:05:06**
* **Process State:** `R<l` (actively running at **98.7% CPU** utilization)
* **Memory Residency:** **1,709,860 KiB (~1.71 GB RSS)**, 5.2% of total machine RAM.
* **Elaboration Sequence:**
  1. `DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact`: Checked (553 metas, 2 open constraints, 2550 comparisons).
  2. `DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact`: Checked (409 metas, 2 open constraints, 1840 comparisons).
  3. `DASHI.Physics.YangMills.BalabanNormalizedFourAxisMartingaleExact`: Checked (280 metas, 2 open constraints, 1585 comparisons).
  4. `DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate`: Entered at 11:30:48; actively executing `path13LDLDecompositionRaw = ℚRing.solve-∀`.

---

## 4. Architectural Analysis: Why 12-Variable RingSolver Hangs

### The Complexity Scaling of `ℚRing.solve-∀`

In `DASHI/Physics/YangMills/BalabanPath4GeneratedLDLCertificate.agda` ($L=4$, $N=3$ independent coordinates $a, b, c$):
* The polynomial identity is over 3 variables.
* The standard library reflection tactic builds Horner normal form trees of depth 3.
* Elaboration completes in $<1$ second.

In `DASHI/Physics/YangMills/BalabanPath13GeneratedLDLCertificate.agda` ($L=13$, $N=12$ independent coordinates $a, b, c, d, e, f, g, h, i, j, k, l$):
* The quadratic identity equates:
  $$\sum_{i=0}^{11} (y_{i+1} - y_i)^2 \quad\equiv\quad \frac{1}{18} \sum_{i=0}^{12} y_i^2 + \sum_{k=0}^{11} d_k (\ell_k(y))^2$$
  where $y_{12} = -\sum_{i=0}^{11} y_i$.
* Expanded out, there are $\binom{12+2-1}{2} = 78$ pairwise monomials.
* The pivot coefficients $d_k$ and linear form fractions $\ell_k$ have rational denominators with up to 18 decimal digits (e.g., $4514842591049713 / 240833315580756192$).
* During reflection, Agda's internal RingSolver represents polynomials as nested Horner trees:
  $$\text{Poly}_N = \text{List } (\text{Poly}_{N-1})$$
* Combining, multiplying, and reducing Horner trees across 12 variables produces an exponential number of rational arithmetic reductions and normalizations.
* **Result:** Memory remains low (~1.7 GB) because terms are normalized sequentially, but the single-core CPU workload scales astronomically, exceeding 20 hours.

---

## 5. Remediation Roadmap for Path-13 LDL Closure

1. **Option A: Staged Monomial Coefficient Decomposition**
   Rather than asking `ℚRing.solve-∀` to normalize the entire 12-variable multivariate quadratic form in a single monolithic reflection step, break the identity into individual coordinate/monomial equations or factor the triangular system $L D L^T$ column by column.
2. **Option B: Recursive Path Assembly (Fibre Folding on LDL)**
   Derive the length-$L$ LDL quadratic floor inductively from a path-contraction recurrence:
   $$(P_{k+1} \to P_k) + \text{local pivot update}$$
   so that RingSolver only ever sees 2 to 3 variables at any single induction step.
3. **Option C: Pre-Computed Matrix Equality Witness via Integer Scaling**
   Clear denominators upfront by cross-multiplying with the common denominator of the pivots, reducing the certificate verification from arbitrary rational GCD reduction to exact integer polynomial equivalence.
