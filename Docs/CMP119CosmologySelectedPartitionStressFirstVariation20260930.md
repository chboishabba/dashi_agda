# CMP119 / expanding universe: first partition-stress producer (2026-09-30)

## Scientific correction: one-point stress is **not** an arbitrary connected insertion

The earlier ten-slot owner CMP119TenLiteralFiniteMeasureReadoutsExact.agda computes C_h = (D_h N) Z - N(D_h Z) for a normalized insertion observable N/Z. Thus C_h/Z² = D_h(N/Z). That is **not** generally the gravitational one-point stress. The stress obtained by varying the matter effective action Gamma_m[g] = -log Z[g] comes first from D_h log Z[g] = (D_h Z)/Z, subject to a fixed covariant metric convention, gauge-fixing, renormalization, determinant/volume factors, and physical continuation. The former connected response is useful for a further variation of the stress if N represents an actual stress insertion, but it must not be renamed T00.

For a finite Euclidean source with action S[g,U] and potentially metric-dependent reference measure nu_g, the properly differentiated unnormalized weight has

    D_h[rho_g dnu_g] = rho_g dnu_g (D_h log[dnu_g/dnu_ref] - D_h S[g,U]),

and therefore

    D_h log Z = [int rho (reference-score_h - D_h S) dnu_ref] / Z.

This is the object **first** required for stress. Its physical Lorentzian meaning is not yet established.

## New Agda construction

DASHI/Physics/Foundations/CMP119CosmologyPartitionStressFirstVariationExact.agda consumes the PREEXISTING CMP119ClassicalWilsonTenMetricVariationExact.agda and CMP119ClassicalWilsonDiagonalMetricVariationExact.agda. It has no new invented six-plane identity. The native Wilson diagonal components come from six selected plaquette-orientation energies; the complete action derivative then adds E, R-operation, boundary and vacuum derivatives and the metric-reference score. `partitionDerivative` is one real finite Haar-integral expression over the existing PhysicalFiniteYMMeasure density. Its first Euclidean Weyl trace is proven pointwise equal to the reference-score trace minus the complete non-Wilson metric trace, because the classical d=4 Wilson four-diagonal action variation vanishes.

Under a pointwise fixed-Haar reference-score proof and the native rational integration laws, the additional `fixedHaarPartitionDerivativeIsExistingGibbsDZ` theorem identifies this computed full-action partition derivative with the existing `NZ.denominatorDerivative` from `CMP119GibbsFiniteMeasureNZDNDZReductionExact` (using the constant insertion only to instantiate the old data carrier). This is **not** an assertion that the connected expectation derivative of the constant insertion equals the one-point stress.\n\nThe pinned `PhysicalFiniteYMMeasure` still exposes a free `partitionFunction` and a free `divide` operation. Consequently its `formalNormalizedPartitionResponse` is **only a formal candidate** until `partitionFunction = int density`, positivity, real rational division, and actual metric differentiability are established. The script's finite quadrature, by contrast, explicitly computes `Z` and a rigorous enclosure of `D_h Z / Z` for that **discrete** model.\n\nThis does **not** construct the published CMP119 source E/R/B/vacuum derivatives: those are named explicit input functions. The rational finite-measure carrier does not supply the actual nonlinear SU(2) Haar integration, its differentiability or the renormalized Lorentzian metric functional.

DASHI/Physics/Foundations/CMP119CosmologyWeakYMAccelerationObstructionExact.agda transports the **existing** weak-YM active-stress nonnegativity into a dimensionless positive-G, Lambda=0 FLRW acceleration sign test: if the source actually satisfies that YM-only Lorentzian decomposition, its matter-driven acceleration is nonpositive. An accelerating same-source model must have a sufficiently positive independent Lambda contribution, or an independently derived extra stress sector outside the no-go assumptions. This does not prove that the full CMP119 quantum theory satisfies that weak-YM decomposition.

## New executable matrix-based source experiment

scripts/grqft_su2_six_plane_partition_metric_source.py computes the actual SU(2) bare Wilson costs from six **explicit rational-quaternion matrix plaquette evaluations**. With positive bare beta=4/g0², it calculates

    S_W = sum_{01,02,03,12,13,23} beta * W_plane,
    D_aa S_W = S_W/2 - sum_{plane containing a} beta * W_plane,

directly from six link products, and checks sum_a D_aa S_W=0 for each row.

A complete action must ALSO provide source E, R, B, vacuum base values and metric derivatives on each row. Reference-measure metric scores are explicit, and the code verifies D_h int dnu_g 1 = 0 for the supplied probability quadrature. It rigorously encloses exp(-S_full) by **exact rational alternating-series bounds** (with controlled argument halving), builds exact rational enclosures for Z, D_aa Z and D_aa log Z, and checks both a naive four-interval trace and a more informative correlated trace integral. Results include input SHA256 and provenance.

Important limitations:

* The configuration rows are **discrete quadrature** over explicitly supplied SU(2) matrices, not an independently certified product-Haar quadrature on SU(2)^links. They are not a proof of the selected CMP119 continuum quantum measure.
* Six faces are supplied as oriented link quartets; validation proves local SU(2) unit norm, not a complete common-lattice shared-link and gauge constraint system.
* Each E/R/B/vacuum value and derivative in the input is independently supplied. No implicit zero-sector assumption is permitted; tests use explicitly zero toy sectors, or a clearly marked **externally chosen** toy volume term.
* Strict positivity and enclosure of the **discrete** partition are certified arithmetically. Neither the bare Wilson-only result nor a supplied toy volume coefficient establishes dark energy. Wick/OS timelike continuation, physical counterterm subtraction, and convergence remain open.
* This script computes only the four diagonal Euclidean responses; six off-diagonal responses remain with the native ten-slot Agda owner and cannot be set to zero without source symmetry derivation.

Regression suite: scripts/test_grqft_su2_six_plane_partition_metric_source.py exercises the exact SU2 Wilson derivative, classical four-dimensional trace-zero obstruction, nontrivial real plaquette, toy volume source, nonunit link rejection, missing six-plane/four-sector rejection, probability normalization and exponential interval bounds. The original toy vacuum term is not a prediction of the CMP119 quantum state.

## Next physical obligations, in exact order

1. **Source-native rows**. Build actual selected CMP119 effective density and metric-dependent full five-sector action at a definite cutoff from the SAME literal SU(2) lattice field and published equation-level source conventions; do not populate E/R/B/vacuum with unverified toy inputs.
2. **Certified Haar integration and first variation**. Produce gauge-consistent, source-controlled product Haar quadrature with error bounds for Z and all first metric derivatives, or prove the requisite analytic integration and uniform domination theorem directly. Certify derivative of the reference/gauge fixing and its normalization.
3. **Selected finite-to-continuum renormalization**. Prove regularity, finite/cutoff-uniform metric derivative estimates and counterterm control sufficient to commute the selected limit with variation. Fix a cosmological renormalisation condition so a vacuum-like stress term is not counted in both Lambda and Gamma_m.
4. **Lorentzian energy and pressure**. Establish analytic continuation/Ward identities and construct T00 and three equal pressures from the SAME renormalized state. Verify conservation and homogeneous/isotropic state assumptions.
5. **Source-driven geometry**. Solve Friedmann constraint + acceleration + continuity for that source and fixed initial data, then derive H(z), w(z) and actual independent observables. Do not use the old DiscreteWarpedEinsteinMatterModel as evidence of quantum source identity: it encodes its vacuum-like source.

**Status:** code committed on Agda PR #1050; neither an exact-head Agda kernel receipt nor a successful exact-head Python workflow run has been returned. Test files are source-written, not certified passing. This is progress in physically relevant first-variation evaluation, NOT a proof of cosmic acceleration, quantum gravity, or the Clay YM existence/mass-gap result.


## 2026-09-30 continuation: assembled R144 D1 replaces free sector callbacks

New owner `CMP119CosmologyR144CompleteActionPartitionResponseExact.agda` reuses the existing R142/R144 fact that the selected generated-action first variation is the whole finite localized D1 sum. Its `completeLocalizedActionDerivative` is therefore computed from the exact finite action and selected tangent, then packaged into the existing Gibbs denominator derivative. `completeActionPartitionDerivativeIsLiteralHaarD1` identifies the resulting DZ with the literal finite-measure integral of `-rho * D1(S_complete)`. The same D1 scalar is also welded back to the selected canonical CMP119 stress insertion through the pre-existing R144-to-R119/R118 bridge.

This is stronger than separately postulating metric derivatives for E, R, B and vacuum when only their **assembled source derivative** is required. It does not decompose that D1 back into independently source-certified sector derivatives, and it does not prove the finite action is the published CMP119 complete action at every cutoff.

New owner `CMP119CosmologyPhysicalFinitePartitionAuthorityExact.agda` isolates another previously hidden gap in the pinned finite-measure carrier: `partitionFunction` and `divide` are arbitrary fields. The authority package requires (Z=int rho), (Z>0), and the actual rational quotient law before a normalized DZ/Z response may be treated as such. It deliberately does not call that ratio a proved derivative of log Z without a metric-family differentiability theorem.

New owner `CMP119CosmologySelectedDensityR144PartitionWeldExact.agda` composes R124 with the assembled R144 response. At a selected RG scale, the Balaban source density mapped by R124 is proved equal to the literal physical finite measure used by the cosmology DZ calculation, so the calculation can no longer silently switch measures between source provenance and stress evaluation.

The remaining physical frontier is now: instantiate the R124 density-to-physical-measure weld and R132/R144 generated action with the actual selected CMP119 source, prove finite product-Haar normalization/differentiability and uniform bounds, then pass the one-point response through renormalization and Lorentzian continuation before solving FLRW.
