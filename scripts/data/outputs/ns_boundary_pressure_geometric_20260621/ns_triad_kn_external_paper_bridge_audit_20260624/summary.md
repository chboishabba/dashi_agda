# NS triad K_N external paper bridge audit

Candidate-only, fail-closed audit of the Fields ACL paper and the Shahmurov reduction paper.

## Fields ACL

- pdf: `/home/c/Downloads/D663F306-4179-11F1-A876-C7C17E70DEF5.pdf`
- pages: `84`
- candidate-only: `true`
- theorem promotion: `false`
- full-NS promotion: `false`
- Clay promotion: `false`

Keywords checked:
- `Angular Cancellation Lemma`: `true`
- `Theorem 4.27`: `true`
- `unit-width shells`: `true`
- `G(k,p)`: `false`
- `resonant set`: `true`

Snippets:
- `Angular Cancellation Lemma`: establish global regularity for the three-dimensional incompressible Navier–Stokes equations on the periodic domain T3 for arbitrary smooth initial data. The proof introduces three new structural mechanisms. First, the Angular Cancellation Lemma (ACL, Theorem 4.27) provides a sharp bound on the local cascade interaction within each Littlewood– Paley shell, establishing that azimuthal oscillation of the Leray-projected coupling kernel produces deterministic geom
- `Theorem 4.27`: the three-dimensional incompressible Navier–Stokes equations on the periodic domain T3 for arbitrary smooth initial data. The proof introduces three new structural mechanisms. First, the Angular Cancellation Lemma (ACL, Theorem 4.27) provides a sharp bound on the local cascade interaction within each Littlewood– Paley shell, establishing that azimuthal oscillation of the Leray-projected coupling kernel produces deterministic geometric cancellation.
- `unit-width shells`: emark 2.4 (Lattice Geometry and Shell Scaling). The spectrum is the discrete lattice Z3 . While the Littlewood–Paley decomposition (Definition 2.3) uses dyadic frequency blocks, the closure argument in Section 4 employs unit-width shells 𝑆𝑗 = {𝑘 ∈ Z3 : 𝑗 ≤ |𝑘| < 𝑗 + 1}, for which #𝑆𝑗 = 𝑂(𝑗 2 ) (spherical surface area, thickness 1). This distinction is essential: for dyadic shells of thickness ∼ 2𝑗 , the lattice count #𝑆𝑗 ∼ 23𝑗 is volumetric, which would
- `G(k,p)`: [not found]
- `resonant set`: .5 The Angular Cancellation Lemma Remark 4.18 (Central geometric mechanism). The results of this subsection constitute the primary geometric contribution of this paper. The geometric factor decomposition (Lemma 4.20), resonant set geometry (Lemma 4.22), amplitude-geometry decoupling (Lemma 4.24), and Theorem 4.27 (the assembled ACL bound) together establish a new geometric mechanism in the theory of incompressible fluid dynamics, formalised and m

## Shahmurov reduction

- pdf: `/home/c/Downloads/2606.07875v1.pdf`
- pages: `68`
- candidate-only: `true`
- theorem promotion: `false`
- full-NS promotion: `false`
- Clay promotion: `false`

Keywords checked:
- `Theorem 2.2`: `true`
- `Corollary 2.3`: `true`
- `axisymmetric-with-swirl`: `true`
- `reduction theorem`: `true`
- `companion axisymmetric-with-swirl endpoint theorem`: `false`

Snippets:
- `Theorem 2.2`: a field-level equivariance statement by using a quantitative axis-equivariance defect; Appendix K and Appendix L record the absolute estimates behind the flux-hull routing. The reader may first follow the proof through Theorem 2.2, treating these estimates as lemmas, and then return to the appendices for the line-by-line inequalities. Relation to the literature The proof belongs to the classical regularity tradition initiated by Leray’s construc
- `Corollary 2.3`: uction hulls generate a named output or a strict active descendant, and closed positive-production hulls are ruled out by the kinetic-energy Liouville theorem. The remaining terminal endpoint is axisymmetric with swirl. Corollary 2.3 (Reduction of global regularity to the axisymmetric-with-swirl endpoint). If smooth finite-energy axisymmetric Navier–Stokes solutions with arbitrary swirl are globally regular, then smooth finite-energy three-dimension
- `axisymmetric-with-swirl`: is a reduction theorem: any hypothetical first singularity of a general three-dimensional solution generates, after scale normalization, threshold selection, and endpoint extraction, a terminal singular endpoint in the axisymmetric-with-swirl class. Thus a proof of the companion axisymmetricwith-swirl endpoint theorem closes the corresponding full three-dimensional finite-energy regularity statement. The proof is organized around the scalar vorticity-amplitu
- `reduction theorem`: e data; vorticity; vortex stretching; flux-closed active hulls; Nash inequality. MSC 2020. 35Q30, 76D05, 35B65, 35B44, 42B37. 1 Contents 1 Introduction: the reduction problem 4 2 Equations and the singular-endpoint reduction theorem 6 3 Packets, threshold bands, and outputs 7 4 The amplitude identity 9 5 Zero production and Nash–Liouville 10 6 Positive production and active rebase 11 7 Flux-closed active hulls 12 7.1 Solenoidal hull opera
- `companion axisymmetric-with-swirl endpoint theorem`: [not found]

## Bridge conclusion

- Fields ACL is a candidate carrier for the SchurResidueScale off-diagonal block question.
- Shahmurov is a candidate carrier for the endpoint-reduction / residence bridge, conditional on the missing AS theorem.
- Neither paper upgrades theorem, full-NS, or Clay authority.
