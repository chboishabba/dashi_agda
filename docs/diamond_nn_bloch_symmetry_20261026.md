# 2026-10-26: Diamond nearest-neighbour Bloch same-carrier max-cut

## Original objective and external authority
The broad thread started with a crystallographic D4h (4/mmm)
classification/finite symmetry proof task, broadened to real
tetragonal and diamond crystal space groups, atomic 369, quantum
Hamiltonians, NV defect and observable tests. This cut implements
the **first nonconstant Bloch Hamiltonian** attached to the ACTUAL
native infinite diamond FCC two-sublattice carrier, not a borrowed
ternary cube with equal cardinality.

External original research/prior art:
- IUCr *International Tables for Crystallography*, diamond Fd-3m
  No.227. https://onlinelibrary.wiley.com/iucr/itc/Ac/ch2o3v0001/sgtable2o3o227/
- L. Fu, C. L. Kane and E. J. Mele, *Topological Insulators in Three
  Dimensions*, Physical Review Letters 98, 106803 (2007), and
  the subsequent Phys. Rev. B 76, 045302 (2007) diamond-lattice
  nearest-neighbour/spin-orbit formulation, DOI
  https://doi.org/10.1103/PhysRevB.76.045302.
  This PR implements only a **spinless, uniform nearest-neighbour**
  two-sublattice restriction; it does NOT formalise their spin-orbit,
  topological invariants or bulk bandgap conclusions.
- Diamond geometry (fcc prim vectors and shifted B motif)
  is pre-existing and now local to #1261:
  `DiamondFccPrimitiveGlideExact.agda`.
- Shared Gaussian complex-integer Q4 diffraction phase arithmetic
  pre-exists in the PR's `DiamondEightSiteStructureFactorExact.agda`.
- Optics/Fourier pixel PR #1272 retains ownership of its
  actual optical experiment, phase/reference and
  same-device commuting squares.
- NV spin/hardware PRs #1262, #1269, #1270 retain source authors,
  spin-one obstruction, calibrated source/measurement status and
  electron/nuclear logical-register distinctions.

## Actual implementation
`DiamondNearestNeighbourBlochExact.agda`:
- Recover FOUR tetrahedral A→B neighbours in the existing ideal
  infinite FCC site carrier, at quarter-cell coordinates
  (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1).
- `gamma(q)` is the exact Gaussian integer sum of FOUR unit-modulus
  hopping phases on the restricted q ∈ (Z/4Z)^3 momentum carrier.
  Do not confuse it with the EIGHT-site diffraction amplitude.
- The ideal two-sublattice spinless Hermitian operator is
  H(q)=[[0,gamma(q)],[conjugate(gamma(q)),0]],
  with source-written 64-case identities
  H(q)^2=norm2(gamma(q)) I.
- Five cubic generators (XY, YZ, flipX,flipY,flipZ) have explicit
  gamma and norm2 covariance proof cases (5×64 each).
  Six permutations and eight sign choices cover all 48 cubic
  signed-coordinate transformations via compositional lemmas.
  This is a *physical basis* action, not 48 independently copied
  equalities on a tensor of arbitrary species.
- `DiamondBlochCubicCovarianceExact.agda` strengthens it to
  full 48-operation 2×2 matrix covariance: even sign parity
  preserves gamma, odd sign parity conjugates gamma and
  H(gq)=sigma_x H(q) sigma_x. Reuses generator/transitivity
  and 8×64 closed Agda cases for sign parity.
- `DiamondBlochSpectralEvidenceBoundaryExact.agda` formalises
  two non-entailments:
  (i) `norm² gamma` does NOT recover the complex gamma phase,
  even on 64 samples (e.g. 000 versus 111 share norm² 16 but
  gamma values 4 versus -4i); the required phase reference
  is an independent consumer.
  (ii) `m²+norm² gamma` retains full cubic *scalar*
  covariance under A/B staggered onsite mass m, but
  a uniform A/B scattering contrast breaks the actual
  sublattice-exchanging diamond glide (proved by the
  previous `DiamondSublatticeContrastStructureFactorExact`).
  Spectral-value equality is therefore weaker than an actual
  crystallographic symmetry or a same-Hamiltonian intertwinement.

## Independent exact computational audit
`scripts/check_diamond_nearest_neighbour_bloch_exact.py`
cross-checks quarter-cell FCC primitive actual neighbour coordinates,
Hermitian matrix square, all 48×64 finite cubic transformations,
explicit parity conjugation, and the sampled spectral distribution:
- squared offdiagonal hopping 0 on 48 momentum phase classes;
- squared offdiagonal hopping 16 on 16 classes.
This is mathematically consistent with four equal tetrahedral
nearest-neighbour bonds on a two-sublattice spinless ideal host.
It is NOT diamond's measured band gap and NOT the NV spin spectrum.
A separate independent local Python exact check was executed.

## Latest related donor refresh
- #1272: optical Fourier-pixel bidirectional original experiment,
  phase ambiguity versus intensity, conditional measurement
  commuting squares. Reuse *methodology*, not apparatus facts.
- #1269: SI-typed source metrology, calibrated axial NV electron
  model, nuclear/electron register identity and photon counting.
- #1270: original Gemsheim et al. 2026 three-nuclear-qubit
  ambient Grover experiment; manufacturer's aggregate/core-count
  claims separately evidence-gated.
- #1262: spin-one Sz² cyclic-label no-go remains valid.
- #1249: native 27→26→13×2 carrier and nonwrapping grid
  obstruction; source owner, not to be replicated.
- #1239: modular F3^3 path-cube/Jordan non-identity warnings.

## Exact status / next Pareto gate
Implemented as source-written Agda proof terms, but **not yet
Agda kernel checked**. Local Python finite mathematical diagnostics
pass, and no CI gate is required. Source existance, soundness,
kernel acceptance and measured evidence are separate stages.

The missing full material symmetry gate is **the actual 192-operation
nonsymmorphic Seitz-to-Hilbert Bloch gauge representation**, including
origin conventions and fractional translation Bloch phases,
not merely the 48 point-group square-norm invariance. Then:
- prove a genuine symmetry action on a source-matched Hamiltonian,
  add multi-orbital/spin-orbit/strain, and recover the PR #1262
  spin-one label and field-breaking obstructions;
- connect to the PR #1269 same-device SI quantities, pulse/channel
  and photon observation, with independently measured calibration;
- use #1272 optical phase reference/identifiability methodology only
  when the actual optical hardware and field are supplied;
- generalise to authoritative 230 space groups and real data
  without pretending a 64-sample toy band model completes physics.

Attribution applies at every level. Mathematical crystal symmetry
and the Fu–Kane–Mele diamond model are classical/external prior art;
Gemsheim/SAXON claims are independently sourced experimental/vendor
claims; new finite adapter, regressions and proofs are PR #1261 work.
