# Base369 27−1, Griess 1990 Albert fine grading and exact Hamiltonian Pareto cut (2026-10-24)

## Source-root priority / attribution

**NEW PRIMARY SOURCE ROOT REDISCOVERED:** Robert L. Griess Jr., *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, Journal of Algebra **131** (1990), 281–293, DOI **10.1016/0021-8693(90)90176-O**. It describes an elementary abelian subgroup **A ≅ (Z/3)^3** of order 27 in the automorphism group of the **27-dimensional Albert exceptional Jordan algebra**, with a normalizing **SL(3,3)**, and a decomposition into **27 distinct one-dimensional A-character spaces**. This directly upgrades the relevance of the actual user's balanced **3×3×3 cube**: the dual character group is again F3³, with the trivial character plus **26 nontrivial characters**. The 26 traceless characters follow when the fixed identity line is exactly the trivial-character space and the invariant trace kills the other characters. Source: https://doi.org/10.1016/0021-8693(90)90176-O and https://deepblue.lib.umich.edu/items/d36dccdb-d5e9-47c5-a73e-876d12327d9a.

**Separate literature owners**: Griess *The Friendly Giant* (Invent. Math. 69, 1982) and Frenkel–Lepowsky–Meurman (1988) construct the **different** Monster Griess/VOA weight-two algebra of dimension **196884**; classical Albert/Jordan–von Neumann–Wigner construction gives J₃(O)=Herm₃(O) dimension27 with Jordan product X∘Y=(XY+YX)/2; Aut(J₃(O)) is F4, but no natural Monster-to-Albert product embedding is constructed here. Basic mathematical source: https://books.physics.oregonstate.edu/GELG/aa.html. A single mathematician appearing in both sources does NOT imply an algebra homomorphism or physical identification.

**EXISTING DASHI FIRST OWNERS (do not reinvent):**
- `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda` is literal 3×3×3 non-wrapping spatial cube (54 native grid bonds).
- `DASHI/Wikimedia/IbrahimTernary27OriginTraceless26AlbertShapeBidiExact.agda` already proves an exact SET BIJECTION Cube27 ↔ distinguished origin + 26 non-origin positions, with explicit no-go for promoting this alone to an Albert Jordan product, identity or F4/E6.
- `DASHI/Foundations/ExceptionalAlbertFreudenthalResidualExact.agda` owns 27=1+26, F4 52, E6 78, Freudenthal 56 and 53 reduction *dimension* boundaries.
- `DASHI/Moonshine/Base369Ternary27CharacterAdjacencyEquivarianceExact.agda`, `Base369Ternary27SpectralSymmetryIrrepBridgeExact.agda`, and `Base369Ternary27PathCubeSpectralBandsExact.agda` already distinguish **A=F3³** characters and **non-periodic cube adjacency**.
- `DASHI/Moonshine/Base369PeriodicTernaryTorusPathRestrictionBidiExact.agda`, `Base369PeriodicHeisenbergFibreEquivarianceExact.agda` already distinguish periodic **C3³** torus from open P3³ and demonstrate where Heisenberg shifts cease to be grid automorphisms.
- `DASHI/Foundations/Base369Ternary27StabiliserOperatorHolonomyExact.agda` and `Base369Ternary27AdmissibilityPathDynamicsExact.agda` give finite operator/path admission data, NOT physical gauge holonomy or selfadjoint quantum Hamiltonians.
- Hamiltonian reusable owners have very different scopes: `DASHI/Quantum/Stone.agda` and `SelfAdjointGenerator.agda` / `SelfAdjointColimitGenerator.agda` use a **one-point** toy Stone generator; `DASHI/Physics/YangMills/YMKatoClosedFormHamiltonianExact.agda` records a conditional closed-form/selfadjoint theorem compiler, **not** a particular actual 27-dimensional physical Hamiltonian; `DASHI/Geometry/LCP/FiniteSpectralGap.agda` is a finite Bool carrier; `DASHI/Core/ContactHamiltonian.agda` uses 'Hamiltonian' for residual/pressure and is NOT a quantum energy operator. These consumers must not be conflated with this literal 27×27 finite case.

## Structural correction: F3³ is not C27

Our earlier order-27 Monster spectral projectors and weights [7298,7295,7296,7290] belong to **C27** with elements of order 27 and 27 complex eigencharacters. The new **Albert** donor belongs to **A=(Z/3)^3**, exponent **three**: all 26 nonzero elements/characters have order three, unlike C27 with 18 primitive 27th-order characters. There is NO group isomorphism; a carrier-cardinality bijection is NOT an intertwiner.

Crucially: the previous `IbrahimTernary27OriginTraceless26AlbertShapeBidiExact` identifies the *geometric origin* with a **one-element label** for the algebraic scalar line. In a **Hilbert space of functions on the 27-site cube**, the scalar/trivial Fourier character is instead the constant vector, NOT the site delta at the geometric origin. The two maps are valid in separate categories but are not the same linear map.

The genuine source Albert grading has 27 one-dimensional simultaneous A eigenspaces, with identity in the trivial line, and **J₀** identified with the other 26 lines. A structural product must be supplied from Griess 1990 or an explicit Albert model: it cannot be inferred from the F3³ Fourier basis alone.

## Exact locally executed finite Hamiltonian consumers

`/mnt/data/check_369_albert_f3cube_hamiltonian.py`, executed PASS with exact SymPy, verifies:

| Model | Undirected bonds | Spectrum (eigenvalue:multiplicity) | Preserves scalar/traceless |
|---|---:|---|---|
| Open 3×3×3 **P3³ grid** Laplacian | 54 | 0:1, 1:3, 2:3, 3:4, 4:6, 5:3, 6:3, 7:3, 9:1 | Yes |
| Periodic **F3³=C3³ torus** Cayley Laplacian | 81 | 0:1, 3:6, 6:12, 9:8 | Yes; actually diagonal in F3³ characters |
| Full affine **F3³⋊SL3(3)** Laplacian | 351 | 0:1, 27:26 | Yes, with flat 26-dimensional nonzero band |

On the 27-dimensional function space, P₀=(1/27)11ᵀ and Q=I−P₀ are exact orthogonal projectors of ranks 1 and 26. Both open and torus Laplacians annihilate the constant vector and therefore preserve the 26-dimensional zero-sum subspace. But δ_geometric-origin ≠ constant scalar vector. The explicit script enumerated all **5616** elements of SL3(F3) via its elementary transvections; it is transitive on the **26** nonzero characters. The stabilizer of the torus's six axial unit generators inside SL3(F3) has **24** elements, and a shear preserves P₀/Q but NOT either nearest-neighbour Laplacian.

**New max-cut theorem:** translation symmetry by A plus full SL3 transitivity on nonzero differences implies the affine group acts **2-transitively** on the 27 sites. A real selfadjoint zero-row-sum Hamiltonian commuting with all of it must be H=κ Q. As a hopping Laplacian, this is a rescaled complete 27-site graph with **351** undirected nonlocal bonds (unless κ=0). The literal full-weight complete-graph Laplacian is 27Q with 26-fold degenerate eigenvalue27. So exact A:SL3 symmetry and 54-nearest-neighbour cube locality cannot coexist for a nontrivial uniform graph-Laplacian Hamiltonian. This is independent from the earlier 36-bond completion needed for just the selected mod3 braid element.

## ACTUAL 27-dimensional exceptional Jordan Hamiltonian (not merely shape)

`/mnt/data/check_369_albert_jordan_hamiltonian.py`, executed PASS: builds the **actual** Hermitian 3×3 octonionic Jordan product from Cayley–Dickson quaternion doubling using rational arithmetic; tests all 27 basis vectors, identity, positive diagonal Gram pairing, sampled Frobenius and Jordan identities. Distinguish this literal construction from the original SET-ONLY Albert-shape Agda owner.

Choose genuine Jordan element h=diag(1,0,-1) and define H_h(X)=h∘X. This is selfadjoint relative to the positive Albert trace form. Because h is diagonal, its **complete exact** 27-dimensional spectrum is:
- +1 and −1 each multiplicity1;
- +1/2 and −1/2 each multiplicity8;
- 0 multiplicity9.

The actual algebraic scalar projector E(X)=(Tr X/3)I has rank1 and tracefree projector Q(X)=X−E(X) has rank26. Here H_h(I)=h is traceless, so **unlike either graph Laplacian, H_h does NOT preserve the 1-dimensional unit line or the 26-dimensional complement separately**. The selfadjoint compression Q H_h Q on J₀ has eigenvalues ±1/√3 each multiplicity1, ±1/2 each multiplicity8, and 0 multiplicity8. This is explicitly checked with exact SymPy radicals. Compression need NOT equal a full Albert automorphism or a source Hamiltonian for gravity.

The new `DASHI/Moonshine/Base369AlbertF3CubeHamiltonianSymmetryMaxCutExact.agda` imports the original Cube27, 1+26 shape, path and periodic character owners. It proves a typed general Jordan theorem: **if the left-Jordan-multiplication operator L_h commutes with an action fixing the Jordan identity, then h itself must be fixed by that action**, evaluating the commutator at the unit. Given the genuine Griess 1990 A action with only the trivial character line fixed, any A-invariant L_h must have a scalar h. Source's actual Albert action is a required consumer receipt, not manufactured by a 27-label bijection. The module separately proves a periodic axis coordinate translation has order3, not 27.

## Concrete cross-pollination to Monster Griess / VOA / KK / AdS3

**Actual Monster V2 charge side:** earlier g∈Monster of order27, with C27 spectral ranks, Fourier projectors and the source Griess cubic. This has an entirely different operator/action algebra from Griess 1990's Albert/F4 A=3³. A bridge must supply an explicit algebra or group representation map, first comparing exponent structure, products, quadratic/cubic forms, and whether the finite Hamiltonian/domain is actually preserved. Numerical 27=27 or 1+26 does NOT pay that.

**Operator route to test first**: construct the source A action and homogeneous Albert basis from Griess 1990, calculate a nonzero example of J_a∘J_b→J_{a+b}, its actual cubic invariant and a proposed selfadjoint Hamiltonian or derivation. Compare only admissible consumers against the existing finite cube, Monster Griess C27 projected cubic and actual source-selected 3B operators. Distinguish whether a claimed physical H is the open-grid graph, torus Cayley, complete-graph, Albert L_h, or Monster VOA L₀/mode-Hamiltonian.

**Physics boundary:** Jordan multiplication by an element is a mathematical selfadjoint operator under the positive trace form. Calling it a physical Hamiltonian requires a chosen Hilbert/state interpretation, experimentally sourced coupling/scale, observable dictionary and dynamics. None of this constructs a 5D Ricci-flat KK compactification to AdS3 or a holographic Monster/VOA duality. Do not use hypothetical exceptional algebra physics references as empirical validation.

## Pareto tasks and acceptance

P0: exact-head Agda compilation of the NEW adapter plus existing owners; source-written until then. P1: match source Griess 1990 Albert A-eigenbasis and actual cubic-product structure, not generic tensor characters. P2: test one explicitly sourced product against a well-typed Hamiltonian and the original 54/81/351-bond distinctions. P3: only with a same-object representation/field theory producer, attempt the Monster C27 cubic and bulk KK/AdS3 observables. 

Local receipts: `python3 /mnt/data/check_369_albert_f3cube_hamiltonian.py` and `python3 /mnt/data/check_369_albert_jordan_hamiltonian.py` passed; both `py_compile` passed. GitHub portable shorter analogues committed as `scripts/check_base369_f3cube_albert_hamiltonian_symmetry.py` and `scripts/check_base369_actual_albert_jordan_hamiltonian_spectrum.py`. The full literal octonion-product file is a separately delivered local Python artifact; no Agda kernel, full Griess 1990 fine-grading matrix implementation, Monster multiplication or physical KK/AdS3 receipt claimed.
