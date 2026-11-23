## 23 November 2026 — exact FULL nine-coordinate torus spectral decomposition

The original hyperfabric is three separate (C_3^3) periodic source factors, not one 27-mode periodic voxel. Since a 3D C3^3 additive Fourier character has support-multiplicity row `(1,6,12,8)`, the full 9D periodic Fourier character stratum of support r is exactly `binomial(9,r)*2^r`:

```text
r=0..9: 1,18,144,672,2016,4032,5376,4608,2304,512.
sum = 19683 = 3^9;
maximum-support r=9 = 512 = 8^3.
```

This is a true full-hyperfabric tensorization of the 8 high-support modes in each original three-trit voxel. The **periodic** C3^9 torus Laplacian has eigenvalue `3*r` with these multiplicities; the **nonperiodic** P3^9 path Laplacian does not share this C3-character eigenbasis. Do not mistake the genuine 8-mode 3D shell or 512-mode nine-dimensional stratum for the independent NS 1/128 gain, YM 16×8=128 incidence, or the H05 eight vertices. These are separate, precisely typed sources until linked by a proved operator intertwiner.

The new runnable script now checks the full 10-shell counts (commits `724c397e`, `7d8c85ce`); independent local integer test `sum(C(9,r)*2^r)=19683` and 512=8³ PASS. The earlier source-trit coordinate repair `c276ef63` / `bc0846fd` remains essential.

---

## 23 November 2026 — important native-path-coordinate repair after source reread

The first committed Python checker used trit integers `0,1,2` but evaluated the path relation `0-1-2`, with centre 1. **That is NOT the ORIGINAL SSP-balanced source**, whose native nonwrap spatial path is `-1↔0↔+1`, with centre 0. Though the unlabelled graph is isomorphic and 54/81/118,098 edge counts are unchanged, using residue 0 as a group origin while taking residue 1 as spatial centre is NOT same-carrier faithful. It can invalidate marked coordinates, source incidence and k/time covariance.

The corrected committed `scripts/check_rh_hyperfabric_k_time_spatial_intertwiner_20261123.py` (GitHub commits `c276ef63`, `bc0846fd`) now enumerates `(-1,0,+1)^3` and full `(-1,0,+1)^9`, with true path predicate `a=b or a=0 or b=0`, and maps mod3 arithmetic back into balanced representation via `(x+1)%3-1`. True antipode is now `x↦-x` (rather than a residue 2 label) and every k-chart uses the same original zero-centred source. The local independently executed corrected-source test confirms all original 54/81 edges, 729/729 dual-Fourier positions/frequencies and 118,098/118,098 nine-coordinate edge inverse recoveries PASS. The original fixed-path commutator rank24 had already been independently computed in genuine balanced coordinates, so that structural no-go remains valid. The updated source was read back; no byte-for-byte external runtime or Agda kernel receipt is claimed.

**Acceptance correction:** never infer same-source geometry solely from matching numbers/edge spectra or from an abstract graph isomorphism; require literal source coordinate centre, orientation sign, incidence labels, original time/refinement indices and inverse. This repair is why the Hyperfabric P3³-versus-GF3³ distinction matters, even before actual RH zero transport.

---

# RH × hyperfabric: actual (k,t)-indexed spatial/Fourier intertwiner source audit (23 November 2026)

**Source ownership / attribution.** The following pre-existing DONORS were read from `master` and reused on RH draft PR #1533:
- `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`: the original P3³ 27-site nearest-neighbour graph, and the 9-coordinate `TernaryHyperformalPoint` with 27³=19,683 nodes, not a 27-site surrogate;
- `DASHI/Moonshine/Base369PeriodicTernaryTorusPathRestrictionBidiExact.agda`: the same 9-trit set with distinct *periodic* C3^9 adjacency (P3^9 is a strict path subgraph);
- `DASHI/Moonshine/Base369Ternary27SignedSymmetryMonsterIntertwinerExact.agda`, `Base369Ternary27CharacterAdjacencyEquivarianceExact.agda`, `Base369Ternary27SpectralSymmetryIrrepBridgeExact.agda`: **already-existing intertwiners** for B3 coordinate reflections/rotations, native fixed P3³ adjacency, C3³ characters and (k\mapsto-k). The phase/Monster interpretation has its own explicit non-promotion boundary;
- `DASHI/Unified/TOE369CoarseFineIntertwinerMaxCutExact.agda`: pre-existing coarse/fine and ternary TOE normalization; its selected Monster linear intertwiners remain distinctly open;
- `DASHI/Information/PNFHistoryTimeHyperfabricDeltaExact.agda`, `DASHI/Reasoning/HistoryTimeIndexedConsumerFibreExact.agda`, `DASHI/Core/GovernedIndexedResidualCubeExact.agda`: original source/consumer/history/time/step/refinement ownership, not a single k-time counter;
- original Griess/Sah grade shears and native #1249 C2 27→13+orientation codec own the Singer actor, not RH. RH's earlier `RHFourWindowC26NativeHyperfabricSquareExact` already owns the nonidentity C26 **index-fibre** square.

**Correction to old graph no-go:** the original Singer (G=-M) maps 54/54 original P3³ edges and 81/81 original periodic C3³ edges to nonedges **of each respective FIXED source graph**. This ONLY refutes fixed-graph invariance. For (P_G) the exact G action and original adjacency/Laplacian (A_0,L_0), define true transported graphs (A_k=P_G^k A_0P_G^{-k}), (L_k=P_G^k L_0P_G^{-k}). Then (P_G A_k=A_{k+1}P_G) and (P_G L_k=L_{k+1}P_G) for every k. This is an exact **isomorphism between indexed graph CHARTS**, not an automorphism of A0 and not a discovered physical evolution. Locally, the fixed-path Laplacian commutator (P_GL_0-L_0P_G) has rank **24**, explicitly showing its non-equivariance.

**True nine-coordinate graph:** each original P3³ voxel has 27 nodes, 54 edges. On ((P3³)^3=P3^9), there are 19,683 nodes and (3×54×27²=118,098) undirected edges, all source-edge witnesses reconstructible under the three-block (G^k) chart. The periodic C3^9 host has (3×81×27²=177,147) edges; it is NOT the same adjacency. An exact independent local test walked ALL 118,098 nonperiodic nine-coordinate edges and checked both endpoint source recovery under the G and G^-1 transport.

**Genuine source-frequency intertwiner:** original (C_3^3) Fourier characters on periodic grade coordinates (x\in F_3³), (chi_q(x)=\exp(2\pi i(q\cdot x)/3)), satisfy
[
 \chi_{G^{-T}q}(Gx)=\chi_q(x)
]
for all 27×27=729 position/frequency pairs; this is the contragredient of the ACTUAL original Griess grade map, not a claim that Singer belongs to B3. The periodic (C_3^3) Laplacian has exact support-frequency eigenvalue (lambda(q)=3,|\{i:q_i\ne0\}|) with strata
[
 0:1,\quad3:6,\quad6:12,\quad9:8.
]
The **8** here is the real highest-support (all-three-nonzero) Fourier shell; the *nonperiodic* P3³ Laplacian is **not** diagonalized by these C3³ characters. At k, the transporting q-label is (G^{-kT}q). No actual ζ-zero, Monster module or RH signed-far representation is entailed by this finite character identity.

**Physical time t and refinement/iteration k are TWO independent axes.** A true source time step (T_{t,k}:X_{t,k}\to X_{t+1,k}) and a refinement (R_{t,k}:X_{t,k}\to X_{t,k+1}) have commuting defect
[
 D_{t,k}=R_{t+1,k}T_{t,k}-T_{t,k+1}R_{t,k}.
]
For invertible change-of-chart (P_{t,k}), the correct new time/refinement maps are (T'_{t,k}=P_{t+1,k}T_{t,k}P_{t,k}^{-1}) and (R'_{t,k}=P_{t,k+1}R_{t,k}P_{t,k}^{-1}), giving the exact identity
[
 D'_{t,k}=P_{t+1,k+1}D_{t,k}P_{t,k}^{-1}.
]
**Therefore a nonzero physical commutation defect cannot be erased by relabelling**. Source-specific T/R must be supplied. A local two-time/two-refinement rational toy (T_{t,k}=I-a_t L_k) with (a_0=1/8,a_1=1/16) verifies the two distinct indices but is NOT the original NS/YM/RH time evolution. The added `DASHI/Analysis/RHHyperfabricKTimeTransportedSpatialIntertwinerExact.agda` constructs the exact nonidentity k-indexed edge relation with all source-edge witnesses, a typed independent Time parameter and historical/consumer/sign/residual/mode/observedZero fields. It is source-written only, not Agda-kernel accepted. The periodic-path distinction is represented by using two separate imported original edge producers.

**What 8, 128, 16 actually mean (DO NOT erase the geometric flag):**

1. Original **NS finite periodic dyadic** source `NSPeriodicConcreteCarrier`, `NSPeriodicConcreteMultiplierScalingReceipt`, `NSPeriodicConcreteNorms`, `NSPeriodicConcreteRationalCertificate` and `scripts/ns_radius8_multiplier_scaling.py`: spatial-frequency separation radius (R=8), rational max-norm hat multiplier gain (2^{-(R-1)}=1/128), and far-high factor (2\text{ placements}×2\text{ Bony}×2\text{ Bernstein}=8). Thus **8×(1/128)=1/16**. This is a real dyadic-geometric *finite-model* scaling pattern, NOT a full NS analytic/operator estimate (source status explicitly false).
2. Original **YM R445 4D blocking** source `YMClayNativeSideFourPairSpectatorSortProgramExact` and original Wilson/codec ledger: 2^4=**16** coarse block sites, four positive directions per site =64 coarse bonds, two selected fine links each =128 (hence **8 selected fine links per site**), with 896 remaining out of 1024 fine positive links. Exact incidence/product geometry, but DIFFERENT operator and physical dimension from NS/hyperfabric.
3. Original **H05** typed commuting cube has **8 vertices**, 12 maps and six faces. This is a third distinct 8, not the NS factor or YM incidence count.
4. Original **C3³ periodic** Fourier has **8** maximum-support characters, giving another honest geometric stratum.

The shared integers may suggest a chart/normalization comparison; no same-object intertwiner between NS dyadic cutoffs, YM 4D Wilson bonds, H05 vertices or RH source follows from cardinalities alone. In particular the factors (8,128,16) do NOT imply the Singer action is a fixed-path graph symmetry.

**Files/receipts:** new standalone `scripts/check_rh_hyperfabric_k_time_spatial_intertwiner_20261123.py` (commit `af2ba256`, optimized `53a8c30b`), source-written Agda `DASHI/Analysis/RHHyperfabricKTimeTransportedSpatialIntertwinerExact.agda` (commit `aa496c4a`). The source-equivalent local SymPy and exhaustive vertex/edge checks passed; the committed GitHub script and Agda have NOT been independently executed as kernel/CI receipts. Original fixed graph and source-date attribution preserved.

**P0 negative control and next source task:** the new graph-family intertwiner is a true mathematical change of chart, but without the actual RH (T_{t,k}), its zero-count/mu/FarExact operator and a signed estimate, it contributes no strict terminal (H_n+E_n+S_W<T_W(\rho)). The already-paid reflection/character source intertwiners cannot be promoted to a G-action on actual ζ-zero multiplicities. To advance, attach a SOURCE-PRODUCED time/refinement (T,R), calculate the literal (D_{t,k}) and signed FarExact/mu operator in both parity sectors; check a truly nonzero defect or prove it zero without chart fiat. H07 physical 9DOF tangent/frame and all six analytic RH commuting faces remain OPEN. No RH/GRH/Clay completion or Agda/Lean kernel check.
