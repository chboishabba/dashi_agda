# RH P0 × native 27→13+orientation hyperfabric: nonidentity C26 H05 commuting square (23 November 2026)

**Source audit and attribution.** Original mathematical C2 antipode and 27→(1+13×2) quotient/conditional residual are owned by `DASHI/Foundations/BalancedTernaryAntipodalOrbitExact.agda`, `BalancedTernaryAntipodalResidualCodecExact.agda` and `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda` (original native #1249). The original grade order13 word on the SAME F3^3 grades is owned by Griess 1990 / Sah and Agda `DASHI/Moonshine/Griess1990MoufangCoherentSL3SectionSourceExact.agda`, `Griess1990Moufang81ExplicitThirteenCycleExact.agda` (Lean #52 counterpart). H05 owns `DASHI/Core/GovernedIndexedResidualCubeExact.agda` (TOE #1291). RH owns `DASHI/Analysis/RHFourWindowBiharmonicFiniteCubeExact.agda` (RH PR #1533, same original Lean 4-window source). This note ADAPTS these existing owners; it does not introduce a new ternary site carrier or new C26 physical lattice.

**New source-written module:** `DASHI/Analysis/RHFourWindowC26NativeHyperfabricSquareExact.agda` on RH PR #1533; companion portable regression `scripts/check_rh_c26_native_signed_h05_nonidentity_square_20261123.py`. Independent source-equivalent LOCAL Python/SymPy acceptance: exact 26/26 state and sign recoveries, 26/26 thirteenth/26th iterates, 156/156 six-face path checks, rational 26×26 projector identities, and 54/54 original spatial edge non-equivariance PASS. The new actual GitHub script's bytes were not directly executable in this environment; no remote CI or Agda/Lean kernel proof is claimed.

## I. Exact native commuting square: nontrivial source G action, sign INCLUDED

On original 27 trits `V=F3^3`, let `A(v)=-v`. Its unique fixed point is v=0; nonzero points are 13 antipodal pairs. The existing projective sign codec gives a **two-sided** finite isomorphism of sets

```text
 F3^3 \ {0}    --encode-->   Axis13 × Orientation2
       |                        |
       | G=-M                   | Ghat = encode o G o decode
       v                        v
 F3^3 \ {0}    --encode-->   Axis13 × Orientation2
```

where `M(x,y,z)=(x+y,y+z,x+y+z) mod3` is the original Griess order13 grade action and `G=A∘M` is its signed order26 lift. This commutes on **all 26 native original points**, with source recovery `decode o encode=id`, and `Ghat^13(a,b)=(a,not b)`, `Ghat^26(a,b)=(a,b)`. The actual source of the `Axis13×Bool` *constructor* matters; an abstract 13-element type would not preserve the native graph or source labels.

The native canonical Axis13 section uses the **first nonzero coordinate positive**. In that section, `M` acts on a projective axis with a nontrivial sign 1-cocycle `ω_M(a)` recording whether its preferred representative is replaced by the antipode. Exact exhaustive source computation: **four** canonical axes have `ω_M=1`, nine have `ω_M=0`. Therefore

```text
Ghat(a,epsilon)
  = (Mbar(a), epsilon XOR omega_M(a) XOR 1).
```

Over a full 13-axis cycle the parity of `Σ omega_M(a)` is zero, but the `13` copies of the explicit antipode XOR 1 contribute one remaining flip. Hence `Ghat^13` flips sign and does NOT send it to scalar zero. This cocycle is the key point: replacing Ghat with (a→next13(a), epsilon→not epsilon) in the canonical section is incorrect on four axes, even though a different coherent 13-cycle section can trivialize the M cocycle by a change of gauge.

## I-bis. Intrinsic finite-field geometry: Singer cycle, not a coincidental 13

The original real 27-element additive grade carrier is F3³. Relative to the original x/y/z coordinate basis, the source selected Griess grade word is
`M=[[1,1,0],[0,1,1],[1,1,1]] mod3`, and the signed lift is `G=-M`. Its original 3×3 characteristic polynomial is

```text
charpoly_F3(G)(X) = X³ - X + 1.
```

At X=0,1,2 its value in F3 is always 1, so the cubic is irreducible. The original nonzero input basis vector `v=(1,0,0)` gives an explicit **cyclic** basis `[v,Gv,G²v]` with determinant `1 mod3`. The exact local GF3 matrix identities `G³-G+I=0`, `G¹³=-I`, `G²⁶=I` certify that (after this source-compatible basis choice) the native additive F3³ space is the finite field `F27=F3[X]/(X³-X+1)`, with the original G actor equal to multiplication by primitive residue `alpha=X mod f`. Since `alpha` has multiplicative order26=27-1, it is a **Singer cycle** on the 26 nonzero field elements; on the projective quotient the actor is the Singer 13-cycle on PG(2,3).

```text
1 -> F3× = C2 -> F27× = C26 -> (F27× / F3×) = C13 -> 1.
```

This exact sequence splits as abstract groups because gcd(2,13)=1, but our ORIGINAL projective Axis13 codec uses the **canonical first-nonzero-positive** orientation section and introduces the four-flip sign cocycle. A split abstract group presentation does NOT mean the canonical `Axis13×Bool` transport has zero local sign corrections. The field multiplication interpretation is of the original F3³ additive-grade/label action, not native P3³ path graph adjacency or Albert Jordan multiplication. Do not misread the coincident Gaussian norm `13=3²+2²` as a proved isometry to this Singer projective geometry.

The new source-written Agda `sourceFieldPolynomial` in `RHFourWindowC26NativeHyperfabricSquareExact.agda` lists all 27 native trit constructor cases for `G³-G+I=0`; **it is not independently Agda typechecked**. The portable script now checks the exact 3×3 polynomial, cyclic determinant1 and original 26×26 character/parity identities. This is finite algebra, not a C26 action on zeta zeros.

## II. Genuine six-face H05 finite cube, with nonidentity z-axis

The previously constructed RH source traced square carries `Source4` containing BOTH nonzero raw π/3 contributions and their cancellation witness. Its `TracedFold` and `TracedFive` retain `Source4` in both legs, unlike the lossy observed stencil alone. The NEW `nativeC26H05Cube` is exactly the ORIGINAL typed H05 cube with:

```text
A,E = Code26 × Source4       B,F = Code26 × TracedFold
C,D,H,I = Code26 × TracedFive
x = projectWithSource or identity, y = directWithSource/unfoldWithSource
z = codeStep on Code26 × identity on full RH source/provenance.
```

The x-y face commutes by the genuine original traced projective 4→3→5 square, while x-z/y-z commute by functoriality of the product under **NONIDENTITY** codeStep. Two x-y faces and four independent z-naturality faces are explicitly source-written; native H05 `xyz-zyx` compiles all six endpoint paths provided Agda validates the source. Every original Source4, its cancellation proofs, and independent H05 history/time/refinement/Frobenius/version/consumer index plus RH sign/residual/mode/observed-zero tags are maintained by `mapIndexedPayload`. This is not the old degenerate z=identity cube, but it is still an **external product action on RH**—the RH observable itself has NO established nontrivial Griess/C26 covariance.

The non-bidirectional observation control remains: discarding source history makes (24,24) and (48,48) π/3 raw cancellation histories indistinguishable. `recoverAfterDirect`, `recoverAfterFold`, `recoverAfterMove`, `indexedPreservesSign`, `indexedPreservesResidual`, `indexedPreservesObservation`, and `indexedPreservesMetadata` explicitly avoid that false source identification.

## III. Genuine parity-sector decomposition, NOT sign deletion

Let `P_G` be the 26×26 rational permutation of original nonzero F3^3 points by G, and `P_A=P_G^13` the native antipode. Define the two **exact complementary** Q-linear operators

```text
 E=(I+P_A)/2  and  O=(I-P_A)/2.
 E²=E, O²=O, EO=0, E+O=I, trace E=trace O=13,
 P_G E=E P_G, P_G O=O P_G,
 (P_G)^13 E=+E, (P_G)^13 O=-O.
```

The even sector is 13D and odd sector is 13D; BOTH are nonzero, and both are needed to reconstruct the original 26 signed orientations. A projection to the even sector alone loses the physical SOURCE SIGN RESIDUAL and breaks the bidirectional contract. These are rational representations of the ORIGINAL grade-label permutation; they are NOT the native spatial cube Laplacian eigenprojectors or a representation of actual RH zero geometry.

The characteristic count can be viewed as 26 oriented basis = 13 even + 13 odd, while the fixed global centre is an additional, separately typed 1D constituent. Under the full SL3(3) action, other decompositions (1+12+13) and the C13/Albert module comparison have DIFFERENT operators/groups; do not identify them by equal dimensions.

## IV. What geometry solves, and what it does not

**Positive solved finite geometric gate:**
1. Original 27→13 signed quotient and actual Griess C26 lift are constructed on the SAME finite grade carrier, with exact sign-cocycle and 26-state inverse.
2. The native H05 six-face cube has a NONIDENTITY action along its third axis, commuting with traced RH 4→5 projection/unfolding.
3. The source sign and orientation residual remain separately reconstructible; the exact rational even/odd projectors provide a source faithful 13+13 field split.
4. The original positive-pole RH π/3 witness, its q=4 negative biharmonic Fourier notch and the original source/target normalization are UNCHANGED.

**Not a solve of analytic RH:**
- The grade actor maps ALL 54/54 nearest-neighbour original cube edges to nonedges. No P3³ graph-isometry, 9DOF tangent/frame transport, or original spatial Laplacian intertwiner.
- The x/y/z cube acts as an EXTERNAL PRODUCT on RH source; its naturality is a real finite commutation but gives NO nontrivial action on actual zeta zeros, μ-background, `literalFarExactAt`, or `compensationTargetThreshold`.
- The old direct substitution π/13 puts both pole coordinates negative across the original λ corridor and drops old positive target strength below its sufficient floor; a sign-bit relabelling does NOT repair that signed source inequality.
- To pay A2, demand a NEW source-specific action on the actual RH zero-side and smooth μ objects, a proven intertwiner of its signed far operator, and an inequality for BOTH antipodal sectors with all local slack and original metadata intact. A group character or 13-axis cardinality alone cannot give this.

## V. 2600 provenance, factor vs invariant

The number 2600 can be factored as 13×200=26×100=2³×5²×13. **This is arithmetic, not an invariant attached to the original C26 construction**. Repository search shows literal 2600 in `scripts/ns_kappa_bias_profile_sweep.py` as a sweep parameter and in original CoreWeave financing/DDTL sources as a financial observation, among other unrelated literals. Prior personal discussion also recalled a rough 2,600-line dashboard deletion, but none supplies a same-object RH/hyperfabric value 2600. Combining the RH t≥200 threshold and 13 axes to obtain 2600 is a new OPTIONAL product scale, not a theorem; do not promote to a cycle length (26), mode count (13+13), or analytic cutoff. If a target F2600 object is later identified, demand source/units/definition before connecting.

**Status:** local exact rational/finite carrier checks PASS; source-written Agda remains pending native compiler, and true signed FarExact/compensation, Bishop π semantic bridge, RH/GRH, and 9DOF analytic fibre actions remain OPEN.
