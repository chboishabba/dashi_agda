# Alexander horned C3: shared-central collar cover assembly (2026-10-25)

## Implemented

New Lean source: `proofs/horned_c3_lean/HornedC3/ThreeArmCollarCoverAssembly.lean`.

The implementation reuses the pre-existing `ThreeArmCollarIntersections`
and `ThreeArmVanKampen` modules, rather than inventing a fresh version
of van Kampen. Given a central open region `C` and satellite-only open
regions `S : Fin 3 -> Set X`, set `U_i = C union S_i`.
If the `S_i` are pairwise disjoint, then
`U_i intersect U_j = C` for i != j, and any triple intersection
containing two distinct indices is C.

The new `CollarCoverCertificates` structure states the remaining
proof-carrying hypotheses, while `collarCertificatesToCover` derives
all fields of the existing `ThreeArmCollarCover` and
`collarCertificatesPi1FreeProduct` consumes the existing Hatcher-at
free-product equivalence. In particular, this reduces the off-diagonal
**path-connectivity** certificates to path-connectivity of C, and
all-equal intersection cases to connectedness of U_i.

The based `OverlapGroup` subsingleton obligations are deliberately
**still present**. A set identity `U_i intersect U_j = C`
does not automatically furnish a proof about a based fundamental group
without a transport/rewrite theorem at this exact interface.
The current assembly accepts precisely those already-typed overlap
witnesses. This is an explicit dependency, NOT a hidden geometric axiom
or fabricated theorem about the wild ball.

## Exact final geometric inputs

1. An explicit actual open central region `C` inside the particular
   complement `E = S3 minus B` and open satellite-only subsets `S_i`.
2. Pairwise disjointness and coverage of **all of E** by U_i.
3. Based central path-connectivity and each arm's path-connectivity.
4. The based fundamental-group overlap subsingleton certificate, with
   the source-specific collar homotopies.
5. Equivariant homotopy identifications of arm groups with Hatcher's
   original one-sector group G_A.

Only after these are discharged can the existing conditional free
product result be transported to `pi1(E) = G_A * G_A * G_A` as an
internally formalized same-object result. A topological claim
backed by published manifold theorems may be valid on paper without
this complete machine-level realization; the statuses are distinct.

## Pareto/Ibrahim/snowball: source and prior-art path

First reuse the exact already-developed Lean/Agda/collar sources and
their explicit hypotheses. Next read Hatcher's **original punctured
torus** argument and Lippert's supported horn attachment for a
relative collar construction capable of inhabiting the open-cover
fields. Do not substitute a tree of binary addresses, a finite
nested-ball regression, or an abstract three-sector free product for
those concrete maps. Then test the geometric inclusion and induced
group maps in the *same* ambient complement.

Attribution: Alexander (1924) original wild sphere; Hatcher,
Algebraic Topology Example 2B.2, original selected group-stage
construction; Lippert, The Alexander Horned Sphere and Bing's Hooked
Rug, original named exposition used for supported constructions;
Deicyde/hatcher-at existing formal van Kampen machinery; repository
PR #1244 source-specific C3 gluing and assembly. Repeated reporting
or the same construction appearing in another exposition is not
independent evidence.

## Verification status

The new Lean source is committed on PR #1244. **No exact-head Lean
typecheck was run in this turn**, therefore it is source-written,
not claimed kernel-verified. If compilation exposes mismatched
implicit arguments or required simp rewrites, these remain code
integration issues, not fulfilled geometric obligations.
No Agda, CI or physical experiment receipt is claimed.
