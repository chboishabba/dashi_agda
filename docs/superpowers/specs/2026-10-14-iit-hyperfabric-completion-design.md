# IIT Hyperfabric Completion Design

## Goal
Complete the IIT/hyperfabric programme by turning the current finite system-phi prototype into a source-faithful IIT-4 evaluator, calibrating it against the recurrent XOR-grid family, and then using the repo's 369/pants/hyperfabric machinery as controlled experimental carriers rather than as substitutes for IIT quantities.

## Architecture
The experiment carrier is factored as

- `H`: path-indexed causal fabric / gluing graph,
- `mu`: local synthesis operation at each 2->1 causal cell,
- `s`: current system state.

A local causal cell has two input fibres and one output fibre, `(A,B) -> C`. Gluing transports prior outputs into named A/B input ports and is definitionally separate from XOR/OR/AND/triXor. IIT directional partitions act on causal/gluing connections by noising them; they do not rewrite the local gate.

The existing 1->3 topological pants owner remains a separate trivalent orientation. No causal reversal is inferred without an explicit witness.

## Completion tranches

1. **Executable IIT-4 kernel.** One finite owner must define exact finite TPM/repertoire inputs, directional partitions, cause/effect intrinsic information, normalized MIP selection, and unnormalized `phi_s` return. Zero-denominator behaviour must be typed rather than hidden. A Python reference evaluator must emit machine-readable receipts using the same conventions.

2. **XOR-grid calibration.** Re-express the existing recurrent XOR grid through local 2->1 synthesis cells plus the gluing graph. The evaluator must reproduce the expected qualitative facts: feed-forward decompositions yield zero system integration; recurrent XOR fabrics can remain irreducible; minimum partitions act on connections rather than gates. No historical IIT-3 counterexample quantity may be silently called IIT-4 big-Phi.

3. **Matched fabric/gate sweeps.** Hold `H` fixed and vary `mu` across Boolean XOR/OR/AND and repo-native ternary `triXor`; then hold `mu` fixed and vary `H` across open path, cycle, grid, and pants/hyperfabric fixtures. Results must be statewise and must expose the selected MIP.

4. **369 algebra controls.** Use exact repo owners for F3/triXor, Z/9Z-like nonary addition, and F3^2 phase-product addition. In particular, compare same-cardinality Z9 and F3^2 systems under matched fabric topology. Same cardinality must never be treated as same algebra.

5. **Pants/hyperfabric fixtures.** Represent repeated `(A,B)->C` cells indexed by path/step with output-to-input gluing. Test open versus closed paths, branchings, pairwise compatible gluings, and higher-order/cocycle-compatible fixtures. Preserve the distinction between graph partition, stalk-restriction partition, and global-section partition.

6. **Pointed ternary-27 integration.** Reuse the exact 27 = origin + NonOrigin26 carrier, 27 <-> C3^3 <-> CubeCell27 chart, 9 = 1 + 8 face sheets, edge transports, and corner cocycles. C3^3 recentering is an algebraic carrier permutation relative to the chosen chart, not a canonical non-periodic cube symmetry.

7. **Full IIT distinctions and relations.** Extend beyond system `phi_s`: enumerate mechanisms/purviews, compute distinction `phi_d`, build relations and relation `phi_r`, and construct the full cause-effect structure before evaluating structure integrated information `Phi`. Keep these quantities definitionally and computationally distinct.

8. **Aaronson-style stress test.** Only after the IIT-4 evaluator exists, compare highly integrated XOR/369 fabrics against declared cognitive/phenomenal consumers. High integration is not itself a proof of consciousness.

9. **Consumer descent.** Reuse `ConsumerDescentMinimalObserverExact` and related MaleCNS/brain observers to state what information an IIT observable preserves or loses. Produce explicit non-descent witnesses when a candidate IIT observation cannot recover a declared consumer-relevant distinction.

10. **Formal/executable receipt loop.** Every Python run emits JSON/CSV receipts with fabric definition, local gate law, state, partition enumeration, MIP, repertoire values and phi outputs. Agda owners verify exact finite structural claims and rational portions of receipts. Python numerical output is never promoted to a kernel proof.

## Source and attribution boundaries
- IIT-4 definitions are calibrated against Albantakis et al. 2023 and remain version-separated from historical IIT/XOR counterexamples.
- Existing repo owners are reused rather than reimplemented, including Base369 algebra, pants/frontier, hyperfabric, pointed-27, cyclotomic/Fourier, trialectic, consumer-descent, brain/MaleCNS, Monster and zeta surfaces.
- Existing attribution/source metadata is preserved when external identities or literature-backed claims are reused.

## Success criteria
The programme is complete when:
1. one source-faithful finite IIT-4 evaluator computes `phi_s`, `phi_d`, `phi_r`, and `Phi` on finite fixtures;
2. the XOR-grid calibration is reproduced in the generic fibre/gluing representation;
3. matched sweeps isolate effects of fabric, local algebra, and state;
4. 369/pants/27-state fixtures are evaluated without cardinality or geometry/algebra conflation;
5. consumer-descent theorems state exactly what IIT observables can and cannot recover;
6. executable receipts are generated and formal claims are separated from numerical evidence;
7. Agda kernel-green is claimed only after an actual Agda/CI receipt exists.
