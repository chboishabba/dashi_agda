# Algebraic Carrier Support Lane

## O/R/C/S/L/P/G/F
O: You (algebraic carrier lane owner) synthesize the current moonshine/root-system discussions into a single summary focused on tangible support for the P0 physics closure spine.  
R: Clarify whether there is one runnable carrier idea (e.g., Weyl-invariant Vec ℤ⁴ root lattice) that plugs directly into the closure or whether the lane stays as advisory context.  
C: Docs-only; new note under `Docs/`.  
S: Context medium—Docs/PrimeToModular.md, Docs/MoonshinePrimeSource.md, Docs/MoonshinePrimeObject.md already list candidate carriers; collision with other lanes is avoided.  
L: cheapest viable tier (`gpt-5.1-codex-mini`).  
P: you; no additional experts.  
G: Keep the lane summary compact; avoid changing shared files.  
F: Need to declare carrier idea status clearly for P0 relevance.

## Summary
- **Landed core-spine bridge**:
  [`CoreSpineBridge.md`](./CoreSpineBridge.md) is now the compact entrypoint
  for the typed carrier thread from `Base369.TriTruth` through
  `DASHI.Algebra.Trit`, `RealTernaryCarrier.Carrier n`,
  `AgreementUltrametric.ultrametricVec`, and the bounded contraction
  certificate surface. It also records the CRT/J p47/p59/p71 scalar bridge.
  This is stronger than advisory naming convergence, but still a `bridge`
  surface rather than a new solved-physics theorem.
- **Direct carrier idea**: the signed Weyl-root lattice on `Vec ℤ⁴` decorated with the `SP.SignedPerm4` action plus the hyperbolic cone/MDL structure already present in the shift Lorentz instance. This lattice naturally supports a `B₄`/Weyl symmetry, offers a modular-quotient candidate (via signed-looped Hecke actions), and sits adjacent to the Moonshine prime object that counts basin signatures. Because it is already embedded in `ShiftLR` code and carries the Hecke-friendly signed-permutation action, it can be promoted to the P0 spine by:
  1. Formally abstracting the carrier as “vector lattice + Weyl action + hyperbolic cone + Hecke compat field”.
  2. Showing that `shiftPrimeEmbedding` and `shiftMotifOf` factor through that abstraction, which links the lattice symmetry to the observable Hecke signature.
  3. Using that carrier for gauge/matter reconstruction or continuum-limit proposals by appealing to its orthogonal root-system structure (triality, Niemeier orbit data) already discussed in `Docs/OrbitShellProfilesAndLorentzSignature.md`.
- **Advisory material**: other streams (modular/Hauptmodul, null-model testing, outreach) remain advisory for now; they do not directly produce a new carrier but provide motivation and tests once a carrier is pinned down.

## Decision
This lane now has one landed core-spine bridge over the existing ternary
carrier and one direct next carrier idea: the Weyl-invariant `Vec ℤ⁴` lattice
with signed permutations and Hecke-compatible invariants. The ternary bridge is
repo-native and typechecked; the Weyl-root carrier remains the next promotion
candidate. Additional materials remain advisory until their carrier
abstractions are formalized.
