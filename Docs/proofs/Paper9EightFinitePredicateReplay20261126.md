# Paper 9 — full eight-predicate exact arithmetic replay

26 November 2026. Previous #1546 head 1bf819be. All eight finite **predicate specifications** independently replayed, not executed Lean predicates or native proofs. No CI. Preserve classical CM, Hecke, Eisenstein, Ramanujan, Chudnovsky, Machin, Bishop/Bridges and Murray/Csimma attribution; existing DASHI source owners retained. New local checker is independent scalar residual verification, not a replacement production GMP backend.

## Execution

Local SymPy 1.14 / Python integers and Fraction, C++ GMP exact mpz_submul recurrence and independent mpz_addmul scatter convolution. First scalar-only Python attempt passed unit and diagonal but exceeded 90 seconds during slice. Replaced only expensive H*L Euler recurrence and residual evaluation with a small GMP reference helper, not approximate arithmetic. Full bounded rerun exit 0, 14.024 seconds wall as measured within Python, excluding compilation. No float used in any acceptance predicate.

| Finite specification | Exact result |
|---|---|
| unitOK | 3323/3323 discriminant coefficients + 3323/3323 J*U residuals; independently 3323/3323 eta inverse-product coefficients agree |
| diagOK | 3363/3363 Euler residual, 83/83 norm, 83/83 polynomial columns; H0=1, L0=0, N0=1 |
| sliceOK | 1723/1723 Euler residual, 43/43 norm, 43/43 polynomial columns; H0=1, L0=0, N0=1 |
| shiftOK | literal double zero and strict 80-term half-unit dominance |
| jetOK | all seven literal signed conditions, exact kappa cross |
| piRoundOK | both literal 128-bit rational Machin rounding inequalities |
| sqrtRoundOK | both integer square inequalities at the actual endpoints |
| expWindowOK | all five literal rational 180-term prefix/tail comparisons |

The degree-82 and degree-42 descending signed-hex coefficient arrays reconstructed locally give the exact original JSON Git blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4, 126 slots. Additionally parsed the two literal Lean arrays (blob 185fbf271b9089afc1ce123d2f53a21f5d89a6df) and compared every signed integer with the committed JSON: 83/83 and 43/43 exact matches. This pins the actual coefficient values; neither blob equality nor external arithmetic is a kernel proof.

Executed source files scripts/check_paper9_eight_finite_predicates.py (local Git blob abe036b682cfad6225932ffc22f279090148fbee) and scripts/paper9_gmp_residual.cpp (95012a4dfa03de5c2eab49c42123b29f1f8f9c74). From repository root:
```sh
g++ -O3 -std=c++17 scripts/paper9_gmp_residual.cpp -lgmpxx -lgmp -o scripts/paper9_gmp_residual
timeout 90s python scripts/check_paper9_eight_finite_predicates.py
```
Binary is local build output, not committed. Do not run Python with -O (assertions are load-bearing). This is a finite arithmetic reference, not independent analytic proof, nor the 10M-digit production performance gate.

## Source repairs and actual acceptance entrypoint

Lean branch research/paper9-original-eisenstein-derivative-20261125:
- 5202150f1ae4e4f1d87a49899a0dff158e8c7f75 / 76c1a47f1b8c895437c34f22fb91d0446791d5f3: correct expWindowOK owner to Paper9CMNormalizedCuspWindow, not Paper9CMExpWindow.
- 226b1cba791f308fe9a89d6edb2c6fbc880dd701: qualify shiftOK at Paper9CMShiftCheck.
- 075d1d6244bb0d079d5c99c1cfc3288da1d7a337: match rawTermValue's denominator form to prefixRat directly.
- 204c52d239af8641c1183f0e623036b625235879: Integration/Paper9NativeFiniteAcceptance.lean, eight named decide proofs, universalRawCross composed without new assumptions, print axioms. **UNCOMPILED**. Run with pinned local Lean/Mathlib checkout, initially elaborate dependencies with a bounded command, then this target. Plain decide may be impractical or require proof refactoring; do not replace with an externally asserted Boolean or silently introduce a trusted native oracle. No successful kernel/axiom audit claimed.

## Exact remaining cut

The independent finite arithmetic replay is paid. Native Lean elaboration of the complete analytic dependency chain and native acceptance of each finite predicate remain open. No Lean, Lake, Agda, gh in local PATH and direct remote download DNS failed. No CI invoked. Agda's actual all-index ExpandedCross still needs verified proof transportation or independent native proof; the finite replay does not supply it. The existing signed reflection and width/convergence consumers need no new observer layer. Full production performance acceptance and independent publication review remain. No Clay or novelty promotion.
