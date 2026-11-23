# YM P0 — source-unique two-mark four-column transport across CMP119 factorized steps (22 Nov 2026)

## Source owner / no duplication

Consume existing `BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda` (finite sum over admissible sequences; products over components; ordered products of T steps), `BalabanDifferentiatedMarkedFactorProductExact.agda` (ordinary first-order factor replacement telescope), `BalabanCMP119FactorizedDensityApproximationExact.agda` and the original #1536 `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda` (full interacting 1024 fine links with 896 spectators and exact same-source four coefficients). This note provides the missing EXPLICIT **two-source coefficient accounting** at the finite algebra level, not a second effective physical action, new analytic CMP119 bound, or another abstract polymer gas.

## Exact finite four-column formula

Use the square-free coefficient projection in Q[s,t]/(s^2,t^2). This projection retains exactly the 1/s/t/st original Wilson source jet, not the claim that the physical partition literally has independently replicated marks.

For each actual source factor indexed by i in one fixed original CMP119 sequence / component / ordered-step product, write A_i(s,t)=a_i+s b_i+t c_i+st d_i. If P=product_i A_i, then:

P_0=product_i a_i.
P_F=sum_i b_i product_{k!=i}a_k.
P_G=sum_i c_i product_{k!=i}a_k.
P_FG=sum_i d_i product_{k!=i}a_k + sum_{i!=j} b_i c_j product_{k notin {i,j}}a_k.

The residual sequence factor must be INCLUDED as a source factor if itself dependent on s or t; the admissible-sequence sum is componentwise linear, so the four columns sum over the source-selected domain sequences. This formula includes the intrinsic single-factor mixed Hessian AND all ordered cross-factor first-score contributions. Multiplication is associative in this truncated coefficient algebra. No division is needed, hence it remains valid even where an individual factor has zero base coefficient; taking log jets separately requires positive nonzero TOTAL density.

At any fixed slow field with actual positive K_0 and physical original normalized Z_0, the mixed log jet at zero of K_0+sK_F+tK_G+stK_FG is (K_0 K_FG-K_F K_G)/K_0^2, and must not be replaced with a product of separately integrated F/G marks.

## Strict one-copy source provenance

The two marks are each UNIQUE globally on the actual Wilson 4D gauge source. The factor-wise four columns may contain terms distributed over different factors, but they must arise from differentiation of ONE common original marked CMP119 density. Naively multiplying a copy of (1+sF) into each of two factors produces 2F instead of F as the s coefficient, even after square-free projection. Nilpotent bookkeeping alone does not solve provenance; the physical domain/index/step identification must prove the derivative of the actual K at the source origin equals the propagated 4-column coefficient.

For each original indexed H05 cube vertex/map retain (history, time, refinement, Frobenius, consumer) and original coarse Wilson full link support and 1/F/G/FG labels. The original L4 transverse eight-sheet address and six Wilson physical planes are NOT interchangeable with H05 8 vertices/12 maps/six commuting faces; 27=8+12+6+1 neutral/support/sign ternary states and actual signed cancellations do not imply absolute cluster charge 0.

## Local exact acceptance

Local /mnt/data/check_ym_cmp119_four_column_factor_transport_20261122.py executed: **85/85 exact SymPy rational factorization cases** (five product lengths 1..5, 17 rational source choices each), independently compared recursive coefficient convolution, the explicit single-factor/cross-factor formula, and coefficient extraction from ordinary polynomial expansion. Explicit negative controls prove a naive repeated global mark doubles the s coefficient and signed 3+(-3)=0 does not lower absolute sum 6. Finite algebra diagnostic, not actual CMP119 physical step extraction or Agda kernel. The companion committed compact source checker is a separate source file unless byte-identical local replay is explicitly established.

## Immediate actual source weld

1. Extract true original CMP119 (2.18)-(2.22) sequence/step indices and E/R/B/V factor roles on the correctly integrated F19 coarse Wilson source with all 896 interacting spectators.
2. Produce the physically **same globally unique affine-marked** source in each actual factor and residual, prove its 1/F/G/FG coefficient pushforward equals the original `K_0,K_F,K_G,K_FG` after product/sum/integration (with a true common measure). Use existing one-step marked error telescopes; do not instantiate arbitrary coefficient witnesses as original physics.
3. Bind the source-derived four-column jet to source-first normalized KP cluster log and per-support absolute differentiated activity, not just signed covariance. Pay sparse frustrated/mixed source geometry or valid Bałaban multiscale weak-coupling domain decomposition, large fields and boundary terms.
4. Bound `chargeSumBelowPhysicalRootedShell` with actual physical rate along beta(a)->infinity, uniform prefactor and cutoff/volume; use existing first-step MARKED R445 coarse q<11/20 at beta<=1/144 as an authentic but small-bare-beta donor only. E1/D1/D2/N1/G1 remain open.

Attribution: Wilson/Haar original finite marked source, Bałaban CMP119/122/116 and existing DASHI first-jet/marked product compiler, elementary commutative polynomial coefficient identities. No Agda kernel/CI/Clay success.
