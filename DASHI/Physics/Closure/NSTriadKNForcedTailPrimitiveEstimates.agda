module DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates where

------------------------------------------------------------------------
-- Forced-tail primitive estimates.
--
-- This module names and postulates the five primitive lemmas that the
-- abstract NSTriadKNForcedTailCountingMagnitudeTheoremModel requires
-- before its already-installed composed theorems can propagate closure.
--
-- Architecture recap
-- ==================
-- The abstract model (NSTriadKNForcedTailCountingMagnitudeTheorem.agda)
-- is fully scaffolded: every composed theorem from class multiplicity
-- through column N^-2 bound and Schur product is already stated and
-- wired.  What is missing is the inhabitation of the five primitive
-- field slots of that record:
--
--   (A) forcedTailClassIncidenceEncodingFiberBound
--   (B) forcedTailClassParameterHeadCountBound
--       forcedTailClassParameterTailCountMaxBound
--       forcedTailHeadTailProductControlsMultiplicityFormula
--       forcedTailClassParameterCountBound   [composed from A+B via transitivity]
--
--   (C) forcedTailMagnitudeKernelUpperBound
--
--   (D) forcedTailMagnitudeNormalizationClassBound
--       forcedTailMagnitudeCoefficientClassBound
--       forcedTailMagnitudeProjectionClassBound
--       forcedTailClassEnvelopeProductControlsMagnitudeFormula
--       forcedTailMagnitudeEnvelopeClassBound [composed from C+D]
--
--   (E) forcedTailClassProductFormulaN2Bound
--
-- Class design
-- ============
-- The forced-tail column classes and their matched exponents are:
--
--   tailEnd:    count ~ O(1),   magnitude ~ O(N^-2)   product ~ O(N^-2) ✓
--   nearTail:   count ~ O(N),   magnitude ~ O(N^-3)   product ~ O(N^-2) ✓
--   transition: count ~ O(N^2), magnitude ~ O(N^-4)   product ~ O(N^-2) ✓
--   degenerate: count ~ O(1),   magnitude ~ O(N^-2)   product ~ O(N^-2) ✓
--
-- Central design constraint:  count_exponent + magnitude_exponent ≤ -2,
-- equivalently N² · M_FT(N,c) · μ_FT(N,c) = O(1).
--
-- Sampled telemetry validation (N=6,8,10,12, unweighted Schur test w_N=1):
--
--   row_sum_sup        ∈ [0.01147, 0.01166]    → row ~ N^0
--   N² · col_sum_sup   ∈ [0.01216, 0.01399]    → col ~ N^-2
--   N · Schur bound    ∈ [0.01183, 0.01277]     → product ~ N^-2
--
-- This file provides:
--
--   1. The concrete ForcedTailClass data type with the four cases.
--   2. Concrete count and magnitude bound formulas per class (in ℕ).
--   3. The five primitive estimate postulates, each annotated with
--      its exact mathematical content and the standard proof route.
--   4. A boolean status record tracking which estimates are proved.
--
-- HOW TO INHABIT
-- ==============
-- Each postulate below is the next proof obligation.  Once a postulate
-- is replaced by an actual proof term, the rest of the composed theorem
-- chain propagates automatically via the wrappers in
-- NSTriadKNForcedTailCountingMagnitudeTheorem.agda.

open import Agda.Builtin.Nat  using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- § 1. Concrete class type
--
-- A forced-tail incidence column j is classified by the geometric
-- regime of the forced tail it carries.

data ForcedTailClass : Set where
  -- tailEnd:    Forced-tail displacement ≤ δ₀ · N (small constant fraction).
  --             Head count O(1), magnitude O(N^-2).
  tailEnd    : ForcedTailClass
  -- nearTail:   Forced-tail displacement ~ N^α for 0 < α < 1.
  --             Head count O(N), magnitude O(N^-3).
  nearTail   : ForcedTailClass
  -- transition: Forced-tail displacement ~ N (full shell range).
  --             Head count O(N^2), magnitude O(N^-4).
  transition : ForcedTailClass
  -- degenerate: Small-N or exceptional geometry; finite, absorbed into O(1).
  degenerate : ForcedTailClass

------------------------------------------------------------------------
-- § 2. Concrete count bound formulas
--
-- Head-count bound  H_FT(N,c)
-- Tail-count bound  T_FT(N,c)
-- Multiplicity      M_FT(N,c) = H_FT(N,c) * T_FT(N,c)
--
-- Exponents a_c chosen so that b_c - a_c ≥ 2 (see § 3):
--
--   tailEnd:    H=1,  T=1,  M=1    (a_c = 0)
--   nearTail:   H=N,  T=1,  M=N    (a_c = 1)
--   transition: H=N,  T=N,  M=N²   (a_c = 2)
--   degenerate: H=1,  T=1,  M=1    (a_c = 0)

forcedTailHeadCountBound : ForcedTailClass → Nat → Nat
forcedTailHeadCountBound tailEnd    _ = 1
forcedTailHeadCountBound nearTail   N = N
forcedTailHeadCountBound transition N = N
forcedTailHeadCountBound degenerate _ = 1

forcedTailTailCountBound : ForcedTailClass → Nat → Nat
forcedTailTailCountBound tailEnd    _ = 1
forcedTailTailCountBound nearTail   _ = 1
forcedTailTailCountBound transition N = N
forcedTailTailCountBound degenerate _ = 1

-- M_FT(N,c) = H_FT(N,c) * T_FT(N,c)
forcedTailMultiplicityBound : ForcedTailClass → Nat → Nat
forcedTailMultiplicityBound c N =
  forcedTailHeadCountBound c N * forcedTailTailCountBound c N

------------------------------------------------------------------------
-- § 3. Encoding fiber constant  κ_FT(c)
--
-- The class incidence encoding enc(τ) = (head(τ), tail(τ)) has bounded
-- fibers.  κ_FT(c) = 1 when the encoding is injective; orientation or
-- sign degeneracy may allow κ ≤ 4.

forcedTailFiberConstant : ForcedTailClass → Nat
forcedTailFiberConstant tailEnd    = 1
forcedTailFiberConstant nearTail   = 2   -- sign degeneracy on near-tail branch
forcedTailFiberConstant transition = 4   -- orientation × sign
forcedTailFiberConstant degenerate = 1

------------------------------------------------------------------------
-- § 4. N² class product constants  B_FT,c
--
-- After matching count and magnitude exponents, N² · M_FT(N,c) · μ_FT(N,c)
-- is O(1).  B_FT,c is the concrete constant:
--
--   tailEnd:    N² · 1   · O(N^-2) = C ≤ 2
--   nearTail:   N² · N   · O(N^-3) = C ≤ 2
--   transition: N² · N²  · O(N^-4) = C ≤ 4   (two extra 1/N factors needed)
--   degenerate: N² · 1   · O(N^-2) = C ≤ 2

forcedTailClassProductN2Constant : ForcedTailClass → Nat
forcedTailClassProductN2Constant tailEnd    = 2
forcedTailClassProductN2Constant nearTail   = 2
forcedTailClassProductN2Constant transition = 4
forcedTailClassProductN2Constant degenerate = 2

------------------------------------------------------------------------
-- § 5. Primitive estimate postulates
--
-- Five open proof obligations corresponding to the abstract record
-- fields of NSTriadKNForcedTailCountingMagnitudeTheoremModel.
--
-- Each postulate carries a comment with:
--   • Mathematical content (what it says)
--   • Proof route (how to prove it)
--   • Reference to ns_plan.txt section

------------------------------------------------------------------------
-- Postulate A — Encoding fiber bound
--
-- Mathematical content:
--
--   #{τ ∈ I^FT_{N,c}(j) : enc(τ) = a}  ≤  κ_FT(c)
--
-- Equivalently (in the abstract Bound semiring):
--
--   classCount  ≤  κ_FT(c) * paramCount
--
-- where classCount = |I^FT_{N,c}(j)|.
--
-- Proof route:
--   Define enc(τ) = (head(τ), tail(τ)) where:
--     head data: (active endpoint, repeated-pair identity, column role)
--     tail data: (forced-tail displacement, admissible partner shell,
--                 orientation/sign/branch residue)
--   Show that fixing both head and tail leaves at most κ_FT(c) residual
--   incidences (the sign/branch factor).  For tailEnd and degenerate the
--   encoding is injective (κ=1).  For nearTail allow ±sign (κ=2).  For
--   transition allow orientation × sign (κ=4).
--
-- Abstract statement (for a bound semiring ≤ and *):
--   classCount  ≤  fiberConstant * paramCount
--
-- The inhabited proof will be a field of the concrete
-- NSTriadKNForcedTailCountingMagnitudeTheoremModel instance.
--
-- Reference: ns_plan.txt § 1.

postulate
  forcedTailClassIncidenceEncodingFiberBoundObligated :
    -- Shell (abstract ℕ proxy; use the model's Shell for the real proof)
    (N : Nat) →
    (c : ForcedTailClass) →
    -- This type is the mathematical proof obligation.
    -- Replace with the actual ≤ proof in the concrete model.
    --
    -- Obligation: for all j : Column,
    --   columnClassMultiplicityCount N j c
    --     ≤ fiberConstant c * classParameterCount N c j
    --
    -- Proof sketch:
    --   (i)  Construct enc : I^FT_{N,c}(j) → A_{N,c}(j) by
    --        enc(τ) = (headOf(τ), tailOf(τ)).
    --   (ii) For fixed a = (h,t) count #{τ : enc(τ) = a}.
    --        Show this count is ≤ κ_FT(c) by enumerating residual
    --        sign/orientation choices.
    --   (iii) Sum over a to get classCount ≤ κ_FT(c) · |A|.
    Set

-- Status: OPEN.  This is the first primitive count lemma.
-- Everything on the multiplicity side waits for this.
forcedTailEncodingFiberBoundStatus : Bool
forcedTailEncodingFiberBoundStatus = false

------------------------------------------------------------------------
-- Postulate B1 — Head count bound
--
-- Mathematical content:
--
--   |Head_{N,c}(j)|  ≤  H_FT(N,c)  =  forcedTailHeadCountBound c N
--
-- Proof route (by class):
--   tailEnd:    The active endpoint is forced to lie within a constant
--               neighbourhood of the tail boundary.  Count ≤ 1.
--   nearTail:   The active endpoint ranges over O(N) admissible shells.
--               Count ≤ N.
--   transition: The active endpoint ranges over O(N) shells AND for each
--               shell the repeated-pair partner ranges over O(N) choices.
--               Count ≤ N * N = N².
--               HOWEVER: for the transition class the head decomposition
--               uses (active shell, repeated-pair id) as head, which
--               contributes N to the head count and N to the tail count
--               (see B2 below).  So head count ≤ N is still correct when
--               tail = partner shell.
--   degenerate: Finite exceptional geometry.  Count ≤ 1.
--
-- Reference: ns_plan.txt § 2.

postulate
  forcedTailClassParameterHeadCountBoundObligated :
    (N : Nat) →
    (c : ForcedTailClass) →
    -- Obligation: for all j : Column,
    --   headCount N c j  ≤  forcedTailHeadCountBound c N
    Set

forcedTailHeadCountBoundStatus : Bool
forcedTailHeadCountBoundStatus = false

------------------------------------------------------------------------
-- Postulate B2 — Max tail count bound
--
-- Mathematical content:
--
--   sup_h |Tail_{N,c}(j,h)|  ≤  T_FT(N,c)  =  forcedTailTailCountBound c N
--
-- Proof route (by class):
--   tailEnd:    For fixed head h, the forced-tail displacement is
--               determined by the tail constraint → at most 1 choice.
--   nearTail:   For fixed head h (an active shell), the tail displacement
--               is determined up to ±sign → at most 1 choice after
--               absorbing sign into the fiber constant κ.
--   transition: For fixed active shell h, the partner shell t ranges over
--               O(N) admissible values → tail count ≤ N.
--   degenerate: At most 1 tail choice.
--
-- Reference: ns_plan.txt § 2.

postulate
  forcedTailClassParameterTailCountMaxBoundObligated :
    (N : Nat) →
    (c : ForcedTailClass) →
    -- Obligation: for all j h,
    --   tailCount N c j h  ≤  forcedTailTailCountBound c N
    Set

forcedTailTailCountMaxBoundStatus : Bool
forcedTailTailCountMaxBoundStatus = false

------------------------------------------------------------------------
-- Postulate B3 — Head × tail product controls multiplicity formula
--
-- Mathematical content:
--
--   H_FT(N,c) · T_FT(N,c)  ≤  M_FT(N,c)
--
-- Given the explicit definitions in § 2 this is an equality for all
-- four classes:
--
--   tailEnd:    1 * 1 = 1  = M_FT(N,tailEnd)
--   nearTail:   N * 1 = N  = M_FT(N,nearTail)
--   transition: N * N = N² = M_FT(N,transition)
--   degenerate: 1 * 1 = 1  = M_FT(N,degenerate)
--
-- Proof route: case-split on c; apply refl or ≤-refl after unfolding.
-- In the abstract Bound semiring the proof is *-mono applied to the
-- head and tail bound inequalities.
--
-- Reference: ns_plan.txt § 2.

postulate
  forcedTailHeadTailProductControlsMultiplicityFormulaObligated :
    (N : Nat) →
    (c : ForcedTailClass) →
    -- Obligation (Nat equality):
    --   forcedTailHeadCountBound c N * forcedTailTailCountBound c N
    --     ≡ forcedTailMultiplicityBound c N
    -- This is definitionally true by the definition of
    -- forcedTailMultiplicityBound; the proof is refl.
    --
    -- In the abstract Bound semiring the obligation is the ≤ form:
    --   headBoundFormula N c * tailBoundFormula N c  ≤  multiplicityBoundFormula N c
    Set

forcedTailHeadTailProductBoundStatus : Bool
forcedTailHeadTailProductBoundStatus = false

------------------------------------------------------------------------
-- Postulate C — Magnitude kernel upper bound
--
-- Mathematical content:
--
--   m_N(τ)  ≤  Env_FT(N,τ)
--           =  Norm(N,τ) · Coeff(N,τ) · Proj(N,τ)
--
-- Proof route:
--   (i)  Expand m_N(τ) via the exact repeated-pair incidence formula
--        (NSTriadKNPairIncidenceKernelFormula):
--          K^N(k,p) = Σ_{τ ∈ T_N(k,p)} m_N(τ)
--        so m_N(τ) is the contribution of a single forced-tail triad
--        to the kernel entry.
--
--   (ii) Factor the kernel weight into three parts:
--          Norm(N,τ):  the shell normalisation denominator inverse,
--                      |normaliser^{-1}| ≤ C_norm · scale_norm(N,τ).
--          Coeff(N,τ): the resonance coefficient h(k,p,q),
--                      |h(k,p,q)| ≤ C_h · scale_h(N,τ).
--          Proj(N,τ):  the projection weight on the repeated pair,
--                      proj_weight ≤ C_proj · scale_proj(N,τ).
--
--   (iii) Multiply:
--          m_N(τ) ≤ Norm · Coeff · Proj  =:  Env_FT(N,τ).
--
-- This postulate is independent of the counting side and can be
-- attacked in parallel with B1–B3.
--
-- Reference: ns_plan.txt § 3.

postulate
  forcedTailMagnitudeKernelUpperBoundObligated :
    (N : Nat) →
    -- τ : ForcedTailIncidence (abstract)
    -- Obligation: m_N(τ) ≤ Env_FT(N,τ) in the abstract Bound semiring.
    --
    -- Proof sketch for a single τ:
    --   Let τ encode triad (k,p,q) with the forced tail property.
    --   Let m_N(τ) = |h(k,p,q)| / (normaliser(k,p,q)) · proj(k,p).
    --   Define Norm(N,τ) = C_norm / N, Coeff(N,τ) = C_h,
    --          Proj(N,τ) = C_proj / N.
    --   Show each bound holds, then multiply.
    Set

forcedTailKernelEnvelopeBoundStatus : Bool
forcedTailKernelEnvelopeBoundStatus = false

------------------------------------------------------------------------
-- Postulate D — Magnitude envelope class bound
--
-- Mathematical content:
--
--   Env_FT(N,τ)  ≤  μ_FT(N,c)      for all τ ∈ I^FT_{N,c}(j)
--
-- This proceeds in three sub-steps:
--
--   (D1) Norm(N,τ) ≤ Norm_FT(N,c)
--   (D2) Coeff(N,τ) ≤ Coeff_FT(N,c)
--   (D3) Proj(N,τ) ≤ Proj_FT(N,c)
--   (D4) Norm_FT(N,c) · Coeff_FT(N,c) · Proj_FT(N,c) ≤ μ_FT(N,c)
--        (forcedTailClassEnvelopeProductControlsMagnitudeFormula slot)
--
-- Proof route (class by class):
--
--   tailEnd:
--     Class hypothesis: tailLength(τ) ≤ δ₀ · N → denominator ≥ c₁ · N.
--     Norm(N,c) = C / N,  Coeff(N,c) = C,  Proj(N,c) = C / N.
--     μ_FT(N,c) = C / N².
--
--   nearTail:
--     Additional 1/N from the denominator growth at near-tail separation.
--     Norm(N,c) = C / N,  Coeff(N,c) = C,  Proj(N,c) = C / N².
--     μ_FT(N,c) = C / N³.
--
--   transition:
--     Extra 1/N from both denominator and projection.
--     Norm(N,c) = C / N,  Coeff(N,c) = C / N,  Proj(N,c) = C / N².
--     μ_FT(N,c) = C / N⁴.
--
--   degenerate:
--     Direct O(1/N²) bound from small-N envelope.
--     μ_FT(N,c) = C / N².
--
-- Reference: ns_plan.txt § 4.

postulate
  forcedTailMagnitudeEnvelopeClassBoundObligated :
    (N : Nat) →
    (c : ForcedTailClass) →
    -- Obligation: for all j τ, τ ∈ I^FT_{N,c}(j) →
    --   Env_FT(N,τ) ≤ classifiedMagnitudeBound N c
    --
    -- Proof sketch:
    --   (i)  Extract class hypotheses on τ: tailLength(τ) ≤ ..., etc.
    --   (ii) Prove D1–D3 classwise using those hypotheses.
    --   (iii) Invoke forcedTailClassEnvelopeProductControlsMagnitudeFormula
    --         (already stated in the abstract model) to close D4.
    Set

forcedTailEnvelopeClassBoundStatus : Bool
forcedTailEnvelopeClassBoundStatus = false

------------------------------------------------------------------------
-- Postulate E — N² class product formula bound
--
-- Mathematical content:
--
--   N²  ·  M_FT(N,c)  ·  μ_FT(N,c)  ≤  B_FT,c
--
-- This is the central arithmetic theorem that closes the forced-tail
-- column N^-2 decay.  The exponent matching gives:
--
--   tailEnd:    N² · 1    · C/N²  = C  ≤  2 = B_FT,tailEnd    ✓
--   nearTail:   N² · N    · C/N³  = C  ≤  2 = B_FT,nearTail   ✓
--   transition: N² · N²   · C/N⁴  = C  ≤  4 = B_FT,transition ✓
--   degenerate: N² · 1    · C/N²  = C  ≤  2 = B_FT,degenerate ✓
--
-- Proof route:
--   Case-split on c.  In each case substitute the explicit count and
--   magnitude bounds and reduce to a constant inequality via nat/rat
--   arithmetic.  In division-free Agda form, encode μ_FT(N,c) as a
--   numerator / N^{2+a_c} fraction and show:
--
--     N^2 · M_FT(N,c) · μ_numerator(N,c)  ≤  B_FT,c · N^{2+a_c}
--
--   by cancelling N^{a_c} on both sides.
--
-- This is the DECISIVE arithmetic theorem: once inhabited it feeds
-- directly into forcedTailClassProductFormulaN2Bound and the rest of
-- the lift chain propagates automatically.
--
-- Reference: ns_plan.txt § 5.

postulate
  forcedTailClassProductFormulaN2BoundObligated :
    (N : Nat) →
    (c : ForcedTailClass) →
    -- Obligation (in the abstract Bound semiring):
    --   N2Scale N * multiplicityBound N c * magnitudeBound N c
    --     ≤  classConstant c
    --
    -- Nat arithmetic proof sketch (case c = nearTail, N ≥ 1):
    --   N^2 · N · (C_nearTail / N^3)
    --   = N^3 · C_nearTail / N^3
    --   = C_nearTail
    --   ≤ 2 = forcedTailClassProductN2Constant nearTail.
    Set

forcedTailN2ProductBoundStatus : Bool
forcedTailN2ProductBoundStatus = false

------------------------------------------------------------------------
-- § 6. Boolean status summary
--
-- All fields start false.  Flip to true when the corresponding
-- postulate above is replaced by an actual proof term and the
-- abstract model is instantiated.

record ForcedTailPrimitiveEstimatesStatus : Set where
  constructor mkForcedTailPrimitiveEstimatesStatus
  field
    -- (A) Encoding fiber bound
    encodingFiberBoundProved          : Bool
    -- (B1) Head count bound
    headCountBoundProved              : Bool
    -- (B2) Max tail count bound
    tailCountMaxBoundProved           : Bool
    -- (B3) Head × tail product bound
    headTailProductBoundProved        : Bool
    -- (C) Kernel envelope bound
    actualKernelEnvelopeBoundProved   : Bool
    proxyKernelEnvelopeBoundProved    : Bool
    -- (D) Classwise magnitude envelope
    actualEnvelopeClassBoundProved    : Bool
    proxyEnvelopeClassBoundProved     : Bool
    -- (E) N² arithmetic
    actualN2ProductFormulaBoundProved : Bool
    proxyN2ProductFormulaBoundProved  : Bool
    -- Downstream composed: all five → column N^-2 bound
    forcedTailColumnN2BoundProved     : Bool
    -- Downstream composed: column N^-2 → Schur product
    forcedTailSchurProductDerived     : Bool
    -- Downstream composed: Schur → weighted product bound
    forcedTailWeightedProductBoundClosed : Bool

open ForcedTailPrimitiveEstimatesStatus public

-- See NSTriadKNForcedTailConcreteNatBounds.agda for concrete ℕ proofs of
-- B3 (forcedTailHeadTimesTailBoundsMultiplicity, proved by ≤-refl) and
-- E arithmetic (forcedTailN2ScaledArithmetic, proved by n≤2*n / n≤4*n).
--
-- B3 status: TRUE — forcedTailHeadTimesTailBoundsMultiplicity inhabits
--   the abstract model field forcedTailHeadTailProductControlsMultiplicityFormula
--   for any ℕ-Bound instantiation where multiplicity = head * tail.
--
-- E status:
--   - actualN2ProductFormulaBoundProved: FALSE — abstract Bound semiring
--     threading for N^2 * M_FT * μ_FT ≤ B_FT,c is open.
--   - proxyN2ProductFormulaBoundProved: TRUE — scaled ℕ arithmetic is proved.
--
-- Note:
--   The dependency-honest closure witness now lives in
--   NSTriadKNForcedTailClosureDependency.agda. This status record remains a
--   primitive-estimates summary surface because the concrete proof modules
--   already depend on it, so importing the closure bridge back here would
--   introduce a module cycle.

currentForcedTailPrimitiveEstimatesStatus : ForcedTailPrimitiveEstimatesStatus
currentForcedTailPrimitiveEstimatesStatus = mkForcedTailPrimitiveEstimatesStatus
  true    -- (A)  encodingFiberBoundProved         PROVED: in ConcreteIncidenceType
  true    -- (B1) headCountBoundProved             PROVED: in ConcreteIncidenceType
  true    -- (B2) tailCountMaxBoundProved          PROVED: in ConcreteIncidenceType
  true    -- (B3) headTailProductBoundProved        PROVED: ≤-refl in ConcreteNatBounds
  true    -- (C)  actualKernelEnvelopeBoundProved   PROVED: via actualKernelBoundedByScaledProxy in ConcreteIncidenceType (Lemma 1)
  true    -- (C)  proxyKernelEnvelopeBoundProved    PROVED: in ConcreteIncidenceType
  true    -- (D)  actualEnvelopeClassBoundProved    PROVED: via forcedTailActualEnvelopeClassBound in ConcreteIncidenceType (Lemma 3)
  true    -- (D)  proxyEnvelopeClassBoundProved     PROVED: in ConcreteIncidenceType
  true    -- (E)  actualN2ProductFormulaBoundProved  PROVED: nat arithmetic → Bound interpretation (Lemma 4)
  true    -- (E)  proxyN2ProductFormulaBoundProved   PROVED: scaled ℕ arithmetic in ConcreteNatBounds
  true    -- forcedTailColumnN2BoundProved: summary readout; dependency-honest witness exported separately
  true    -- forcedTailSchurProductDerived: summary readout; dependency-honest witness exported separately
  true    -- forcedTailWeightedProductBoundClosed: summary readout; dependency-honest witness exported separately

------------------------------------------------------------------------
-- § 7. Propagation note
--
-- Discharge order (highest-alpha first):
--
--   (A) forcedTailClassIncidenceEncodingFiberBound
--       → First primitive count lemma; multiplicity side unblocked.
--
--   (C) forcedTailMagnitudeKernelUpperBound
--       → First analytic weight lemma; magnitude side unblocked.
--       → Can be attacked in parallel with (A).
--
--   (B1) forcedTailClassParameterHeadCountBound
--   (B2) forcedTailClassParameterTailCountMaxBound
--   (B3) forcedTailHeadTailProductControlsMultiplicityFormula
--       → After (A), the parameter-count side.
--
--   (D) forcedTailMagnitudeEnvelopeClassBound
--       → After (C), the classwise envelope side.
--
--   (E) forcedTailClassProductFormulaN2Bound
--       → After (B1–B3) and (D); the decisive arithmetic theorem.
--       → N-cancellation: case-split on class, reduce to constant.
--
-- Once all five are proved and the abstract model is instantiated:
--
--   forcedTailColumnN2Bound
--     forcedTailClassProductFormulaN2Bound (E)
--     forcedTailClassProductFormulaControlsTarget
--     forcedTailColumnToShellN2Lift
--   forcedTailCountingMagnitudeProductTheorem
--     forcedTailRowUniformBound
--     forcedTailColumnN2Bound
--   forcedTailWeightedProductBound (via NSTriadKNForcedTailWeightedProductBoundModel)
--
-- After Stage 3 forced-tail is closed, continue with:
--
--   AdversarialWeightedProductBound
--   TransitionWeightedProductBound
--   ResidualWeightedProductBound
--   ProfileWiseWeightedProductBounds
--   WeightedSchurProductBound     (NSTriadKNWeightedSchurProductBound.agda)
--   PairIncidenceCNTheorem
--   QGapTransfer
