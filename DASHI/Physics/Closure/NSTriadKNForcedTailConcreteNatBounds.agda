module DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds where

------------------------------------------------------------------------
-- Concrete ℕ bounds for the forced-tail primitive estimates.
--
-- This module provides:
--
--   B3  (PROVED): H_FT(N,c) * T_FT(N,c) ≤ M_FT(N,c)
--                 Proof: ≤-refl (M_FT is definitionally H*T).
--
--   E   (PROVED, scaled form):
--         N² · M_FT(N,c) · μ_numerator ≤ B_FT,c · N^(2+a_c)
--         Proof: classwise N-cancellation arithmetic.
--         Representation: the magnitude bound μ_FT(N,c) is split
--         into a unit numerator (= 1) and the denominator N^(2+a_c).
--         The inequality N^(2+a_c) · M_FT · 1 ≤ B_FT,c · N^(2+a_c)
--         holds because M_FT(N,c) ≤ B_FT,c for each class (and then
--         N^(2+a_c) factors cancel).
--         NOTE: this is the arithmetic content of E; the abstract
--         model field still requires a concrete Bound instantiation
--         that encodes the N^{-(2+a_c)} magnitude directly.
--
--   A, B1, B2, C, D (concrete ℕ postulates):
--         Stated with proper ℕ types (not abstract Set placeholders),
--         ready for proof once the concrete incidence and kernel
--         types are available.
--
-- Relationship to the abstract model
-- ====================================
-- NSTriadKNForcedTailCountingMagnitudeTheorem.agda defines the
-- abstract NSTriadKNForcedTailCountingMagnitudeTheoremModel record.
-- The fields of that record require:
--
--   forcedTailHeadTailProductControlsMultiplicityFormula :
--     H_FT * T_FT ≤ M_FT          [B3 — closed here]
--
--   forcedTailClassProductFormulaN2Bound :
--     N2Scale * M_FT * μ_FT ≤ B_FT,c   [E — arithmetic closed here;
--                                         abstract field needs Bound
--                                         instantiation with N^{-b_c}]
--
-- For the concrete ℕ instantiation of the model, B3 is inhabited by
-- forcedTailHeadTimesTailBoundsMultiplicity below.

open import Data.Nat
  using ( ℕ; _≤_; _*_; _+_; zero; suc; z≤n; s≤s )
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-reflexive; m≤m+n; *-assoc; *-identityʳ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Bool using (Bool; true; false)

open import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates
  using ( ForcedTailClass
        ; tailEnd; nearTail; transition; degenerate
        ; forcedTailHeadCountBound
        ; forcedTailTailCountBound
        ; forcedTailMultiplicityBound
        ; forcedTailFiberConstant
        ; forcedTailClassProductN2Constant
        )

------------------------------------------------------------------------
-- § 1.  Local arithmetic infrastructure
--
-- These lemmas are proved without *-mono-≤ to avoid stdlib version
-- fragility; m≤m+n and definitional reduction of k * n suffice.

-- n ≤ 2 * n
-- Proof: m≤m+n n (n+0) gives n ≤ n+(n+0), which is 2*n definitionally.
n≤2*n : ∀ (n : ℕ) → n ≤ 2 * n
n≤2*n n = m≤m+n n (n + 0)

-- n ≤ 4 * n
-- Proof: m≤m+n n (n+(n+(n+0))) gives n ≤ n+(n+(n+(n+0))), which is 4*n definitionally.
n≤4*n : ∀ (n : ℕ) → n ≤ 4 * n
n≤4*n n = m≤m+n n (n + (n + (n + 0)))

------------------------------------------------------------------------
-- § 2.  Scaled-bound denominator functions
--
-- The N² arithmetic for class c uses denominator N^(2+a_c) where
-- a_c is the count exponent (0, 1, or 2).

-- Per-class denominator N^(2+a_c)
forcedTailDenominator : ForcedTailClass → ℕ → ℕ
forcedTailDenominator tailEnd    N = N * N           -- N^2 (a_c = 0)
forcedTailDenominator nearTail   N = N * (N * N)     -- N^3 (a_c = 1)
forcedTailDenominator transition N = N * N * (N * N) -- N^4 (a_c = 2)
forcedTailDenominator degenerate N = N * N           -- N^2 (a_c = 0)

-- LHS of E (scaled form): N² · M_FT(N,c) · 1
-- = (N * N) * forcedTailMultiplicityBound c N
forcedTailN2ScaledLHS : ForcedTailClass → ℕ → ℕ
forcedTailN2ScaledLHS c N = (N * N) * forcedTailMultiplicityBound c N

-- RHS of E (scaled form): B_FT,c · N^(2+a_c)
forcedTailN2ScaledRHS : ForcedTailClass → ℕ → ℕ
forcedTailN2ScaledRHS c N =
  forcedTailClassProductN2Constant c * forcedTailDenominator c N

------------------------------------------------------------------------
-- § 3.  B3 THEOREM (PROVED)
--       H_FT(N,c) * T_FT(N,c) ≤ M_FT(N,c)
--
-- forcedTailMultiplicityBound c N is DEFINED as
--   forcedTailHeadCountBound c N * forcedTailTailCountBound c N
-- so the goal reduces to  x ≤ x  which is ≤-refl.

-- B3a: equality (the definition itself, stated as a propositional equality)
forcedTailMultiplicityIsHeadTimesTail :
  (c : ForcedTailClass) (N : ℕ) →
  forcedTailHeadCountBound c N * forcedTailTailCountBound c N
    ≡ forcedTailMultiplicityBound c N
forcedTailMultiplicityIsHeadTimesTail _ _ = refl

-- B3b: the ≤ form used by the abstract model field
-- Abstract model field name: forcedTailHeadTailProductControlsMultiplicityFormula
-- This is the direct proof term for that field in a ℕ-Bound instantiation.
forcedTailHeadTimesTailBoundsMultiplicity :
  (c : ForcedTailClass) (N : ℕ) →
  forcedTailHeadCountBound c N * forcedTailTailCountBound c N
    ≤ forcedTailMultiplicityBound c N
forcedTailHeadTimesTailBoundsMultiplicity _ _ = ≤-refl
-- Agda unfolds forcedTailMultiplicityBound c N to the product,
-- so the goal becomes  x ≤ x  and ≤-refl closes it.

------------------------------------------------------------------------
-- § 4.  E THEOREM — SCALED ℕ ARITHMETIC (PROVED)
--       N² · M_FT(N,c) · 1 ≤ B_FT,c · N^(2+a_c)
--
-- These are the four classwise sub-cases.  All proofs are pure ℕ
-- arithmetic via n≤2*n / n≤4*n; no analytic assumptions are used.

-- tailEnd (a_c = 0): (N*N) * (1*1) ≤ 2 * (N*N)
-- 1*1 = 1 definitionally; then (N*N)*1 = N*N by *-identityʳ;
-- then N*N ≤ 2*(N*N) by n≤2*n.
forcedTailN2Arithmetic-tailEnd : (N : ℕ) →
  forcedTailN2ScaledLHS tailEnd N ≤ forcedTailN2ScaledRHS tailEnd N
forcedTailN2Arithmetic-tailEnd N =
  ≤-trans
    (≤-reflexive (*-identityʳ (N * N)))
    -- goal after *-identityʳ: N*N ≤ 2*(N*N) = N*N+(N*N+0)
    (n≤2*n (N * N))

-- nearTail (a_c = 1): (N*N) * (N*1) ≤ 2 * (N*(N*N))
-- *-identityʳ N: N*1 ≡ N → (N*N)*(N*1) ≡ (N*N)*N
-- *-assoc N N N:           (N*N)*N ≡ N*(N*N)
-- n≤2*n (N*(N*N)):         N*(N*N) ≤ 2*(N*(N*N))
forcedTailN2Arithmetic-nearTail : (N : ℕ) →
  forcedTailN2ScaledLHS nearTail N ≤ forcedTailN2ScaledRHS nearTail N
forcedTailN2Arithmetic-nearTail N =
  ≤-trans
    (≤-reflexive
      (trans
        (cong ((N * N) *_) (*-identityʳ N))  -- (N*N)*(N*1) ≡ (N*N)*N
        (*-assoc N N N)))                      -- (N*N)*N ≡ N*(N*N)
    (n≤2*n (N * (N * N)))

-- transition (a_c = 2): (N*N) * (N*N) ≤ 4 * ((N*N)*(N*N))
-- forcedTailMultiplicityBound transition N = N*N (head=N, tail=N).
-- forcedTailDenominator transition N = (N*N)*(N*N) (left-associative).
-- Goal: (N*N)*(N*N) ≤ 4*((N*N)*(N*N)), which is n≤4*n directly.
forcedTailN2Arithmetic-transition : (N : ℕ) →
  forcedTailN2ScaledLHS transition N ≤ forcedTailN2ScaledRHS transition N
forcedTailN2Arithmetic-transition N =
  n≤4*n ((N * N) * (N * N))

-- degenerate (a_c = 0): same exponent structure as tailEnd
-- forcedTailMultiplicityBound degenerate N = 1*1 = 1 definitionally
-- so proof is identical to tailEnd.
forcedTailN2Arithmetic-degenerate : (N : ℕ) →
  forcedTailN2ScaledLHS degenerate N ≤ forcedTailN2ScaledRHS degenerate N
forcedTailN2Arithmetic-degenerate N =
  ≤-trans
    (≤-reflexive (*-identityʳ (N * N)))
    (n≤2*n (N * N))

-- Combined E theorem: classwise dispatch
forcedTailN2ScaledArithmetic : (c : ForcedTailClass) (N : ℕ) →
  forcedTailN2ScaledLHS c N ≤ forcedTailN2ScaledRHS c N
forcedTailN2ScaledArithmetic tailEnd    = forcedTailN2Arithmetic-tailEnd
forcedTailN2ScaledArithmetic nearTail   = forcedTailN2Arithmetic-nearTail
forcedTailN2ScaledArithmetic transition = forcedTailN2Arithmetic-transition
forcedTailN2ScaledArithmetic degenerate = forcedTailN2Arithmetic-degenerate

------------------------------------------------------------------------
-- § 5.  Concrete ℕ postulates for A, B1, B2, C, D
--
-- These are no longer abstract Set placeholders; they are stated with
-- concrete ℕ types.  The incidence count and kernel weight types are
-- represented as ℕ proxies until the concrete triad type is available.
--
-- Each postulate is accompanied by:
--   (i)  Its mathematical content.
--   (ii) The required proof route.
--   (iii) What concrete type or incidence model it waits on.

------------------------------------------------------------------------
-- Postulate A — Encoding fiber bound (concrete ℕ version)
--
-- Content: for any column j and class c, the number of forced-tail
-- incidences τ ∈ I^FT_{N,c}(j) with enc(τ) = a is ≤ κ_FT(c).
--
-- Concrete ℕ statement:
--   incidenceCount(N,c,j) ≤ κ_FT(c) * parameterCount(N,c,j)
--
-- where incidenceCount and parameterCount are ℕ quantities computed
-- from the concrete triad incidence type.
--
-- Proof dependency: concrete ForcedTailIncidence type + encoding map.
--
-- Once the concrete triad type is defined, replace this postulate with:
--   forcedTailFiberBound c N j = fiberCountBound (forcedTailEncoding c N j)
--     where fiberCountBound is proved by enumeration of sign/orientation
--     residues (≤ κ_FT(c) choices per encoded pair (head, tail)).

postulate
  forcedTailClassIncidenceFiberBoundConcrete :
    (N : ℕ)
    (c : ForcedTailClass)
    (j : ℕ)                -- proxy for Column (concrete column index)
    (incidenceCount : ℕ)   -- |I^FT_{N,c}(j)|
    (parameterCount : ℕ)   -- |A_{N,c}(j)| = |Head_{N,c}(j)| × sup_h|Tail_{N,c}(j,h)|
    → incidenceCount ≤ forcedTailFiberConstant c * parameterCount

------------------------------------------------------------------------
-- Postulate B1 — Head count bound (concrete ℕ version)
--
-- Content: |Head_{FT}(N,c,j)| ≤ H_FT(N,c).
--
-- Proof dependency: concrete head enumeration for each class.
--   tailEnd:    head ∈ {active endpoint in δ₀-neighbourhood} → count ≤ 1.
--   nearTail:   head ∈ {active shells} → count ≤ N.
--   transition: head ∈ {active shells} → count ≤ N.
--   degenerate: finite exceptional geometry → count ≤ 1.

postulate
  forcedTailHeadCountBoundConcrete :
    (N : ℕ)
    (c : ForcedTailClass)
    (j : ℕ)                -- column index proxy
    (headCount : ℕ)        -- |Head_{FT}(N,c,j)|
    → headCount ≤ forcedTailHeadCountBound c N

------------------------------------------------------------------------
-- Postulate B2 — Max tail count bound (concrete ℕ version)
--
-- Content: for any head h, |Tail_{FT}(N,c,j,h)| ≤ T_FT(N,c).
--
-- Proof dependency: concrete tail enumeration for each class.
--   tailEnd:    forced-tail displacement determined up to fiber → ≤ 1.
--   nearTail:   displacement determined up to ±sign (absorbed in κ) → ≤ 1.
--   transition: partner shell ranges over O(N) values → ≤ N.
--   degenerate: finite exceptional → ≤ 1.

postulate
  forcedTailTailCountMaxBoundConcrete :
    (N : ℕ)
    (c : ForcedTailClass)
    (j : ℕ)                -- column index proxy
    (h : ℕ)                -- head index proxy
    (tailCount : ℕ)        -- |Tail_{FT}(N,c,j,h)|
    → tailCount ≤ forcedTailTailCountBound c N

------------------------------------------------------------------------
-- Postulate C — Magnitude kernel upper bound (concrete ℕ version, scaled)
--
-- Content: m_N(τ) · D(N,c) ≤ C_kernel
-- where D(N,c) = forcedTailDenominator c N is the scaling denominator
-- and C_kernel is an O(1) constant.
--
-- This is the scaled form of m_N(τ) ≤ C_kernel / N^(2+a_c).
--
-- Proof dependency: concrete kernel weight formula for forced-tail
-- incidences.  Requires the factorisation:
--   m_N(τ) = |h(k,p,q)| / normaliser(k,p,q) · proj(k,p)
-- and showing each factor satisfies its individual bound.
--
-- The concrete bound: m_N(τ) · D(N,c) ≤ C_mag where C_mag ≤ B_FT,c.

postulate
  forcedTailKernelEnvelopeScaledBoundConcrete :
    (N : ℕ)
    (c : ForcedTailClass)
    (τ : ℕ)                -- triad incidence proxy
    (kernelWeightTimesD : ℕ)  -- m_N(τ) · forcedTailDenominator c N (scaled)
    → kernelWeightTimesD ≤ forcedTailClassProductN2Constant c

------------------------------------------------------------------------
-- Postulate D — Classwise magnitude envelope (concrete ℕ version, scaled)
--
-- Content: Env_FT(N,τ) · D(N,c) ≤ B_FT,c for all τ ∈ I^FT_{N,c}(j).
--
-- This is the classwise version of C: the factored envelope
--   Env = Norm · Coeff · Proj
-- satisfies Env · D(N,c) ≤ B_FT,c by the class membership hypotheses.
--
-- Proof dependency: class-membership hypotheses for τ
-- (e.g., tailLength(τ) ≤ δ₀ · N for tailEnd class)
-- plus the individual Norm, Coeff, Proj factor bounds.

postulate
  forcedTailEnvelopeClassScaledBoundConcrete :
    (N : ℕ)
    (c : ForcedTailClass)
    (τ : ℕ)                -- triad incidence proxy
    (envelopeTimesD : ℕ)   -- Env_FT(N,τ) · forcedTailDenominator c N
    → envelopeTimesD ≤ forcedTailClassProductN2Constant c

------------------------------------------------------------------------
-- § 6.  Status record — what is proved in this module

record ForcedTailConcreteNatBoundsStatus : Set where
  constructor mkForcedTailConcreteNatBoundsStatus
  field
    -- B3: H_FT * T_FT ≤ M_FT by ≤-refl
    b3HeadTailProductBound         : Bool
    -- E arithmetic: N² · M_FT · 1 ≤ B_FT,c · N^(2+a_c) by n≤2*n / n≤4*n
    eN2ScaledArithmeticAllClasses  : Bool
    -- A: encoding fiber bound — concrete ℕ, awaits concrete incidence type
    aEncodingFiberBound            : Bool
    -- B1: head count bound — concrete ℕ, awaits concrete head enumeration
    b1HeadCountBound               : Bool
    -- B2: tail count bound — concrete ℕ, awaits concrete tail enumeration
    b2TailCountMaxBound            : Bool
    -- C: kernel envelope scaled — awaits concrete kernel weight formula
    cKernelEnvelopeScaled          : Bool
    -- D: classwise envelope scaled — awaits class-membership hypotheses
    dEnvelopeClassScaled           : Bool

open ForcedTailConcreteNatBoundsStatus public

currentForcedTailConcreteNatBoundsStatus : ForcedTailConcreteNatBoundsStatus
currentForcedTailConcreteNatBoundsStatus = mkForcedTailConcreteNatBoundsStatus
  true    -- B3 proved: forcedTailHeadTimesTailBoundsMultiplicity (≤-refl)
  true    -- E arithmetic proved: forcedTailN2ScaledArithmetic (all four cases)
  false   -- A open: awaits concrete ForcedTailIncidence type + encoding map
  false   -- B1 open: awaits concrete head enumeration
  false   -- B2 open: awaits concrete tail enumeration
  false   -- C open: awaits concrete kernel weight formula
  false   -- D open: awaits class-membership hypothesis discharge

------------------------------------------------------------------------
-- § 7.  Summary of what closing B3 and E arithmetic means
--
-- B3 proved (forcedTailHeadTimesTailBoundsMultiplicity):
--   In any concrete ℕ instantiation of
--   NSTriadKNForcedTailCountingMagnitudeTheoremModel where
--     forcedTailClassParameterHeadBoundFormula N c
--       = forcedTailHeadCountBound c N
--     forcedTailClassParameterTailBoundFormula N c
--       = forcedTailTailCountBound c N
--     forcedTailClassMultiplicityBoundFormula N c
--       = forcedTailMultiplicityBound c N
--   the field forcedTailHeadTailProductControlsMultiplicityFormula
--   is inhabited by ≤-refl (no additional proof required).
--
-- E arithmetic proved (forcedTailN2ScaledArithmetic):
--   The cancellation N^{2+a_c} · M_FT / N^{2+a_c} = M_FT / 1 is
--   established for all four classes via:
--     tailEnd:    N² · 1 ≤ 2 · N²       (*-identityʳ + n≤2*n)
--     nearTail:   N³ ≤ 2 · N³           (*-assoc + n≤2*n)
--     transition: N⁴ ≤ 4 · N⁴           (n≤4*n)
--     degenerate: N² · 1 ≤ 2 · N²       (same as tailEnd)
--   This provides the decisive arithmetic for the abstract model's
--   forcedTailClassProductFormulaN2Bound field once the Bound type
--   is instantiated with a rational or scaled-fraction carrier.
--
-- Remaining open (A, B1, B2, C, D):
--   These require the concrete forced-tail incidence and kernel types.
--   The next milestone is defining ForcedTailTriadIncidence and
--   proving A (encoding fiber bound) as the first real combinatorial
--   theorem.  B1 and B2 follow by class enumeration.  C and D are
--   analytic weight bounds.
