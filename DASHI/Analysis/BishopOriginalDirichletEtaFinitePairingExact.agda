module DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact where

------------------------------------------------------------------------
-- P2 real source promotion of finite eta--zeta pair reindexing.
--
-- Unlike the rational Q[i] finite donor, this file uses the ACTUAL
-- pinned Bishop ℝ Cartesian complex carrier of the native
-- original Dirichlet terms, and the actual selected Round11
-- exponential and canonical Nat-log term family.
--
-- For all complex s and ALL finite N:
--   eta_(2N)(s) + 2 * evenPositivePrefix_N(s) ≈C zeta_(2N)(s).
--
-- This is source-native SETOID ring equality. No integral, eta
-- convergence, analytic division by 1-2^(1-s), zero-free region,
-- Gamma, Xi, or actual analytic continuation is presumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Pointwise equality on the ACTUAL original Riemann-Bishop
-- Cartesian complex, without claiming intensional equality
-- of Cauchy-real records or introducing a synthetic quotient.
infix 4 _≈C_
_≈C_ : BC.BishopComplex → BC.BishopComplex → Set
left ≈C right =
  (R._≃_ (BC.re left) (BC.re right))
  ×
  (R._≃_ (BC.im left) (BC.im right))

≈C-trans : ∀ {x y z} → x ≈C y → y ≈C z → x ≈C z
≈C-trans left right =
  RP.≃-trans (proj₁ left) (proj₁ right)
  ,
  RP.≃-trans (proj₂ left) (proj₂ right)

addRightCongruent :
  ∀ {left right} →
  left ≈C right →
  (fixed : BC.BishopComplex) →
  BC._+C_ left fixed ≈C BC._+C_ right fixed
addRightCongruent equivalent fixed =
  RP.+-cong (proj₁ equivalent) RP.≃-refl
  ,
  RP.+-cong (proj₂ equivalent) RP.≃-refl

originalBishopPrefix :
  (Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalBishopPrefix term zero = BC.zeroC
originalBishopPrefix term (suc n) =
  BC._+C_ (originalBishopPrefix term n) (term n)

twice : Nat → Nat
twice n = n + n

originalEtaBlock originalUnsignedBlock originalEvenPositiveBlock :
  (Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalEtaBlock term n =
  BC._+C_ (term (twice n)) (BC.negC (term (suc (twice n))))
originalUnsignedBlock term n =
  BC._+C_ (term (twice n)) (term (suc (twice n)))
originalEvenPositiveBlock term n = term (suc (twice n))

originalEtaPrefix originalZetaPrefix originalEvenPositivePrefix :
  (Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalEtaPrefix term n =
  originalBishopPrefix (originalEtaBlock term) n
originalZetaPrefix term n =
  originalBishopPrefix (originalUnsignedBlock term) n
originalEvenPositivePrefix term n =
  originalBishopPrefix (originalEvenPositiveBlock term) n

originalBishopEtaStep :
  (eta even a b : BC.BishopComplex) →
  BC._+C_
    (BC._+C_ eta (BC._+C_ a (BC.negC b)))
    (BC._+C_ (BC._+C_ even b) (BC._+C_ even b))
  ≈C
  BC._+C_
    (BC._+C_ eta (BC._+C_ even even))
    (BC._+C_ a b)
originalBishopEtaStep
    (BC.bishop-complex er ei)
    (BC.bishop-complex vr vi)
    (BC.bishop-complex ar ai)
    (BC.bishop-complex br bi) =
  (let open RP.ℝ-Solver in
   solve 4
     (λ e v a b →
       (e ⊕ (a ⊕ (⊝ b))) ⊕ ((v ⊕ b) ⊕ (v ⊕ b))
       ⊜
       (e ⊕ (v ⊕ v)) ⊕ (a ⊕ b))
     RP.≃-refl er vr ar br)
  ,
  (let open RP.ℝ-Solver in
   solve 4
     (λ e v a b →
       (e ⊕ (a ⊕ (⊝ b))) ⊕ ((v ⊕ b) ⊕ (v ⊕ b))
       ⊜
       (e ⊕ (v ⊕ v)) ⊕ (a ⊕ b))
     RP.≃-refl ei vi ai bi)

originalBishopZeroEtaIdentity :
  BC._+C_ BC.zeroC (BC._+C_ BC.zeroC BC.zeroC) ≈C BC.zeroC
originalBishopZeroEtaIdentity =
  (let open RP.ℝ-Solver in
   solve 0
     (Κ 0ℚᵘ ⊕ (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
     RP.≃-refl)
  ,
  (let open RP.ℝ-Solver in
   solve 0
     (Κ 0ℚᵘ ⊕ (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
     RP.≃-refl)

-- A fully generic finite lemma on the ACTUAL pinned Bishop complex.
originalBishopEtaZetaPairing :
  (term : Nat → BC.BishopComplex) →
  (n : Nat) →
  BC._+C_
    (originalEtaPrefix term n)
    (BC._+C_ (originalEvenPositivePrefix term n)
              (originalEvenPositivePrefix term n))
  ≈C originalZetaPrefix term n
originalBishopEtaZetaPairing term zero =
  originalBishopZeroEtaIdentity
originalBishopEtaZetaPairing term (suc n) =
  ≈C-trans
    (originalBishopEtaStep
      (originalEtaPrefix term n)
      (originalEvenPositivePrefix term n)
      (term (twice n))
      (term (suc (twice n))))
    (addRightCongruent
      (originalBishopEtaZetaPairing term n)
      (originalUnsignedBlock term n))

-- A concrete instantation, not an arbitrary renamed eta/zeta.
-- EXACT SAME term family as
-- BishopRiemannOriginalZetaAboveTwoExact.FromOriginalNegativeLog.
module OriginalRound11DirichletEta
  (inputs : Round11.Round11BishopCutset)
  where

  sourceTerms : BC.BishopComplex → Nat → BC.BishopComplex
  sourceTerms =
    Terms.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate

  actualOriginalFiniteEtaZetaPairing :
    (s : BC.BishopComplex) →
    (n : Nat) →
    BC._+C_
      (originalEtaPrefix (sourceTerms s) n)
      (BC._+C_ (originalEvenPositivePrefix (sourceTerms s) n)
                (originalEvenPositivePrefix (sourceTerms s) n))
    ≈C originalZetaPrefix (sourceTerms s) n
  actualOriginalFiniteEtaZetaPairing s n =
    originalBishopEtaZetaPairing (sourceTerms s) n

-- Remaining analytic max-cut:
--  1. align this finite 2N prefix with the actual SeriesOf cutoff;
--  2. prove native even-source reindex to 2^(1-s)*zeta(s);
--  3. produce original eta convergence, uniform-on-compacts;
--  4. address divisor zeros and removable singularities;
--  5. weld to independently selected original Riemann analytic zeta.
