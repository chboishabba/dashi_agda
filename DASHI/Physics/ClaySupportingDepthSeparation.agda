module DASHI.Physics.ClaySupportingDepthSeparation where

------------------------------------------------------------------------
-- Elementary, fully-proved depth-separation weight-ratio lemma (NS-8).
--
-- Companion to `DASHI.Physics.ClaySupportingElementaryLemmas` etc.  As in
-- those modules, every declaration here is a genuine Agda proof over
-- concrete natural numbers: there are NO `postulate`s and NO added axioms.
--
-- This supplies the NS package §A3.2 forced-tail geometry step.  With the
-- dyadic weight  w k = 2^{D − d(k)}  (depths bounded by D), the depth
-- separation  d(i) + ℓ ≤ d(j)  together with the calibration  N+1 ≤ 2^ℓ
-- yields the weight-ratio inequality  (N+1)·w(j) ≤ w(i)  (eqn NS-8), the
-- quantitative input behind the restricted-row estimates R^{FT→adv} ≤ A/N.
--
-- Supporting fully-proved arithmetic:
--   pow-2-pos           1 ≤ 2ⁿ
--   pow-2-mono          a ≤ b ⇒ 2ᵃ ≤ 2ᵇ
--   pow-+               2^{m+k} = 2ᵐ·2ᵏ
--   exp-split           di ≤ dj ≤ D ⇒ D−di = (dj−di)+(D−dj)
--   depthSeparationWeightRatio  the NS-8 inequality itself
--
-- Honesty boundary (unchanged and deliberate): this is the elementary
-- weight arithmetic only.  It does NOT discharge the open analytic leaf
-- (that the actual FT→adv incidence kernel enjoys depth separation, i.e.
-- the geometric hypothesis  d(i)+ℓ ≤ d(j)); that is left as the explicit
-- hypothesis of the theorem, not asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( +-comm; +-∸-assoc; +-∸-comm; m∸n+n≡m; n∸n≡0; m≤m+n
        ; *-identityˡ; *-assoc; *-mono-≤; ∸-monoˡ-≤
        ; ≤-refl; ≤-trans )
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

------------------------------------------------------------------------
-- §1.  Powers of two: positivity, exponent-monotonicity, additivity.

pow-2-pos : ∀ n → 1 ≤ pow 2 n
pow-2-pos zero    = ≤-refl
pow-2-pos (suc n) =
  ≤-trans (pow-2-pos n) (m≤m+n (pow 2 n) (pow 2 n + 0))

pow-2-mono : ∀ {a b} → a ≤ b → pow 2 a ≤ pow 2 b
pow-2-mono {zero}  {b}     z≤n       = pow-2-pos b
pow-2-mono {suc a} {suc b} (s≤s a≤b) =
  *-mono-≤ (≤-refl {2}) (pow-2-mono a≤b)

pow-+ : ∀ b m k → pow b (m + k) ≡ pow b m * pow b k
pow-+ b zero    k = sym (*-identityˡ (pow b k))
pow-+ b (suc m) k =
  trans (cong (b *_) (pow-+ b m k))
        (sym (*-assoc b (pow b m) (pow b k)))

------------------------------------------------------------------------
-- §2.  Subtraction-exponent split:  D∸di = (dj∸di) + (D∸dj)  when di ≤ dj ≤ D.

exp-split :
  ∀ {di dj D} → di ≤ dj → dj ≤ D → D ∸ di ≡ (dj ∸ di) + (D ∸ dj)
exp-split {di} {dj} {D} di≤dj dj≤D =
  trans (cong (_∸ di) (sym (m∸n+n≡m dj≤D)))
    (trans (+-∸-assoc (D ∸ dj) di≤dj)
           (+-comm (D ∸ dj) (dj ∸ di)))

-- ℓ ≤ dj ∸ di   from   di + ℓ ≤ dj.
gap-lower : ∀ {di ℓ dj} → di + ℓ ≤ dj → ℓ ≤ dj ∸ di
gap-lower {di} {ℓ} {dj} h =
  subst (_≤ dj ∸ di) eqℓ (∸-monoˡ-≤ di h)
  where
    eqℓ : (di + ℓ) ∸ di ≡ ℓ
    eqℓ = trans (+-∸-comm ℓ (≤-refl {di})) (cong (_+ ℓ) (n∸n≡0 di))

------------------------------------------------------------------------
-- §3.  The NS-8 depth-separation weight-ratio inequality.
--
-- Weights are dyadic:  w(k) = 2^{D − d(k)}, with every depth d(k) ≤ D.
-- Depth separation  d(i) + ℓ ≤ d(j)  and the calibration  N+1 ≤ 2^ℓ  give
--   (N+1) · w(j) ≤ w(i).

depthSeparationWeightRatio :
  {K : Set} (D : ℕ) (d : K → ℕ) (i j : K) (ℓ N : ℕ) →
  d j ≤ D →
  d i + ℓ ≤ d j →
  suc N ≤ pow 2 ℓ →
  suc N * pow 2 (D ∸ d j) ≤ pow 2 (D ∸ d i)
depthSeparationWeightRatio D d i j ℓ N dj≤D sep calib =
  subst (λ z → suc N * pow 2 (D ∸ d j) ≤ z) (sym step)
        (*-mono-≤ sucN≤ (≤-refl {pow 2 (D ∸ d j)}))
  where
    di≤dj : d i ≤ d j
    di≤dj = ≤-trans (m≤m+n (d i) ℓ) sep

    -- w(i) = 2^{dj−di} · w(j)
    step : pow 2 (D ∸ d i) ≡ pow 2 (d j ∸ d i) * pow 2 (D ∸ d j)
    step =
      trans (cong (pow 2) (exp-split di≤dj dj≤D))
            (pow-+ 2 (d j ∸ d i) (D ∸ d j))

    -- N+1 ≤ 2^ℓ ≤ 2^{dj−di}
    sucN≤ : suc N ≤ pow 2 (d j ∸ d i)
    sucN≤ = ≤-trans calib (pow-2-mono (gap-lower {d i} {ℓ} {d j} sep))
