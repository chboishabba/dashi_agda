module DASHI.Crypto.MLKEMNTTPair03CubicRootFactorReductionExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS-203: PAIR (0,3) CUBIC ROOT-FACTOR REDUCTION
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
-- -------
-- The m=8 pair-(0,3) injectivity problem should not be proved by replaying all
-- 5^8 source candidates.  The actual FIPS points satisfy
--
--   a = gamma_0 = 17,     b = gamma_3 = 568,
--   a^4 = b^4 = 296      in F_3329.
--
-- Hence an eight-coordinate difference vector d compresses 4+4 into
--
--   e_j = d_j + 296 d_(j+4),  j=0,1,2,3,
--
-- and the two zero-signature equations are exactly the statement that the cubic
--
--   E(X) = e0 + e1 X + e2 X^2 + e3 X^3
--
-- vanishes at a and b.
--
-- This module proves the algebraic reduction independently of F_3329's concrete
-- representation.  If multiplication by (b-a) reflects zero, then two roots
-- force
--
--   E(X) = (X-a)(X-b)(p + q X),
--
-- with
--
--   q = e3,
--   p = e2 + (a+b)e3,
--   e0 = ab p,
--   e1 = ab q - (a+b)p.
--
-- For the actual constants, a+b=585 and ab=-331 (mod 3329), yielding the
-- compact 81^2 certificate used by
-- `scripts/crypto_ntt_pair03_compact_injectivity_certificate.py`.
--
-- BLUE-TEAM BOUNDARY
-- ------------------
-- This is a raw-signature kernel reduction only.  It makes no claim that any
-- implementation exposes the raw residues, and it is not a whole-key or
-- runtime theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (nothing)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; _*_ to _⊗_
      ; -_ to neg
      ; 0# to 0F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  infixl 6 _⊖_
  _⊖_ : F → F → F
  x ⊖ y = x ⊕ neg y

  square : F → F
  square x = x ⊗ x

  cube : F → F
  cube x = square x ⊗ x

  record Cubic : Set c where
    constructor cubic
    field
      c0 c1 c2 c3 : F

  open Cubic public

  eval : Cubic → F → F
  eval polynomial x =
    c0 polynomial
    ⊕ (c1 polynomial ⊗ x)
    ⊕ (c2 polynomial ⊗ square x)
    ⊕ (c3 polynomial ⊗ cube x)

  record DifferenceZeroReflecting (a b : F) : Set c where
    constructor difference-zero-reflecting
    field
      reflectsZero :
        (x : F) →
        ((b ⊖ a) ⊗ x) ≡ 0F →
        x ≡ 0F

  open DifferenceZeroReflecting public

  factorQ : Cubic → F
  factorQ polynomial = c3 polynomial

  factorP : F → F → Cubic → F
  factorP a b polynomial =
    c2 polynomial ⊕ ((a ⊕ b) ⊗ c3 polynomial)

  expectedC0 : F → F → Cubic → F
  expectedC0 a b polynomial =
    (a ⊗ b) ⊗ factorP a b polynomial

  expectedC1 : F → F → Cubic → F
  expectedC1 a b polynomial =
    ((a ⊗ b) ⊗ factorQ polynomial)
    ⊖ ((a ⊕ b) ⊗ factorP a b polynomial)

  rootDifferenceFactors :
    (a b : F) →
    (polynomial : Cubic) →
    eval polynomial a ≡ 0F →
    eval polynomial b ≡ 0F →
    ((b ⊖ a) ⊗
      (c1 polynomial
       ⊕ ((a ⊕ b) ⊗ c2 polynomial)
       ⊕ ((square a ⊕ (a ⊗ b) ⊕ square b) ⊗ c3 polynomial)))
      ≡ 0F
  rootDifferenceFactors a b polynomial rootA rootB =
    S.solve 6
      (λ a b c0 c1 c2 c3 →
        ((b S.⊕ (S.⊖ a)) S.⊗
          (c1
           S.⊕ ((a S.⊕ b) S.⊗ c2)
           S.⊕ (((a S.⊗ a) S.⊕ (a S.⊗ b) S.⊕ (b S.⊗ b)) S.⊗ c3)))
          S.⊜ S.con 0)
      rootA rootB
      a b
      (c0 polynomial) (c1 polynomial) (c2 polynomial) (c3 polynomial)

  rootsForceC1 :
    (a b : F) →
    (polynomial : Cubic) →
    DifferenceZeroReflecting a b →
    eval polynomial a ≡ 0F →
    eval polynomial b ≡ 0F →
    c1 polynomial ≡ expectedC1 a b polynomial
  rootsForceC1 a b polynomial differenceReflects rootA rootB =
    S.solve 6
      (λ a b c0 c1 c2 c3 →
        c1 S.⊜
          ((a S.⊗ b) S.⊗ c3)
          S.⊕
          (S.⊖ ((a S.⊕ b) S.⊗ (c2 S.⊕ ((a S.⊕ b) S.⊗ c3)))))
      bracketZero
      a b
      (c0 polynomial) (c1 polynomial) (c2 polynomial) (c3 polynomial)
    where
    bracketZero :
      c1 polynomial
      ⊕ ((a ⊕ b) ⊗ c2 polynomial)
      ⊕ ((square a ⊕ (a ⊗ b) ⊕ square b) ⊗ c3 polynomial)
      ≡ 0F
    bracketZero =
      reflectsZero differenceReflects
        (c1 polynomial
         ⊕ ((a ⊕ b) ⊗ c2 polynomial)
         ⊕ ((square a ⊕ (a ⊗ b) ⊕ square b) ⊗ c3 polynomial))
        (rootDifferenceFactors a b polynomial rootA rootB)

  rootsForceC0 :
    (a b : F) →
    (polynomial : Cubic) →
    DifferenceZeroReflecting a b →
    eval polynomial a ≡ 0F →
    eval polynomial b ≡ 0F →
    c0 polynomial ≡ expectedC0 a b polynomial
  rootsForceC0 a b polynomial differenceReflects rootA rootB =
    S.solve 6
      (λ a b c0 c1 c2 c3 →
        c0 S.⊜
          (a S.⊗ b) S.⊗ (c2 S.⊕ ((a S.⊕ b) S.⊗ c3)))
      rootA c1Exact
      a b
      (c0 polynomial) (c1 polynomial) (c2 polynomial) (c3 polynomial)
    where
    c1Exact : c1 polynomial ≡ expectedC1 a b polynomial
    c1Exact =
      rootsForceC1 a b polynomial differenceReflects rootA rootB

  record CubicTwoRootFactorisation
      (a b : F) (polynomial : Cubic) : Set c where
    constructor cubic-two-root-factorisation
    field
      p : F
      q : F
      qIsLeading : q ≡ c3 polynomial
      pIsNext : p ≡ c2 polynomial ⊕ ((a ⊕ b) ⊗ c3 polynomial)
      c0IsProduct : c0 polynomial ≡ (a ⊗ b) ⊗ p
      c1IsMiddle :
        c1 polynomial ≡ ((a ⊗ b) ⊗ q) ⊖ ((a ⊕ b) ⊗ p)

  open CubicTwoRootFactorisation public

  twoRootsGiveLinearTimesQuadratic :
    (a b : F) →
    (polynomial : Cubic) →
    DifferenceZeroReflecting a b →
    eval polynomial a ≡ 0F →
    eval polynomial b ≡ 0F →
    CubicTwoRootFactorisation a b polynomial
  twoRootsGiveLinearTimesQuadratic a b polynomial differenceReflects rootA rootB =
    cubic-two-root-factorisation
      (factorP a b polynomial)
      (factorQ polynomial)
      refl
      refl
      (rootsForceC0 a b polynomial differenceReflects rootA rootB)
      (rootsForceC1 a b polynomial differenceReflects rootA rootB)

------------------------------------------------------------------------
-- SOURCE-SPECIFIC REMAINDER
--
-- The remaining F_3329 producer is now precise and small:
--   * realize 17 and 568 in the field;
--   * prove 568-17 is nonzero/invertible, hence zero-reflecting;
--   * prove 17^4 = 568^4 = 296;
--   * prove 17+568 = 585 and 17*568 = -331;
--   * discharge the reduced 81^2 bounded-coefficient kernel certificate.
--
-- No 390625-case secret enumeration is required by this reduction.
------------------------------------------------------------------------
