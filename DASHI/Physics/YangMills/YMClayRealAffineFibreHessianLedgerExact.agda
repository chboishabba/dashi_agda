module DASHI.Physics.YangMills.YMClayRealAffineFibreHessianLedgerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I", Communications in
-- Mathematical Physics 122 (1989), 175--202. DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II", Communications in
-- Mathematical Physics 122 (1989), 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Kernel-check the real affine two-mark determinant ledger
--   K(W;s,t) = K0 + s KF + t KG + st KFG
--   D_s K    = KF + t KFG
--   D_t K    = KG + s KFG
--   det      = K D_t,t K - D_s K D_t K = K0 KFG - KF KG
-- and the connected-covariance inverse identity.  The inverse is an explicit
-- hypothesis `k0 * inv ≡ 1`; no field/inverse postulate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_;
   +-assoc; +-comm; +-identityʳ;
   subSelf; subAddDistributes; subMulDistributes;
   *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+; mulOneʳ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

cancelRight :
  ∀ (p q t : ℝ) →
    (p +ℝ q) -ℝ (t +ℝ q) ≡ p -ℝ t
cancelRight p q t =
  trans
    (subAddDistributes p q t q)
    (trans
      (cong (λ z → (p -ℝ t) +ℝ z) (subSelf q))
      (+-identityʳ (p -ℝ t)))

cancelThree :
  ∀ (p q r t : ℝ) →
    ((p +ℝ q) +ℝ r) -ℝ ((t +ℝ q) +ℝ r) ≡ p -ℝ t
cancelThree p q r t =
  trans
    (subAddDistributes (p +ℝ q) r (t +ℝ q) r)
    (trans
      (cong (λ z → ((p +ℝ q) -ℝ (t +ℝ q)) +ℝ z) (subSelf r))
      (trans
        (+-identityʳ ((p +ℝ q) -ℝ (t +ℝ q)))
        (cancelRight p q t)))

cancelFour :
  ∀ (p q r s t : ℝ) →
    (((p +ℝ q) +ℝ r) +ℝ s) -ℝ (((t +ℝ q) +ℝ r) +ℝ s) ≡ p -ℝ t
cancelFour p q r s t =
  trans
    (subAddDistributes ((p +ℝ q) +ℝ r) s ((t +ℝ q) +ℝ r) s)
    (trans
      (cong
        (λ z → (((p +ℝ q) +ℝ r) -ℝ ((t +ℝ q) +ℝ r)) +ℝ z)
        (subSelf s))
      (trans
        (+-identityʳ (((p +ℝ q) +ℝ r) -ℝ ((t +ℝ q) +ℝ r)))
        (cancelThree p q r t)))

mulFourRight :
  ∀ (a b c d e : ℝ) →
    (((a +ℝ b) +ℝ c) +ℝ d) *ℝ e
      ≡ (((a *ℝ e) +ℝ (b *ℝ e)) +ℝ (c *ℝ e)) +ℝ (d *ℝ e)
mulFourRight a b c d e =
  trans
    (*-distribʳ-+ ((a +ℝ b) +ℝ c) d e)
    (trans
      (cong (λ z → z +ℝ (d *ℝ e)) (*-distribʳ-+ (a +ℝ b) c e))
      (cong
        (λ z → (z +ℝ (c *ℝ e)) +ℝ (d *ℝ e))
        (*-distribʳ-+ a b e)))

mulMixedExpansion :
  ∀ (b y d c x : ℝ) →
    (b +ℝ (y *ℝ d)) *ℝ (c +ℝ (x *ℝ d))
      ≡ (((b *ℝ c) +ℝ (b *ℝ (x *ℝ d)))
          +ℝ ((y *ℝ d) *ℝ c)) +ℝ ((y *ℝ d) *ℝ (x *ℝ d))
mulMixedExpansion b y d c x =
  trans
    (*-distribʳ-+ b (y *ℝ d) (c +ℝ (x *ℝ d)))
    (trans
      (cong
        (λ z → z +ℝ ((y *ℝ d) *ℝ (c +ℝ (x *ℝ d))))
        (*-distribˡ-+ b c (x *ℝ d)))
      (trans
        (cong
          (λ z → ((b *ℝ c) +ℝ (b *ℝ (x *ℝ d))) +ℝ z)
          (*-distribˡ-+ (y *ℝ d) c (x *ℝ d)))
        (sym
          (+-assoc
            ((b *ℝ c) +ℝ (b *ℝ (x *ℝ d)))
            ((y *ℝ d) *ℝ c)
            ((y *ℝ d) *ℝ (x *ℝ d))))))

mulSwapRight :
  ∀ (a b c : ℝ) →
    (a *ℝ b) *ℝ c ≡ (a *ℝ c) *ℝ b
mulSwapRight a b c =
  trans
    (*-assoc a b c)
    (trans
      (cong (λ z → a *ℝ z) (*-comm b c))
      (sym (*-assoc a c b)))

mulSwapLeft :
  ∀ (a b c : ℝ) →
    (a *ℝ b) *ℝ c ≡ (b *ℝ c) *ℝ a
mulSwapLeft a b c =
  trans (*-assoc a b c) (*-comm a (b *ℝ c))

mulSwapToOuterRight :
  ∀ (a b c : ℝ) →
    (a *ℝ b) *ℝ c ≡ b *ℝ (a *ℝ c)
mulSwapToOuterRight a b c =
  trans (mulSwapRight a b c) (*-comm (a *ℝ c) b)

mulFourReorder :
  ∀ (a b c d : ℝ) →
    ((a *ℝ b) *ℝ c) *ℝ d ≡ (b *ℝ c) *ℝ (a *ℝ d)
mulFourReorder a b c d =
  trans
    (mulSwapRight (a *ℝ b) c d)
    (trans
      (cong (λ z → z *ℝ c) (mulSwapRight a b d))
      (mulSwapLeft ((a *ℝ d)) b c))

affineMass :
  (k0 kf kg kfg s t : ℝ) →
  ℝ
affineMass k0 kf kg kfg s t =
  ((k0 +ℝ (s *ℝ kf)) +ℝ (t *ℝ kg)) +ℝ ((s *ℝ t) *ℝ kfg)

affineSMassDerivative :
  (kf kg kfg s t : ℝ) →
  ℝ
affineSMassDerivative kf kg kfg s t =
  kf +ℝ (t *ℝ kfg)

affineTMassDerivative :
  (kf kg kfg s t : ℝ) →
  ℝ
affineTMassDerivative kf kg kfg s t =
  kg +ℝ (s *ℝ kfg)

affineMassDeterminant :
  ∀ (k0 kf kg kfg s t : ℝ) →
    affineMass k0 kf kg kfg s t *ℝ kfg
      -ℝ (affineSMassDerivative kf kg kfg s t
          *ℝ affineTMassDerivative kf kg kfg s t)
    ≡ (k0 *ℝ kfg) -ℝ (kf *ℝ kg)
affineMassDeterminant k0 kf kg kfg s t =
  let
    leftExpanded :
      affineMass k0 kf kg kfg s t *ℝ kfg
        ≡ (((k0 *ℝ kfg) +ℝ ((s *ℝ kf) *ℝ kfg))
            +ℝ ((t *ℝ kg) *ℝ kfg))
            +ℝ (((s *ℝ t) *ℝ kfg) *ℝ kfg)
    leftExpanded = mulFourRight k0 (s *ℝ kf) (t *ℝ kg)
      ((s *ℝ t) *ℝ kfg) kfg

    rightExpanded :
      affineSMassDerivative kf kg kfg s t
        *ℝ affineTMassDerivative kf kg kfg s t
        ≡ (((kf *ℝ kg) +ℝ (kf *ℝ (s *ℝ kfg)))
            +ℝ ((t *ℝ kfg) *ℝ kg))
            +ℝ ((t *ℝ kfg) *ℝ (s *ℝ kfg))
    rightExpanded = mulMixedExpansion kf t kfg kg s

    leftReordered :
      (((k0 *ℝ kfg) +ℝ ((s *ℝ kf) *ℝ kfg))
          +ℝ ((t *ℝ kg) *ℝ kfg))
          +ℝ (((s *ℝ t) *ℝ kfg) *ℝ kfg)
        ≡ (((k0 *ℝ kfg) +ℝ (kf *ℝ (s *ℝ kfg)))
            +ℝ ((t *ℝ kfg) *ℝ kg))
            +ℝ ((t *ℝ kfg) *ℝ (s *ℝ kfg))
    leftReordered =
      trans
        (cong
          (λ z → ((k0 *ℝ kfg) +ℝ z) +ℝ ((t *ℝ kg) *ℝ kfg)
                    +ℝ (((s *ℝ t) *ℝ kfg) *ℝ kfg))
          (mulSwapToOuterRight s kf kfg))
        (trans
          (cong
            (λ z → ((k0 *ℝ kfg) +ℝ (kf *ℝ (s *ℝ kfg))) +ℝ z
                      +ℝ (((s *ℝ t) *ℝ kfg) *ℝ kfg))
            (mulSwapRight t kg kfg))
          (cong
            (λ z → ((k0 *ℝ kfg) +ℝ (kf *ℝ (s *ℝ kfg)))
                      +ℝ ((t *ℝ kfg) *ℝ kg) +ℝ z)
            (mulFourReorder s t kfg kfg)))
  in
  trans
    (cong
      (λ z → z -ℝ (affineSMassDerivative kf kg kfg s t
                    *ℝ affineTMassDerivative kf kg kfg s t))
      leftExpanded)
    (trans
      (cong
        (λ z →
          ((((k0 *ℝ kfg) +ℝ ((s *ℝ kf) *ℝ kfg))
              +ℝ ((t *ℝ kg) *ℝ kfg))
              +ℝ (((s *ℝ t) *ℝ kfg) *ℝ kfg)) -ℝ z)
        {affineSMassDerivative kf kg kfg s t
           *ℝ affineTMassDerivative kf kg kfg s t}
        {(((kf *ℝ kg) +ℝ (kf *ℝ (s *ℝ kfg)))
           +ℝ ((t *ℝ kfg) *ℝ kg))
           +ℝ ((t *ℝ kfg) *ℝ (s *ℝ kfg))}
        rightExpanded)
      (trans
        (cong
          (λ z → z -ℝ
            ((((kf *ℝ kg) +ℝ (kf *ℝ (s *ℝ kfg)))
                +ℝ ((t *ℝ kfg) *ℝ kg))
                +ℝ ((t *ℝ kfg) *ℝ (s *ℝ kfg))))
          leftReordered)
        (cancelFour
          (k0 *ℝ kfg) (kf *ℝ (s *ℝ kfg))
          ((t *ℝ kfg) *ℝ kg) ((t *ℝ kfg) *ℝ (s *ℝ kfg))
          (kf *ℝ kg))))

rightInverseFactor :
  ∀ (k0 k inv : ℝ) →
    k0 *ℝ inv ≡ 1ℝ →
    (k0 *ℝ k) *ℝ inv *ℝ inv ≡ k *ℝ inv
rightInverseFactor k0 k inv h =
  trans
    (mulFourReorder k0 k inv inv)
    (trans
      (cong (λ z → (k *ℝ inv) *ℝ z) h)
      (mulOneʳ (k *ℝ inv)))

covarianceInverseLedger :
  ∀ (k0 kf kg kfg inv : ℝ) →
    k0 *ℝ inv ≡ 1ℝ →
    kfg *ℝ inv -ℝ (kf *ℝ inv) *ℝ (kg *ℝ inv)
      ≡ ((k0 *ℝ kfg) -ℝ (kf *ℝ kg)) *ℝ inv *ℝ inv
covarianceInverseLedger k0 kf kg kfg inv h =
  let
    numeratorExpanded :
      ((k0 *ℝ kfg) -ℝ (kf *ℝ kg)) *ℝ inv *ℝ inv
        ≡ ((k0 *ℝ kfg) *ℝ inv *ℝ inv)
            -ℝ ((kf *ℝ kg) *ℝ inv *ℝ inv)
    numeratorExpanded =
      trans
        (cong (λ z → z *ℝ inv)
          (subMulDistributes (k0 *ℝ kfg) (kf *ℝ kg) inv))
        (subMulDistributes
          ((k0 *ℝ kfg) *ℝ inv) ((kf *ℝ kg) *ℝ inv) inv)

    kfkgReorder :
      ((kf *ℝ kg) *ℝ inv) *ℝ inv
        ≡ (kf *ℝ inv) *ℝ (kg *ℝ inv)
    kfkgReorder =
      trans (mulFourReorder kf kg inv inv)
            (*-comm (kg *ℝ inv) (kf *ℝ inv))

    cancelled :
      ((k0 *ℝ kfg) *ℝ inv *ℝ inv)
        -ℝ ((kf *ℝ kg) *ℝ inv *ℝ inv)
        ≡ kfg *ℝ inv -ℝ (kf *ℝ inv) *ℝ (kg *ℝ inv)
    cancelled =
      trans
        (cong
          (λ z → z -ℝ ((kf *ℝ kg) *ℝ inv *ℝ inv))
          (rightInverseFactor k0 kfg inv h))
        (cong (λ z → kfg *ℝ inv -ℝ z) kfkgReorder)
  in
  sym (trans numeratorExpanded cancelled)

affineTiltedCovarianceInverseLedger :
  ∀ (k0 kf kg kfg s t inv : ℝ) →
    affineMass k0 kf kg kfg s t *ℝ inv ≡ 1ℝ →
    kfg *ℝ inv
      -ℝ (affineSMassDerivative kf kg kfg s t *ℝ inv)
          *ℝ (affineTMassDerivative kf kg kfg s t *ℝ inv)
      ≡ ((k0 *ℝ kfg) -ℝ (kf *ℝ kg)) *ℝ inv *ℝ inv
affineTiltedCovarianceInverseLedger k0 kf kg kfg s t inv h =
  trans
    (covarianceInverseLedger
      (affineMass k0 kf kg kfg s t)
      (affineSMassDerivative kf kg kfg s t)
      (affineTMassDerivative kf kg kfg s t)
      kfg inv h)
    (cong
      (λ z → z *ℝ inv *ℝ inv)
      (affineMassDeterminant k0 kf kg kfg s t))

realAffineLedgerLevel : ProofLevel
realAffineLedgerLevel = machineChecked

realAffineInverseApplicationLevel : ProofLevel
realAffineInverseApplicationLevel = conditional
