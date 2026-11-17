module DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

------------------------------------------------------------------------
-- The minimal real carrier used by the literal C^3 construction already
-- contains a commutative-ring structure.  This adapter exposes that structure
-- to the standard non-reflective normaliser.  It adds no analytic assumption:
-- inverse and order are not used anywhere in this file.
------------------------------------------------------------------------

realAddZeroRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.add F a (C3.zero F) ≡ a
realAddZeroRight F a =
  trans (C3.addCommutative F a (C3.zero F)) (C3.addZeroLeft F a)

realAddInverseRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.add F a (C3.negate F a) ≡ C3.zero F
realAddInverseRight F a =
  trans
    (C3.addCommutative F a (C3.negate F a))
    (C3.addInverseLeft F a)

realMultiplyOneRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.multiply F a (C3.one F) ≡ a
realMultiplyOneRight F a =
  trans
    (C3.multiplyCommutative F a (C3.one F))
    (C3.multiplyOneLeft F a)

realDistributeRight :
  ∀ {r} (F : C3.RealField r) (a b c : C3.Carrier F) →
  C3.multiply F (C3.add F a b) c
  ≡ C3.add F (C3.multiply F a c) (C3.multiply F b c)
realDistributeRight F a b c =
  trans
    (C3.multiplyCommutative F (C3.add F a b) c)
    (trans
      (C3.distributeLeft F c a b)
      (cong₂ (C3.add F)
        (C3.multiplyCommutative F c a)
        (C3.multiplyCommutative F c b)))

realCommutativeRing :
  ∀ {r} (F : C3.RealField r) → CommutativeRing r r
realCommutativeRing F = record
  { Carrier = C3.Carrier F
  ; _≈_ = _≡_
  ; _+_ = C3.add F
  ; _*_ = C3.multiply F
  ; -_ = C3.negate F
  ; 0# = C3.zero F
  ; 1# = C3.one F
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = cong₂ (C3.add F)
                }
              ; assoc = C3.addAssociative F
              }
            ; identity = C3.addZeroLeft F , realAddZeroRight F
            }
          ; inverse = C3.addInverseLeft F , realAddInverseRight F
          ; ⁻¹-cong = cong (C3.negate F)
          }
        ; comm = C3.addCommutative F
        }
      ; *-cong = cong₂ (C3.multiply F)
      ; *-assoc = C3.multiplyAssociative F
      ; *-identity = C3.multiplyOneLeft F , realMultiplyOneRight F
      ; distrib = realDistributeRight F , C3.distributeLeft F
      }
    ; *-comm = C3.multiplyCommutative F
    }
  }

private
  solverRing :
    ∀ {r} (F : C3.RealField r) →
    RingCore.AlmostCommutativeRing r r
  solverRing F =
    RingCore.fromCommutativeRing (realCommutativeRing F) (λ _ → nothing)

module Solver {r : Level} (F : C3.RealField r) =
  RingSolver (solverRing F)

module Polynomial {r : Level} (F : C3.RealField r) where
  module R = Solver F

  multiplyReal :
    ∀ {n} → R.Expr n → R.Expr n → R.Expr n → R.Expr n → R.Expr n
  multiplyReal ar ai br bi =
    (ar R.⊗ br) R.⊕ (R.⊝ (ai R.⊗ bi))

  multiplyImaginary :
    ∀ {n} → R.Expr n → R.Expr n → R.Expr n → R.Expr n → R.Expr n
  multiplyImaginary ar ai br bi =
    (ar R.⊗ bi) R.⊕ (ai R.⊗ br)

------------------------------------------------------------------------
-- Extensionality and the exact complex-ring identities required below.
------------------------------------------------------------------------

complexExt :
  ∀ {r} {F : C3.RealField r} {a b : C3.Complex F} →
  C3.real a ≡ C3.real b →
  C3.imaginary a ≡ C3.imaginary b →
  a ≡ b
complexExt {a = C3.complex ar ai} {b = C3.complex .ar .ai}
  refl refl = refl

complex3Ext :
  ∀ {r} {F : C3.RealField r} {a b : C3.Complex3 F} →
  C3.x a ≡ C3.x b →
  C3.y a ≡ C3.y b →
  C3.z a ≡ C3.z b →
  a ≡ b
complex3Ext {a = C3.complex3 ax ay az}
  {b = C3.complex3 .ax .ay .az} refl refl refl = refl

complexAddAssociative :
  ∀ {r} {F : C3.RealField r} (a b c : C3.Complex F) →
  C3.complexAdd (C3.complexAdd a b) c
  ≡ C3.complexAdd a (C3.complexAdd b c)
complexAddAssociative {F = F}
  (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci) =
  complexExt
    (P.R.solve 3
      (λ a b c → ((a P.R.⊕ b) P.R.⊕ c) P.R.⊜
                    (a P.R.⊕ (b P.R.⊕ c))) refl ar br cr)
    (P.R.solve 3
      (λ a b c → ((a P.R.⊕ b) P.R.⊕ c) P.R.⊜
                    (a P.R.⊕ (b P.R.⊕ c))) refl ai bi ci)
  where module P = Polynomial F

complexAddCommutative :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexAdd a b ≡ C3.complexAdd b a
complexAddCommutative {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  complexExt
    (P.R.solve 2 (λ a b → (a P.R.⊕ b) P.R.⊜ (b P.R.⊕ a))
      refl ar br)
    (P.R.solve 2 (λ a b → (a P.R.⊕ b) P.R.⊜ (b P.R.⊕ a))
      refl ai bi)
  where module P = Polynomial F

complexAddZeroLeft :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexAdd (C3.complexZero F) a ≡ a
complexAddZeroLeft {F = F} (C3.complex ar ai) =
  complexExt (C3.addZeroLeft F ar) (C3.addZeroLeft F ai)

complexAddZeroRight :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexAdd a (C3.complexZero F) ≡ a
complexAddZeroRight {F = F} (C3.complex ar ai) =
  complexExt (realAddZeroRight F ar) (realAddZeroRight F ai)

complexAddInverseLeft :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexAdd (C3.complexNegate a) a ≡ C3.complexZero F
complexAddInverseLeft {F = F} (C3.complex ar ai) =
  complexExt (C3.addInverseLeft F ar) (C3.addInverseLeft F ai)

complexNegateInvolutive :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexNegate (C3.complexNegate a) ≡ a
complexNegateInvolutive {F = F} (C3.complex ar ai)
  rewrite C3.negateInvolutive F ar | C3.negateInvolutive F ai = refl

complexMultiplyAssociative :
  ∀ {r} {F : C3.RealField r} (a b c : C3.Complex F) →
  C3.complexMultiply (C3.complexMultiply a b) c
  ≡ C3.complexMultiply a (C3.complexMultiply b c)
complexMultiplyAssociative {F = F}
  (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci) =
  complexExt
    (P.R.solve 6
      (λ ar ai br bi cr ci →
        P.multiplyReal
          (P.multiplyReal ar ai br bi)
          (P.multiplyImaginary ar ai br bi)
          cr ci
        P.R.⊜
        P.multiplyReal ar ai
          (P.multiplyReal br bi cr ci)
          (P.multiplyImaginary br bi cr ci))
      refl ar ai br bi cr ci)
    (P.R.solve 6
      (λ ar ai br bi cr ci →
        P.multiplyImaginary
          (P.multiplyReal ar ai br bi)
          (P.multiplyImaginary ar ai br bi)
          cr ci
        P.R.⊜
        P.multiplyImaginary ar ai
          (P.multiplyReal br bi cr ci)
          (P.multiplyImaginary br bi cr ci))
      refl ar ai br bi cr ci)
  where module P = Polynomial F

complexMultiplyCommutative :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexMultiply a b ≡ C3.complexMultiply b a
complexMultiplyCommutative {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  complexExt
    (P.R.solve 4
      (λ ar ai br bi →
        P.multiplyReal ar ai br bi P.R.⊜ P.multiplyReal br bi ar ai)
      refl ar ai br bi)
    (P.R.solve 4
      (λ ar ai br bi →
        P.multiplyImaginary ar ai br bi P.R.⊜
        P.multiplyImaginary br bi ar ai)
      refl ar ai br bi)
  where module P = Polynomial F

complexMultiplyZeroLeft :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexMultiply (C3.complexZero F) a ≡ C3.complexZero F
complexMultiplyZeroLeft {F = F} (C3.complex ar ai) =
  complexExt
    (P.R.solve 2
      (λ ar ai →
        P.multiplyReal (P.R.Κ (C3.zero F)) (P.R.Κ (C3.zero F)) ar ai
        P.R.⊜ P.R.Κ (C3.zero F)) refl ar ai)
    (P.R.solve 2
      (λ ar ai →
        P.multiplyImaginary (P.R.Κ (C3.zero F)) (P.R.Κ (C3.zero F)) ar ai
        P.R.⊜ P.R.Κ (C3.zero F)) refl ar ai)
  where module P = Polynomial F

complexMultiplyZeroRight :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexMultiply a (C3.complexZero F) ≡ C3.complexZero F
complexMultiplyZeroRight {F = F} a =
  trans
    (complexMultiplyCommutative a (C3.complexZero F))
    (complexMultiplyZeroLeft a)

complexOneMultiply :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexMultiply (C3.complexOne F) z ≡ z
complexOneMultiply {F = F} (C3.complex zr zi) =
  complexExt
    (P.R.solve 2
      (λ zr zi →
        P.multiplyReal (P.R.Κ (C3.one F)) (P.R.Κ (C3.zero F)) zr zi
        P.R.⊜ zr) refl zr zi)
    (P.R.solve 2
      (λ zr zi →
        P.multiplyImaginary (P.R.Κ (C3.one F)) (P.R.Κ (C3.zero F)) zr zi
        P.R.⊜ zi) refl zr zi)
  where module P = Polynomial F

complexNegateMultiplyLeft :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexMultiply (C3.complexNegate a) b
  ≡ C3.complexNegate (C3.complexMultiply a b)
complexNegateMultiplyLeft {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  complexExt
    (P.R.solve 4
      (λ ar ai br bi →
        P.multiplyReal (P.R.⊝ ar) (P.R.⊝ ai) br bi
        P.R.⊜ P.R.⊝ (P.multiplyReal ar ai br bi))
      refl ar ai br bi)
    (P.R.solve 4
      (λ ar ai br bi →
        P.multiplyImaginary (P.R.⊝ ar) (P.R.⊝ ai) br bi
        P.R.⊜ P.R.⊝ (P.multiplyImaginary ar ai br bi))
      refl ar ai br bi)
  where module P = Polynomial F

complexNegateMultiplyRight :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexMultiply a (C3.complexNegate b)
  ≡ C3.complexNegate (C3.complexMultiply a b)
complexNegateMultiplyRight a b =
  trans
    (complexMultiplyCommutative a (C3.complexNegate b))
    (trans
      (complexNegateMultiplyLeft b a)
      (cong C3.complexNegate (complexMultiplyCommutative b a)))

complexConjugateMultiply :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexConjugate (C3.complexMultiply a b)
  ≡ C3.complexMultiply (C3.complexConjugate a) (C3.complexConjugate b)
complexConjugateMultiply {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  complexExt
    (P.R.solve 4
      (λ ar ai br bi →
        P.multiplyReal ar ai br bi P.R.⊜
        P.multiplyReal ar (P.R.⊝ ai) br (P.R.⊝ bi))
      refl ar ai br bi)
    (P.R.solve 4
      (λ ar ai br bi →
        P.R.⊝ (P.multiplyImaginary ar ai br bi) P.R.⊜
        P.multiplyImaginary ar (P.R.⊝ ai) br (P.R.⊝ bi))
      refl ar ai br bi)
  where module P = Polynomial F

complexConjugateNegate :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexConjugate (C3.complexNegate a)
  ≡ C3.complexNegate (C3.complexConjugate a)
complexConjugateNegate {F = F} (C3.complex ar ai) =
  complexExt refl
    (P.R.solve 1
      (λ ai → P.R.⊝ (P.R.⊝ ai) P.R.⊜ P.R.⊝ (P.R.⊝ ai))
      refl ai)
  where module P = Polynomial F

complexConjugateZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complexConjugate (C3.complexZero F) ≡ C3.complexZero F
complexConjugateZero {F = F}
  rewrite C3.negateZero F = refl

complexRealPartAdd :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexRealPart (C3.complexAdd a b)
  ≡ C3.complexAdd (C3.complexRealPart a) (C3.complexRealPart b)
complexRealPartAdd {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  complexExt refl (sym (C3.addZeroLeft F (C3.zero F)))

complexRealPartConjugate :
  ∀ {r} {F : C3.RealField r} (a : C3.Complex F) →
  C3.complexRealPart (C3.complexConjugate a)
  ≡ C3.complexRealPart a
complexRealPartConjugate (C3.complex ar ai) = refl

complexAddReorderSix :
  ∀ {r} {F : C3.RealField r} (a b c d e f : C3.Complex F) →
  C3.complexAdd
    (C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d))
    (C3.complexAdd e f)
  ≡
  C3.complexAdd
    (C3.complexAdd (C3.complexAdd a f) (C3.complexAdd b d))
    (C3.complexAdd c e)
complexAddReorderSix {F = F}
  (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci)
  (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi) =
  complexExt
    (P.R.solve 6
      (λ a b c d e f →
        (((a P.R.⊕ b) P.R.⊕ (c P.R.⊕ d)) P.R.⊕ (e P.R.⊕ f))
        P.R.⊜
        (((a P.R.⊕ f) P.R.⊕ (b P.R.⊕ d)) P.R.⊕ (c P.R.⊕ e)))
      refl ar br cr dr er fr)
    (P.R.solve 6
      (λ a b c d e f →
        (((a P.R.⊕ b) P.R.⊕ (c P.R.⊕ d)) P.R.⊕ (e P.R.⊕ f))
        P.R.⊜
        (((a P.R.⊕ f) P.R.⊕ (b P.R.⊕ d)) P.R.⊕ (c P.R.⊕ e)))
      refl ai bi ci di ei fi)
  where module P = Polynomial F

------------------------------------------------------------------------
-- C^3 linear, bilinear and Hermitian identities.
------------------------------------------------------------------------

complex3AddZeroRight :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Add v (C3.complex3Zero F) ≡ v
complex3AddZeroRight (C3.complex3 vx vy vz) =
  complex3Ext
    (complexAddZeroRight vx)
    (complexAddZeroRight vy)
    (complexAddZeroRight vz)

complex3ScaleZero :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexZero F) v ≡ C3.complex3Zero F
complex3ScaleZero (C3.complex3 vx vy vz) =
  complex3Ext
    (complexMultiplyZeroLeft vx)
    (complexMultiplyZeroLeft vy)
    (complexMultiplyZeroLeft vz)

complex3NegateScale :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Complex F) (v : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Scale a v)
  ≡ C3.complex3Scale (C3.complexNegate a) v
complex3NegateScale a (C3.complex3 vx vy vz) =
  complex3Ext
    (sym (complexNegateMultiplyLeft a vx))
    (sym (complexNegateMultiplyLeft a vy))
    (sym (complexNegateMultiplyLeft a vz))

complex3ScaleNegativeOne :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexNegate (C3.complexOne F)) v
  ≡ C3.complex3Negate v
complex3ScaleNegativeOne (C3.complex3 vx vy vz) =
  complex3Ext
    (trans (complexNegateMultiplyLeft (C3.complexOne _) vx)
      (cong C3.complexNegate (complexOneMultiply vx)))
    (trans (complexNegateMultiplyLeft (C3.complexOne _) vy)
      (cong C3.complexNegate (complexOneMultiply vy)))
    (trans (complexNegateMultiplyLeft (C3.complexOne _) vz)
      (cong C3.complexNegate (complexOneMultiply vz)))

bilinearDotCommutative :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.bilinearDot3 u v ≡ C3.bilinearDot3 v u
bilinearDotCommutative
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  trans
    (cong₂ C3.complexAdd
      (cong₂ C3.complexAdd
        (complexMultiplyCommutative ux vx)
        (complexMultiplyCommutative uy vy))
      (complexMultiplyCommutative uz vz))
    (cong
      (λ pair → C3.complexAdd pair (C3.complexMultiply vz uz))
      (complexAddCommutative
        (C3.complexMultiply vx ux)
        (C3.complexMultiply vy uy)))

bilinearDotConjugate :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.bilinearDot3 (C3.complex3Conjugate u) (C3.complex3Conjugate v)
  ≡ C3.complexConjugate (C3.bilinearDot3 u v)
bilinearDotConjugate {F = F}
  (C3.complex3 (C3.complex uxr uxi) (C3.complex uyr uyi)
    (C3.complex uzr uzi))
  (C3.complex3 (C3.complex vxr vxi) (C3.complex vyr vyi)
    (C3.complex vzr vzi)) =
  complexExt
    (P.R.solve 12
      (λ uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi →
        ((P.multiplyReal uxr (P.R.⊝ uxi) vxr (P.R.⊝ vxi)
          P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr (P.R.⊝ vyi))
          P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr (P.R.⊝ vzi))
        P.R.⊜
        ((P.multiplyReal uxr uxi vxr vxi
          P.R.⊕ P.multiplyReal uyr uyi vyr vyi)
          P.R.⊕ P.multiplyReal uzr uzi vzr vzi))
      refl uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi)
    (P.R.solve 12
      (λ uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi →
        ((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr (P.R.⊝ vxi)
          P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr (P.R.⊝ vyi))
          P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr (P.R.⊝ vzi))
        P.R.⊜
        P.R.⊝
          ((P.multiplyImaginary uxr uxi vxr vxi
            P.R.⊕ P.multiplyImaginary uyr uyi vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr uzi vzr vzi))
      refl uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi)
  where module P = Polynomial F

bilinearDotNegateRight :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Negate v)
  ≡ C3.complexNegate (C3.bilinearDot3 u v)
bilinearDotNegateRight {F = F}
  (C3.complex3 (C3.complex uxr uxi) (C3.complex uyr uyi)
    (C3.complex uzr uzi))
  (C3.complex3 (C3.complex vxr vxi) (C3.complex vyr vyi)
    (C3.complex vzr vzi)) =
  complexExt
    (P.R.solve 12
      (λ uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi →
        ((P.multiplyReal uxr uxi (P.R.⊝ vxr) (P.R.⊝ vxi)
          P.R.⊕ P.multiplyReal uyr uyi (P.R.⊝ vyr) (P.R.⊝ vyi))
          P.R.⊕ P.multiplyReal uzr uzi (P.R.⊝ vzr) (P.R.⊝ vzi))
        P.R.⊜
        P.R.⊝
          ((P.multiplyReal uxr uxi vxr vxi
            P.R.⊕ P.multiplyReal uyr uyi vyr vyi)
            P.R.⊕ P.multiplyReal uzr uzi vzr vzi))
      refl uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi)
    (P.R.solve 12
      (λ uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi →
        ((P.multiplyImaginary uxr uxi (P.R.⊝ vxr) (P.R.⊝ vxi)
          P.R.⊕ P.multiplyImaginary uyr uyi (P.R.⊝ vyr) (P.R.⊝ vyi))
          P.R.⊕ P.multiplyImaginary uzr uzi (P.R.⊝ vzr) (P.R.⊝ vzi))
        P.R.⊜
        P.R.⊝
          ((P.multiplyImaginary uxr uxi vxr vxi
            P.R.⊕ P.multiplyImaginary uyr uyi vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr uzi vzr vzi))
      refl uxr uxi uyr uyi uzr uzi vxr vxi vyr vyi vzr vzi)
  where module P = Polynomial F

hermitianAddRight :
  ∀ {r} {F : C3.RealField r} (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Add v w)
  ≡ C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.hermitianPairing3 u w)
hermitianAddRight {F = F}
  (C3.complex3 (C3.complex uxr uxi) (C3.complex uyr uyi)
    (C3.complex uzr uzi))
  (C3.complex3 (C3.complex vxr vxi) (C3.complex vyr vyi)
    (C3.complex vzr vzi))
  (C3.complex3 (C3.complex wxr wxi) (C3.complex wyr wyi)
    (C3.complex wzr wzi)) =
  complexExt
    (P.R.solve 18
      (λ uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi wxr wxi wyr wyi wzr wzi →
        ((P.multiplyReal uxr (P.R.⊝ uxi) (vxr P.R.⊕ wxr) (vxi P.R.⊕ wxi)
          P.R.⊕
          P.multiplyReal uyr (P.R.⊝ uyi) (vyr P.R.⊕ wyr) (vyi P.R.⊕ wyi))
          P.R.⊕
          P.multiplyReal uzr (P.R.⊝ uzi) (vzr P.R.⊕ wzr) (vzi P.R.⊕ wzi))
        P.R.⊜
        (((P.multiplyReal uxr (P.R.⊝ uxi) vxr vxi
          P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr vyi)
          P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr vzi)
          P.R.⊕
        ((P.multiplyReal uxr (P.R.⊝ uxi) wxr wxi
          P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) wyr wyi)
          P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) wzr wzi)))
      refl uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi wxr wxi wyr wyi wzr wzi)
    (P.R.solve 18
      (λ uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi wxr wxi wyr wyi wzr wzi →
        ((P.multiplyImaginary uxr (P.R.⊝ uxi) (vxr P.R.⊕ wxr) (vxi P.R.⊕ wxi)
          P.R.⊕
          P.multiplyImaginary uyr (P.R.⊝ uyi) (vyr P.R.⊕ wyr) (vyi P.R.⊕ wyi))
          P.R.⊕
          P.multiplyImaginary uzr (P.R.⊝ uzi) (vzr P.R.⊕ wzr) (vzi P.R.⊕ wzi))
        P.R.⊜
        (((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr vxi
          P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr vyi)
          P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr vzi)
          P.R.⊕
        ((P.multiplyImaginary uxr (P.R.⊝ uxi) wxr wxi
          P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) wyr wyi)
          P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) wzr wzi)))
      refl uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi wxr wxi wyr wyi wzr wzi)
  where module P = Polynomial F

bilinearDotAddRight :
  ∀ {r} {F : C3.RealField r} (u v w : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Add v w)
  ≡ C3.complexAdd
      (C3.bilinearDot3 u v)
      (C3.bilinearDot3 u w)
bilinearDotAddRight u v w =
  trans
    (cong
      (λ first → C3.bilinearDot3 first (C3.complex3Add v w))
      (sym (C3.complex3ConjugateInvolutive u)))
    (trans
      (hermitianAddRight (C3.complex3Conjugate u) v w)
      (cong₂ C3.complexAdd
        (cong
          (λ first → C3.bilinearDot3 first v)
          (C3.complex3ConjugateInvolutive u))
        (cong
          (λ first → C3.bilinearDot3 first w)
          (C3.complex3ConjugateInvolutive u))))

hermitianScaleRight :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) (a : C3.Complex F) →
  C3.hermitianPairing3 u (C3.complex3Scale a v)
  ≡ C3.complexMultiply a (C3.hermitianPairing3 u v)
hermitianScaleRight {F = F}
  (C3.complex3 (C3.complex uxr uxi) (C3.complex uyr uyi)
    (C3.complex uzr uzi))
  (C3.complex3 (C3.complex vxr vxi) (C3.complex vyr vyi)
    (C3.complex vzr vzi))
  (C3.complex ar ai) =
  complexExt
    (P.R.solve 14
      (λ uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi ar ai →
        ((P.multiplyReal uxr (P.R.⊝ uxi) (P.multiplyReal ar ai vxr vxi)
            (P.multiplyImaginary ar ai vxr vxi)
          P.R.⊕
          P.multiplyReal uyr (P.R.⊝ uyi) (P.multiplyReal ar ai vyr vyi)
            (P.multiplyImaginary ar ai vyr vyi))
          P.R.⊕
          P.multiplyReal uzr (P.R.⊝ uzi) (P.multiplyReal ar ai vzr vzi)
            (P.multiplyImaginary ar ai vzr vzi))
        P.R.⊜
        P.multiplyReal ar ai
          ((P.multiplyReal uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr vzi)
          ((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr vzi))
      refl uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi ar ai)
    (P.R.solve 14
      (λ uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi ar ai →
        ((P.multiplyImaginary uxr (P.R.⊝ uxi) (P.multiplyReal ar ai vxr vxi)
            (P.multiplyImaginary ar ai vxr vxi)
          P.R.⊕
          P.multiplyImaginary uyr (P.R.⊝ uyi) (P.multiplyReal ar ai vyr vyi)
            (P.multiplyImaginary ar ai vyr vyi))
          P.R.⊕
          P.multiplyImaginary uzr (P.R.⊝ uzi) (P.multiplyReal ar ai vzr vzi)
            (P.multiplyImaginary ar ai vzr vzi))
        P.R.⊜
        P.multiplyImaginary ar ai
          ((P.multiplyReal uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr vzi)
          ((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr vzi))
      refl uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi ar ai)
  where module P = Polynomial F

hermitianNegateRight :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Negate v)
  ≡ C3.complexNegate (C3.hermitianPairing3 u v)
hermitianNegateRight u v =
  trans
    (cong (C3.hermitianPairing3 u)
      (sym (complex3ScaleNegativeOne v)))
    (trans
      (hermitianScaleRight u v (C3.complexNegate (C3.complexOne _)))
      (trans
        (complexNegateMultiplyLeft
          (C3.complexOne _) (C3.hermitianPairing3 u v))
        (cong C3.complexNegate
          (complexOneMultiply (C3.hermitianPairing3 u v)))))

hermitianAddLeft :
  ∀ {r} {F : C3.RealField r} (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Add u v) w
  ≡ C3.complexAdd
      (C3.hermitianPairing3 u w)
      (C3.hermitianPairing3 v w)
hermitianAddLeft {F = F} u v w =
  trans
    conjugateAddStep
    dotAddStep
  where
  conjugateAddStep :
    C3.hermitianPairing3 (C3.complex3Add u v) w
    ≡ C3.bilinearDot3
        (C3.complex3Add
          (C3.complex3Conjugate u)
          (C3.complex3Conjugate v))
        w
  conjugateAddStep =
    cong (λ x → C3.bilinearDot3 x w) (conjugateVectorAdd u v)

  dotAddStep :
    C3.bilinearDot3
      (C3.complex3Add
        (C3.complex3Conjugate u)
        (C3.complex3Conjugate v))
      w
    ≡ C3.complexAdd
        (C3.hermitianPairing3 u w)
        (C3.hermitianPairing3 v w)
  dotAddStep =
    trans
      (bilinearDotCommutative
        (C3.complex3Add
          (C3.complex3Conjugate u)
          (C3.complex3Conjugate v))
        w)
      (trans
        (bilinearDotAddRight
          w
          (C3.complex3Conjugate u)
          (C3.complex3Conjugate v))
        (cong₂ C3.complexAdd
          (bilinearDotCommutative w (C3.complex3Conjugate u))
          (bilinearDotCommutative w (C3.complex3Conjugate v))))

  conjugateVectorAdd :
    ∀ {r} {F : C3.RealField r} (a b : C3.Complex3 F) →
    C3.complex3Conjugate (C3.complex3Add a b)
    ≡ C3.complex3Add (C3.complex3Conjugate a) (C3.complex3Conjugate b)
  conjugateVectorAdd
    (C3.complex3 (C3.complex axr axi) (C3.complex ayr ayi)
      (C3.complex azr azi))
    (C3.complex3 (C3.complex bxr bxi) (C3.complex byr byi)
      (C3.complex bzr bzi)) =
    complex3Ext
      (complexExt refl
        (P.R.solve 2
          (λ a b → P.R.⊝ (a P.R.⊕ b) P.R.⊜
                    ((P.R.⊝ a) P.R.⊕ (P.R.⊝ b))) refl axi bxi))
      (complexExt refl
        (P.R.solve 2
          (λ a b → P.R.⊝ (a P.R.⊕ b) P.R.⊜
                    ((P.R.⊝ a) P.R.⊕ (P.R.⊝ b))) refl ayi byi))
      (complexExt refl
        (P.R.solve 2
          (λ a b → P.R.⊝ (a P.R.⊕ b) P.R.⊜
                    ((P.R.⊝ a) P.R.⊕ (P.R.⊝ b))) refl azi bzi))
    where module P = Polynomial F

hermitianScaleLeft :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Complex F) (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Scale a u) v
  ≡ C3.complexMultiply
      (C3.complexConjugate a)
      (C3.hermitianPairing3 u v)
hermitianScaleLeft {F = F}
  (C3.complex ar ai)
  (C3.complex3 (C3.complex uxr uxi) (C3.complex uyr uyi)
    (C3.complex uzr uzi))
  (C3.complex3 (C3.complex vxr vxi) (C3.complex vyr vyi)
    (C3.complex vzr vzi)) =
  complexExt
    (P.R.solve 14
      (λ ar ai uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi →
        ((P.multiplyReal
            (P.multiplyReal ar (P.R.⊝ ai) uxr (P.R.⊝ uxi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uxr (P.R.⊝ uxi)))
            vxr vxi
          P.R.⊕
          P.multiplyReal
            (P.multiplyReal ar (P.R.⊝ ai) uyr (P.R.⊝ uyi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uyr (P.R.⊝ uyi)))
            vyr vyi)
          P.R.⊕
          P.multiplyReal
            (P.multiplyReal ar (P.R.⊝ ai) uzr (P.R.⊝ uzi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uzr (P.R.⊝ uzi)))
            vzr vzi)
        P.R.⊜
        P.multiplyReal ar (P.R.⊝ ai)
          ((P.multiplyReal uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr vzi)
          ((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr vzi))
      refl ar ai uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi)
    (P.R.solve 14
      (λ ar ai uxr uxi uyr uyi uzr uzi
         vxr vxi vyr vyi vzr vzi →
        ((P.multiplyImaginary
            (P.multiplyReal ar (P.R.⊝ ai) uxr (P.R.⊝ uxi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uxr (P.R.⊝ uxi)))
            vxr vxi
          P.R.⊕
          P.multiplyImaginary
            (P.multiplyReal ar (P.R.⊝ ai) uyr (P.R.⊝ uyi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uyr (P.R.⊝ uyi)))
            vyr vyi)
          P.R.⊕
          P.multiplyImaginary
            (P.multiplyReal ar (P.R.⊝ ai) uzr (P.R.⊝ uzi))
            (P.R.⊝
              (P.multiplyImaginary ar (P.R.⊝ ai) uzr (P.R.⊝ uzi)))
            vzr vzi)
        P.R.⊜
        P.multiplyImaginary ar (P.R.⊝ ai)
          ((P.multiplyReal uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyReal uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyReal uzr (P.R.⊝ uzi) vzr vzi)
          ((P.multiplyImaginary uxr (P.R.⊝ uxi) vxr vxi
            P.R.⊕ P.multiplyImaginary uyr (P.R.⊝ uyi) vyr vyi)
            P.R.⊕ P.multiplyImaginary uzr (P.R.⊝ uzi) vzr vzi))
      refl ar ai uxr uxi uyr uyi uzr uzi
        vxr vxi vyr vyi vzr vzi)
  where module P = Polynomial F

hermitianNegateLeft :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Negate u) v
  ≡ C3.complexNegate (C3.hermitianPairing3 u v)
hermitianNegateLeft u v =
  trans
    (cong (λ x → C3.hermitianPairing3 x v)
      (sym (complex3ScaleNegativeOne u)))
    (trans
      (hermitianScaleLeft (C3.complexNegate (C3.complexOne _)) u v)
      scalarIdentity)
  where
  scalarIdentity :
    C3.complexMultiply
      (C3.complexConjugate (C3.complexNegate (C3.complexOne _)))
      (C3.hermitianPairing3 u v)
    ≡ C3.complexNegate (C3.hermitianPairing3 u v)
  scalarIdentity =
    trans
      (cong
        (λ scalar → C3.complexMultiply scalar (C3.hermitianPairing3 u v))
        (trans
          (complexConjugateNegate (C3.complexOne _))
          (cong C3.complexNegate
            (C3.realEmbedConjugate _ (C3.one _)))))
      (trans
        (complexNegateMultiplyLeft
          (C3.complexOne _) (C3.hermitianPairing3 u v))
        (cong C3.complexNegate
          (complexOneMultiply (C3.hermitianPairing3 u v))))

hermitianConjugatePair :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.hermitianPairing3
    (C3.complex3Conjugate u)
    (C3.complex3Conjugate v)
  ≡ C3.hermitianPairing3 v u
hermitianConjugatePair u v =
  trans
    (cong
      (λ first →
        C3.bilinearDot3 first (C3.complex3Conjugate v))
      (C3.complex3ConjugateInvolutive u))
    (bilinearDotCommutative u (C3.complex3Conjugate v))

hermitianConjugateSymmetry :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.hermitianPairing3 v u
  ≡ C3.complexConjugate (C3.hermitianPairing3 u v)
hermitianConjugateSymmetry u v =
  trans
    (bilinearDotCommutative (C3.complex3Conjugate v) u)
    (trans
      (cong
        (λ first → C3.bilinearDot3 first (C3.complex3Conjugate v))
        (sym (C3.complex3ConjugateInvolutive u)))
      (bilinearDotConjugate (C3.complex3Conjugate u) v))

------------------------------------------------------------------------
-- Literal Leray identities.  The self-adjoint theorem is proved for the
-- exact rank-one formula, not imported as a projection axiom.
------------------------------------------------------------------------

modePairRight :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (u : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.modeVector E k)
  ≡ C3.complexConjugate
      (C3.bilinearDot3 (C3.modeVector E k) u)
modePairRight E k u =
  trans
    (bilinearDotCommutative
      (C3.complex3Conjugate u)
      (C3.modeVector E k))
    (trans
      (cong
        (λ first →
          C3.bilinearDot3 first (C3.complex3Conjugate u))
        (sym (C3.modeVectorConjugate E k)))
      (bilinearDotConjugate (C3.modeVector E k) u))

modePairLeft :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (u : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.modeVector E k) u
  ≡ C3.bilinearDot3 (C3.modeVector E k) u
modePairLeft E k u =
  cong
    (λ first → C3.bilinearDot3 first u)
    (C3.modeVectorConjugate E k)

modeVectorAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode) →
  C3.modeVector E (Z3.addMode p q)
  ≡ C3.complex3Add (C3.modeVector E p) (C3.modeVector E q)
modeVectorAdd {F = F} E (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.embedAdd E px qx
        | C3.embedAdd E py qy
        | C3.embedAdd E pz qz =
  complex3Ext
    (realEmbedAdd (C3.embedInteger E px) (C3.embedInteger E qx))
    (realEmbedAdd (C3.embedInteger E py) (C3.embedInteger E qy))
    (realEmbedAdd (C3.embedInteger E pz) (C3.embedInteger E qz))
  where
  realEmbedAdd :
    ∀ a b →
    C3.realEmbed F (C3.add F a b)
    ≡ C3.complexAdd (C3.realEmbed F a) (C3.realEmbed F b)
  realEmbedAdd a b =
    complexExt refl (sym (C3.addZeroLeft F (C3.zero F)))

rankOneCorrectionSymmetry :
  ∀ {r} {F : C3.RealField r}
    (c : C3.Carrier F)
    (dx dy : C3.Complex F) →
  C3.complexNegate
    (C3.complexMultiply
      (C3.complexMultiply (C3.realEmbed F c) dy)
      (C3.complexConjugate dx))
  ≡
  C3.complexNegate
    (C3.complexMultiply
      (C3.complexConjugate
        (C3.complexMultiply (C3.realEmbed F c) dx))
      dy)
rankOneCorrectionSymmetry {F = F} c
  (C3.complex dxr dxi) (C3.complex dyr dyi) =
  complexExt
    (P.R.solve 5
      (λ c dxr dxi dyr dyi →
        P.R.⊝
          (P.multiplyReal
            (P.multiplyReal c (P.R.Κ (C3.zero F)) dyr dyi)
            (P.multiplyImaginary c (P.R.Κ (C3.zero F)) dyr dyi)
            dxr (P.R.⊝ dxi))
        P.R.⊜
        P.R.⊝
          (P.multiplyReal
            (P.multiplyReal c (P.R.Κ (C3.zero F)) dxr dxi)
            (P.R.⊝
              (P.multiplyImaginary c (P.R.Κ (C3.zero F)) dxr dxi))
            dyr dyi))
      refl c dxr dxi dyr dyi)
    (P.R.solve 5
      (λ c dxr dxi dyr dyi →
        P.R.⊝
          (P.multiplyImaginary
            (P.multiplyReal c (P.R.Κ (C3.zero F)) dyr dyi)
            (P.multiplyImaginary c (P.R.Κ (C3.zero F)) dyr dyi)
            dxr (P.R.⊝ dxi))
        P.R.⊜
        P.R.⊝
          (P.multiplyImaginary
            (P.multiplyReal c (P.R.Κ (C3.zero F)) dxr dxi)
            (P.R.⊝
              (P.multiplyImaginary c (P.R.Κ (C3.zero F)) dxr dxi))
            dyr dyi))
      refl c dxr dxi dyr dyi)
  where module P = Polynomial F

lerayProjectSelfAdjoint :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.lerayProject3 E I k v)
  ≡ C3.hermitianPairing3 (C3.lerayProject3 E I k u) v
lerayProjectSelfAdjoint {F = F} E I k u v =
  begin
    C3.hermitianPairing3 u (C3.lerayProject3 E I k v)
  ≡⟨ hermitianAddRight u v
        (C3.complex3Negate
          (C3.complex3Scale alphaV (C3.modeVector E k))) ⟩
    C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.hermitianPairing3 u
        (C3.complex3Negate
          (C3.complex3Scale alphaV (C3.modeVector E k))))
  ≡⟨ cong
        (C3.complexAdd (C3.hermitianPairing3 u v))
        (trans
          (hermitianNegateRight u
            (C3.complex3Scale alphaV (C3.modeVector E k)))
          (cong C3.complexNegate
            (trans
              (hermitianScaleRight u (C3.modeVector E k) alphaV)
              (cong (C3.complexMultiply alphaV)
                (modePairRight E k u))))) ⟩
    C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.complexNegate
        (C3.complexMultiply alphaV (C3.complexConjugate dotU)))
  ≡⟨ cong
        (C3.complexAdd (C3.hermitianPairing3 u v))
        (rankOneCorrectionSymmetry
          (C3.inverseNormSquared I k) dotU dotV) ⟩
    C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.complexNegate
        (C3.complexMultiply (C3.complexConjugate alphaU) dotV))
  ≡⟨ sym
        (cong
          (C3.complexAdd (C3.hermitianPairing3 u v))
          (trans
            (hermitianNegateLeft
              (C3.complex3Scale alphaU (C3.modeVector E k)) v)
            (cong C3.complexNegate
              (trans
                (hermitianScaleLeft alphaU (C3.modeVector E k) v)
                (cong
                  (C3.complexMultiply (C3.complexConjugate alphaU))
                  (modePairLeft E k v)))))) ⟩
    C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.hermitianPairing3
        (C3.complex3Negate
          (C3.complex3Scale alphaU (C3.modeVector E k)))
        v)
  ≡⟨ sym
        (hermitianAddLeft u
          (C3.complex3Negate
            (C3.complex3Scale alphaU (C3.modeVector E k)))
          v) ⟩
    C3.hermitianPairing3 (C3.lerayProject3 E I k u) v
  ∎
  where
  open ≡-Reasoning
  dotU = C3.bilinearDot3 (C3.modeVector E k) u
  dotV = C3.bilinearDot3 (C3.modeVector E k) v
  alphaU =
    C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      dotU
  alphaV =
    C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      dotV

lerayProjectFixesTransverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.modeVector E k) ≡ C3.complexZero F →
  C3.lerayProject3 E I k u ≡ u
lerayProjectFixesTransverse {F = F} E I k u transverse =
  begin
    C3.lerayProject3 E I k u
  ≡⟨ cong
        (λ dotValue →
          C3.complex3Subtract u
            (C3.complex3Scale
              (C3.complexMultiply
                (C3.realEmbed F (C3.inverseNormSquared I k))
                dotValue)
              (C3.modeVector E k)))
        (trans (bilinearDotCommutative (C3.modeVector E k) u) transverse) ⟩
    C3.complex3Subtract u
      (C3.complex3Scale
        (C3.complexMultiply
          (C3.realEmbed F (C3.inverseNormSquared I k))
          (C3.complexZero F))
        (C3.modeVector E k))
  ≡⟨ cong
        (λ scalar →
          C3.complex3Subtract u
            (C3.complex3Scale scalar (C3.modeVector E k)))
        (complexMultiplyZeroRight
          (C3.realEmbed F (C3.inverseNormSquared I k))) ⟩
    C3.complex3Subtract u
      (C3.complex3Scale (C3.complexZero F) (C3.modeVector E k))
  ≡⟨ cong (C3.complex3Subtract u)
        (complex3ScaleZero (C3.modeVector E k)) ⟩
    C3.complex3Subtract u (C3.complex3Zero F)
  ≡⟨ cong (C3.complex3Add u)
        (complex3ZeroNegated F) ⟩
    C3.complex3Add u (C3.complex3Zero F)
  ≡⟨ complex3AddZeroRight u ⟩
    u
  ∎
  where
  open ≡-Reasoning

  complex3ZeroNegated :
    ∀ {r} (F : C3.RealField r) →
    C3.complex3Negate (C3.complex3Zero F) ≡ C3.complex3Zero F
  complex3ZeroNegated F
    rewrite C3.negateZero F = refl

removeLerayFromTransverseTest :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (test value : C3.Complex3 F) →
  C3.bilinearDot3 test (C3.modeVector E k) ≡ C3.complexZero F →
  C3.hermitianPairing3 test (C3.lerayProject3 E I k value)
  ≡ C3.hermitianPairing3 test value
removeLerayFromTransverseTest E I k test value transverse =
  trans
    (lerayProjectSelfAdjoint E I k test value)
    (cong
      (λ projected → C3.hermitianPairing3 projected value)
      (lerayProjectFixesTransverse E I k test transverse))
