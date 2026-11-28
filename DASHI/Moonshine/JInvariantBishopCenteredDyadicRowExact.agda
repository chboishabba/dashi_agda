module DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Concrete Paper9 specialization of the existing binary address carrier.
-- Low bits choose +1 shifts; the FINAL high bit chooses -1.
-- The PNP finite codec retains every address. The Karp polarity/residual
-- distinction is respected: orientation is not a substitute for the index.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Integer.Base as Z using (+_; -[1+_])
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _⋆)
import RealProperties as P
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as B
import DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact as Addr
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopComplexOriginQuadraticRemainderExact as O
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; scaleC)
open Comp using (complexTrans; complexSym)

side : Nat → D.Side
side zero = D.negative
side (suc n) = D.positive

walk : ∀ {n} → B.BinaryWord n → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
walk B.end p = p
walk (B.bit0 w) p = walk w (D.left p)
walk {suc n} (B.bit1 w) p = walk w (D.right (side n) p)

h : Nat → ℝ
h zero = R.1ℝ
h (suc n) = h n * D.half

offset0 : ∀ {n} (w : B.BinaryWord (suc n)) →
  Addr.offset (B.bit0 w) ≡ (Addr.offset w Z.+ Addr.offset w) Z.+ (+ 0)
offset0 (B.bit0 w) = refl
offset0 (B.bit1 w) = refl

offset1 : ∀ {n} (w : B.BinaryWord (suc n)) →
  Addr.offset (B.bit1 w) ≡ (Addr.offset w Z.+ Addr.offset w) Z.+ (+ 1)
offset1 (B.bit0 w) = refl
offset1 (B.bit1 w) = refl

j : ∀ {n} → B.BinaryWord n → ℝ
j w = K.embedInteger (Addr.offset w)

embedEq : ∀ {a b : Z.ℤ} → a ≡ b → K.embedInteger a ≃ K.embedInteger b
embedEq refl = P.≃-refl

j0Read : ∀ {n} (w : B.BinaryWord (suc n)) →
  j (B.bit0 w) ≃ (j w + j w)
j0Read w = P.≃-trans (embedEq (offset0 w))
  (P.≃-trans (G.intAdd (Addr.offset w Z.+ Addr.offset w) (+ 0))
    (P.≃-trans (P.+-cong (G.intAdd (Addr.offset w) (Addr.offset w)) P.≃-refl)
      (P.+-identityʳ (j w + j w))))

j1Read : ∀ {n} (w : B.BinaryWord (suc n)) →
  j (B.bit1 w) ≃ ((j w + j w) + R.1ℝ)
j1Read w = P.≃-trans (embedEq (offset1 w))
  (P.≃-trans (G.intAdd (Addr.offset w Z.+ Addr.offset w) (+ 1))
    (P.+-cong (G.intAdd (Addr.offset w) (Addr.offset w)) P.≃-refl))

realWalk : ∀ {n} (w : B.BinaryWord n) p →
  C.re (U.tau (walk w p)) ≃ h n * (C.re (U.tau p) + j w)
realWalk B.end p =
  let open P.ℝ-Solver in solve 1
    (λ x → x ⊜ Κ 1ℚᵘ ⊗ (x ⊕ Κ 0ℚᵘ)) P.≃-refl (C.re (U.tau p))
realWalk (B.bit0 B.end) p =
  let open P.ℝ-Solver in solve 1
    (λ x → Κ (+ 1 / 2) ⊗ x ⊜ (Κ 1ℚᵘ ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ Κ 0ℚᵘ))
    P.≃-refl (C.re (U.tau p))
realWalk (B.bit1 B.end) p =
  let open P.ℝ-Solver in solve 1
    (λ x → Κ (+ 1 / 2) ⊗ (x ⊕ (⊝ Κ 1ℚᵘ))
      ⊜ (Κ 1ℚᵘ ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ (⊝ Κ 1ℚᵘ)))
    P.≃-refl (C.re (U.tau p))
realWalk {suc (suc n)} (B.bit0 w@(B.bit0 _)) p =
  P.≃-trans (realWalk w (D.left p))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ a x j → a ⊗ (Κ (+ 1 / 2) ⊗ x ⊕ j)
          ⊜ (a ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ (j ⊕ j)))
        P.≃-refl (h (suc n)) (C.re (U.tau p)) (j w))
      (P.*-congˡ (P.+-cong P.≃-refl (P.≃-symm (j0Read w)))))
realWalk {suc (suc n)} (B.bit0 w@(B.bit1 _)) p =
  P.≃-trans (realWalk w (D.left p))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ a x j → a ⊗ (Κ (+ 1 / 2) ⊗ x ⊕ j)
          ⊜ (a ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ (j ⊕ j)))
        P.≃-refl (h (suc n)) (C.re (U.tau p)) (j w))
      (P.*-congˡ (P.+-cong P.≃-refl (P.≃-symm (j0Read w)))))
realWalk {suc (suc n)} (B.bit1 w@(B.bit0 _)) p =
  P.≃-trans (realWalk w (D.right D.positive p))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ a x j → a ⊗ (Κ (+ 1 / 2) ⊗ (x ⊕ Κ 1ℚᵘ) ⊕ j)
          ⊜ (a ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ ((j ⊕ j) ⊕ Κ 1ℚᵘ)))
        P.≃-refl (h (suc n)) (C.re (U.tau p)) (j w))
      (P.*-congˡ (P.+-cong P.≃-refl (P.≃-symm (j1Read w)))))
realWalk {suc (suc n)} (B.bit1 w@(B.bit1 _)) p =
  P.≃-trans (realWalk w (D.right D.positive p))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ a x j → a ⊗ (Κ (+ 1 / 2) ⊗ (x ⊕ Κ 1ℚᵘ) ⊕ j)
          ⊜ (a ⊗ Κ (+ 1 / 2)) ⊗ (x ⊕ ((j ⊕ j) ⊕ Κ 1ℚᵘ)))
        P.≃-refl (h (suc n)) (C.re (U.tau p)) (j w))
      (P.*-congˡ (P.+-cong P.≃-refl (P.≃-symm (j1Read w)))))

imagWalk : ∀ {n} (w : B.BinaryWord n) p →
  C.im (U.tau (walk w p)) ≃ h n * C.im (U.tau p)
imagWalk B.end p = P.≃-symm (P.*-identityˡ (C.im (U.tau p)))
imagWalk {suc n} (B.bit0 w) p =
  P.≃-trans (imagWalk w (D.left p))
    (P.≃-symm (P.*-assoc (h n) D.half (C.im (U.tau p))))
imagWalk {suc n} (B.bit1 w) p =
  P.≃-trans (imagWalk w (D.right (side n) p))
    (P.≃-symm (P.*-assoc (h n) D.half (C.im (U.tau p))))

chart : ∀ {n} (w : B.BinaryWord n) p →
  U.tau (walk w p) ≈C scaleC (h n) (C.complex (C.re (U.tau p) + j w) (C.im (U.tau p)))
chart w p = realWalk w p , imagWalk w p

centeredChart : ∀ {n} (r : Addr.SignedIndex n) p →
  U.tau (walk (Addr.uncenter r) p) ≈C
    scaleC (h (suc n)) (C.complex
      (C.re (U.tau p) + K.embedInteger (Addr.integerRead r)) (C.im (U.tau p)))
centeredChart r p = complexTrans (chart (Addr.uncenter r) p)
  (P.*-congˡ (P.+-cong P.≃-refl
    (embedEq (trans
      (sym (Addr.integerOffsetRead (Addr.uncenter r)))
      (cong Addr.integerRead (Addr.centerUncenter r))))) , P.≃-refl)

-- Same binary fold order as the existing branch-outcome owner and
-- capacity partition. No new tree datatype or branch materialization.
fold : ∀ {n} → (B.BinaryWord n → BishopComplex) → BishopComplex
fold {zero} f = f B.end
fold {suc n} f = fold (λ w → f (B.bit0 w)) +C fold (λ w → f (B.bit1 w))

foldCong : ∀ {n} (f g : B.BinaryWord n → BishopComplex) →
  (∀ w → f w ≈C g w) → fold f ≈C fold g
foldCong {zero} f g eq = eq B.end
foldCong {suc n} f g eq = A.addCCongruent
  (foldCong (λ w → f (B.bit0 w)) (λ w → g (B.bit0 w)) (λ w → eq (B.bit0 w)))
  (foldCong (λ w → f (B.bit1 w)) (λ w → g (B.bit1 w)) (λ w → eq (B.bit1 w)))

foldScale : ∀ {n} a (f : B.BinaryWord n → BishopComplex) →
  scaleC a (fold f) ≈C fold (λ w → scaleC a (f w))
foldScale {zero} a f = C.≈C-refl _
foldScale {suc n} a f = complexTrans (O.scaleAdd a _ _)
  (A.addCCongruent (foldScale a (λ w → f (B.bit0 w)))
    (foldScale a (λ w → f (B.bit1 w))))

weight : ℝ → Nat → ℝ
weight a zero = R.1ℝ
weight a (suc n) = a * weight a n

selector : Nat → U.BishopUpperHalfPlanePoint → D.Side
selector n _ = side n

module At (inputs : Round11.BishopCutset) where
  module Rows = D.At inputs

  -- The existing exact refinement is the compressed aggregate. Expansion
  -- as a complete finite sum is a theorem, not a required execution path.
  module Fold (a : ℝ) (row : U.BishopUpperHalfPlanePoint → BishopComplex)
    (refine : Nat → U.BishopUpperHalfPlanePoint → BishopComplex)
    (base : ∀ p → refine zero p ≈C row p)
    (step : ∀ n p → refine (suc n) p ≈C
      scaleC a (refine n (D.left p) +C refine n (D.right (side n) p))) where

    read : ∀ n p → refine n p ≈C
      fold (λ (w : B.BinaryWord n) → scaleC (weight a n) (row (walk w p)))
    read zero p = complexTrans (base p) (complexSym (Lim.scaleOne (row p)))
    read (suc n) p =
      let f = λ (w : B.BinaryWord n) → scaleC (weight a n) (row (walk w (D.left p)))
          g = λ (w : B.BinaryWord n) → scaleC (weight a n) (row (walk w (D.right (side n) p)))
      in complexTrans (step n p)
        (complexTrans (A.scaleCCongruent (A.addCCongruent (read n (D.left p))
          (read n (D.right (side n) p))) a)
          (complexTrans (O.scaleAdd a (fold f) (fold g))
            (A.addCCongruent
              (complexTrans (foldScale a f) (foldCong _ _ (λ w → O.scaleNest a (weight a n) _)))
              (complexTrans (foldScale a g) (foldCong _ _ (λ w → O.scaleNest a (weight a n) _))))))

  module Four = Fold ((+ 1 / 16) ⋆) Rows.row4 (Rows.refine4 selector)
    (λ p → C.≈C-refl _) (λ n p → C.≈C-refl _)
  module Six = Fold ((+ 1 / 64) ⋆) Rows.row6 (Rows.refine6 selector)
    (λ p → C.≈C-refl _) (λ n p → C.≈C-refl _)

  conserved4 : ∀ n p → fold (λ (w : B.BinaryWord n) →
    scaleC (weight ((+ 1 / 16) ⋆) n) (Rows.row4 (walk w p))) ≈C Rows.row4 p
  conserved4 n p = complexTrans (complexSym (Four.read n p)) (Rows.refinement4 selector n p)

  conserved6 : ∀ n p → fold (λ (w : B.BinaryWord n) →
    scaleC (weight ((+ 1 / 64) ⋆) n) (Rows.row6 (walk w p))) ≈C Rows.row6 p
  conserved6 n p = complexTrans (complexSym (Six.read n p)) (Rows.refinement6 selector n p)
