module DASHI.Moonshine.CM163BishopHecke41SectorFilterExact where

-- SOURCE-WRITTEN, kernel pending. Exact off-sector cancellation on
-- the actual primitive Machin phase. This works for ALL degrees,
-- not only the finite coefficient-packet cutoffs.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; s≤s)
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_; _/_; m%n<n; m≡m%n+[m/n]*n)
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41PrimitivePhaseExact as Primitive
import DASHI.Moonshine.CM163BishopHecke41ProductExact as H
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

powIndex : ∀ z {a b : Nat} → a ≡ b → powC z a ≈C powC z b
powIndex z refl = C.≈C-refl _

subMul : ∀ a b c → ((a -C b) *C c) ≈C ((a *C c) -C (b *C c))
subMul a b c =
  complexTrans (L.complexMultiplyCommutative (a -C b) c)
    (complexTrans (Alg.mulSub c a b)
      (A.subCCongruent (L.complexMultiplyCommutative c a) (L.complexMultiplyCommutative c b)))

geometric : BishopComplex → Nat → BishopComplex
geometric z zero = A.zeroC
geometric z (suc n) = A.oneC +C (z *C geometric z n)

geoTelescoping : ∀ z n → ((z -C A.oneC) *C geometric z n) ≈C (powC z n -C A.oneC)
geoTelescoping z zero = complexTrans (L.complexMultiplyRightZero _) (complexSym (H.differenceSelf A.oneC))
geoTelescoping z (suc n) =
  let g = geometric z n
      d = z -C A.oneC
      p = powC z n
  in complexTrans (L.complexMultiplyDistributesLeft d A.oneC (z *C g))
    (complexTrans (A.addCCongruent (L.complexMultiplyRightIdentity d)
      (complexTrans (complexSym (L.complexMultiplyAssociative d z g))
        (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative d z) (C.≈C-refl g))
          (complexTrans (L.complexMultiplyAssociative z d g)
            (A.mulCCongruent (C.≈C-refl z) (geoTelescoping z n))))))
      (complexTrans (A.addCCongruent (C.≈C-refl d) (Alg.mulSub z p A.oneC))
        (complexTrans (A.addCCongruent (C.≈C-refl d)
          (A.subCCongruent (C.≈C-refl _) (L.complexMultiplyRightIdentity z)))
          (cancelMiddle z (z *C p)))))
  where
  cancelMiddle : ∀ z p → ((z -C A.oneC) +C (p -C z)) ≈C (p -C A.oneC)
  cancelMiddle (C.complex a b) (C.complex c d) =
    (let open P.ℝ-Solver in solve 2 (λ a c → (a ⊖ Κ 1ℚᵘ) ⊕ (c ⊖ a) ⊜ c ⊖ Κ 1ℚᵘ)
      P.≃-refl a c) ,
    (let open P.ℝ-Solver in solve 2 (λ b d → (b ⊖ Κ 0ℚᵘ) ⊕ (d ⊖ b) ⊜ d ⊖ Κ 0ℚᵘ)
      P.≃-refl b d)

module At (inputs : Round11.BishopCutset) where
  module Rm = Ram.At inputs
  module Pr = Primitive.At inputs

  zeta = Rm.zeta

  period : ∀ n → powC zeta (n * 41) ≈C A.oneC
  period n = complexTrans (complexSym (Ram.powPow zeta 41 n))
    (complexTrans (A.powCCongruent Rm.phaseOrder n) (Power.powUnit n))

  reduce : ∀ n → powC zeta n ≈C powC zeta (n % 41)
  reduce n = complexTrans (powIndex zeta (m≡m%n+[m/n]*n n 41))
    (complexTrans (complexSym (Power.powAdd zeta (n % 41) ((n / 41) * 41)))
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (period (n / 41)))
        (L.complexMultiplyRightIdentity _)))

  gapResidue : ∀ k → k < 41 → (k ≡ zero → ⊥) →
    Rec.BishopComplexNonzero (powC zeta k -C A.oneC)
  gapResidue zero bound h = ⊥-elim (h refl)
  gapResidue (suc k) (s≤s bound) h =
    Phase.guardCong
      (A.subCCongruent (powIndex zeta (cong suc (FP.toℕ-fromℕ< bound))) (C.≈C-refl _))
      (Pr.primitive (Fin.fromℕ< bound))

  gapNZ : ∀ n → (n % 41 ≡ zero → ⊥) →
    Rec.BishopComplexNonzero (powC zeta n -C A.oneC)
  gapNZ n h = Phase.guardCong (complexSym (A.subCCongruent (reduce n) (C.≈C-refl _)))
    (gapResidue (n % 41) (m%n<n n 41) h)

  offSectorZero : ∀ n c → (n % 41 ≡ zero → ⊥) →
    (powC zeta n *C c) ≈C c → c ≈C A.zeroC
  offSectorZero n c h hc =
    J.cancelLeft (powC zeta n -C A.oneC) c A.zeroC (gapNZ n h)
      (complexTrans (subMul (powC zeta n) A.oneC c)
        (complexTrans (A.subCCongruent hc (L.complexMultiplyLeftIdentity c))
          (complexTrans (H.differenceSelf c) (complexSym (L.complexMultiplyRightZero _)))))

  rootTraceZero : ∀ n → (n % 41 ≡ zero → ⊥) →
    geometric (powC zeta n) 41 ≈C A.zeroC
  rootTraceZero n h =
    let z = powC zeta n
        order = complexTrans (Ram.powPow zeta n 41)
          (complexTrans (powIndex zeta (NP.*-comm 41 n)) (period n))
    in J.cancelLeft (z -C A.oneC) (geometric z 41) A.zeroC (gapNZ n h)
      (complexTrans (geoTelescoping z 41)
        (complexTrans (A.subCCongruent order (C.≈C-refl _))
          (complexTrans (H.differenceSelf A.oneC) (complexSym (L.complexMultiplyRightZero _)))))

  -- If the coefficient stream is rotation-covariant, all nonzero
  -- residual classes vanish, with a real apartness witness.
  sectorFilter : (c : Nat → BishopComplex) →
    (∀ n → (powC zeta n *C c n) ≈C c n) →
    ∀ n → (n % 41 ≡ zero → ⊥) → c n ≈C A.zeroC
  sectorFilter c cov n hn = offSectorZero n (c n) hn (cov n)
