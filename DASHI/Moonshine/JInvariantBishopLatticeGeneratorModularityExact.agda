module DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact where

-- SOURCE-WRITTEN. Global S and T laws on the actual convergent G4/G6
-- lattice values. Finite square identities are carried to the original
-- shell limits. No Fourier identification is asserted by this file.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst; trans)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
open A using (_*C_)
open C using (_≈C_)
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open Comp using (complexTrans; complexSym)
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact as Sum
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Rot
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as X
import DASHI.Moonshine.JInvariantBishopShearExhaustionExact as Shear
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact as Re
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L

ComplexRespect : (K.NonzeroLatticePoint → C.BishopComplex) → Set
ComplexRespect f = ∀ i j → K.point i ≡ K.point j → f i ≈C f j

rawC : (K.NonzeroLatticePoint → C.BishopComplex) → L.LatticePoint → C.BishopComplex
rawC f p = C.complex (X.raw (λ i → C.re (f i)) p) (X.raw (λ i → C.im (f i)) p)

rawCRead : ∀ f → ComplexRespect f → ∀ i → rawC f (K.point i) ≈C f i
rawCRead f h i = X.rawRead (λ j → C.re (f j)) (λ j k eq → proj₁ (h j k eq)) i ,
  X.rawRead (λ j → C.im (f j)) (λ j k eq → proj₂ (h j k eq)) i

rawCPointwise : ∀ f h → (∀ i → f i ≈C h i) → ∀ p → rawC f p ≈C rawC h p
rawCPointwise f h eq p with X.origin? p
... | yes _ = C.≈C-refl A.zeroC
... | no neq = eq (K.nonzero-lattice-point p (λ h → ⊥-elim (neq h)))

rawCScale : ∀ v f p → rawC (λ i → v *C f i) p ≈C (v *C rawC f p)
rawCScale v f p with X.origin? p
... | yes _ = complexSym (Laws.complexMultiplyRightZero v)
... | no _ = C.≈C-refl _

rawCReindex : ∀ f → ComplexRespect f → ∀ g p →
  rawC (λ i → f (Re.forwardPunctured g i)) p ≈C rawC f (L.forwardIndex g p)
rawCReindex f respect g p with X.origin? p
... | yes eq rewrite eq | Re.forwardOrigin g = C.≈C-refl A.zeroC
... | no neq =
  let i = K.nonzero-lattice-point p (λ h → ⊥-elim (neq h))
      j = Re.forwardPunctured g i
      respects : ComplexRespect (λ i → f (Re.forwardPunctured g i))
      respects a b h = respect (Re.forwardPunctured g a) (Re.forwardPunctured g b)
        (cong (L.forwardIndex g) h)
  in complexTrans (rawCRead (λ i → f (Re.forwardPunctured g i)) respects i)
    (complexSym (rawCRead f respect j))

sumC : ∀ {Y : Set} → (Y → C.BishopComplex) → List Y → C.BishopComplex
sumC f ps = C.complex (Rot.sum (λ p → C.re (f p)) ps) (Rot.sum (λ p → C.im (f p)) ps)

sumCCong : ∀ {Y : Set} (f g : Y → C.BishopComplex) ps →
  (∀ p → f p ≈C g p) → sumC f ps ≈C sumC g ps
sumCCong f g ps h = Rot.sumCong _ _ ps (λ p → proj₁ (h p)) ,
  Rot.sumCong _ _ ps (λ p → proj₂ (h p))

sumCMap : ∀ {Y Z : Set} (f : Z → C.BishopComplex) (g : Y → Z) ps →
  sumC f (map g ps) ≈C sumC (λ p → f (g p)) ps
sumCMap f g ps = Rot.sumMap (λ p → C.re (f p)) g ps , Rot.sumMap (λ p → C.im (f p)) g ps

sumCPerm : ∀ {Y : Set} (f : Y → C.BishopComplex) {ps qs} →
  ps Perm.↭ qs → sumC f ps ≈C sumC f qs
sumCPerm f h = Rot.sumPerm (λ p → C.re (f p)) h , Rot.sumPerm (λ p → C.im (f p)) h

sumCMul : ∀ {Y : Set} (v : C.BishopComplex) (f : Y → C.BishopComplex) ps →
  sumC (λ p → v *C f p) ps ≈C (v *C sumC f ps)
sumCMul v f [] = complexSym (Laws.complexMultiplyRightZero v)
sumCMul v f (p ∷ ps) = complexTrans (A.addCCongruent (C.≈C-refl (v *C f p)) (sumCMul v f ps))
  (complexSym (Laws.complexMultiplyDistributesLeft v (f p) (sumC f ps)))

prefixC : Nat → U.BishopUpperHalfPlanePoint → Nat → C.BishopComplex
prefixC k p n = sumC (rawC (E.summand k p)) (S.squarePoints n)

-- The exact original finite S identity; no reindexing at infinity is hidden.
prefixS : ∀ k p n →
  prefixC k (G.actS p) n ≈C (A.powC (U.tau p) k *C prefixC k p n)
prefixS k p n =
  let f = E.summand k p
      v = A.powC (U.tau p) k
      ps = S.squarePoints n
      fS = λ i → f (Re.forwardPunctured H.S i)
      pointLaw : ∀ q → rawC fS q ≈C rawC f (Rot.rot q)
      pointLaw q = complexTrans (rawCReindex f (Rot.summandRespect k p) H.S q)
        (subst (λ t → rawC f (L.forwardIndex H.S q) ≈C rawC f t)
          (Rot.rotIsGenerator q) (C.≈C-refl _))
  in complexTrans (sumCCong _ _ ps (rawCPointwise _ _ (G.summandS k p)))
    (complexTrans (sumCCong _ _ ps (rawCScale v fS))
      (complexTrans (sumCMul v (rawC fS) ps)
        (A.mulCCongruent (C.≈C-refl v)
          (complexTrans (sumCCong _ _ ps pointLaw)
            (complexTrans (complexSym (sumCMap (rawC f) Rot.rot ps))
              (sumCPerm (rawC f) (Rot.squarePermutation n)))))))

-- The exact original finite T identity, prior to cofinal tail comparison.
prefixT : ∀ k p n → prefixC k (G.actT p) (Shear.twice n) ≈C
  sumC (rawC (E.summand k p)) (map Shear.shear (S.squarePoints (Shear.twice n)))
prefixT k p n =
  let f = E.summand k p
      ps = S.squarePoints (Shear.twice n)
      pointLaw : ∀ q → rawC (λ i → f (Re.forwardPunctured H.T i)) q ≈C rawC f (Shear.shear q)
      pointLaw q = complexTrans (rawCReindex f (Rot.summandRespect k p) H.T q)
        (subst (λ t → rawC f (L.forwardIndex H.T q) ≈C rawC f t)
          (Shear.shearIsGenerator q) (C.≈C-refl _))
  in complexTrans (sumCCong _ _ ps (rawCPointwise _ _ (G.summandT k p)))
    (complexTrans (sumCCong _ _ ps pointLaw)
      (complexSym (sumCMap (rawC f) Shear.shear ps)))

Converges : (Nat → C.BishopComplex) → C.BishopComplex → Set
Converges f v = Seq._ConvergesTo_ (λ n → C.re (f n)) (C.re v) ×
                Seq._ConvergesTo_ (λ n → C.im (f n)) (C.im v)

ShellConverges : Nat → U.BishopUpperHalfPlanePoint → C.BishopComplex → Set
ShellConverges k p v =
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellComponent n (λ i → C.re (E.summand k p i)))) (C.re v) ×
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellComponent n (λ i → C.im (E.summand k p i)))) (C.im v)

ShellAbsConverges : Nat → U.BishopUpperHalfPlanePoint → C.BishopComplex → Set
ShellAbsConverges k p v =
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellAbsolute n (λ i → C.re (E.summand k p i)))) (C.re v) ×
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellAbsolute n (λ i → C.im (E.summand k p i)))) (C.im v)

prefixLimit : ∀ k p v → ShellConverges k p v → Converges (prefixC k p) v
prefixLimit k p v (hr , hi) =
  X.prefixConverges (λ i → C.re (E.summand k p i))
    (λ i j eq → proj₁ (Rot.summandRespect k p i j eq)) (C.re v) hr ,
  X.prefixConverges (λ i → C.im (E.summand k p i))
    (λ i j eq → proj₂ (Rot.summandRespect k p i j eq)) (C.im v) hi

cofinalLimit : ∀ k p v a → ShellConverges k p v → ShellAbsConverges k p a →
  Converges (λ n → sumC (rawC (E.summand k p)) (map Shear.shear (S.squarePoints (Shear.twice n)))) v
cofinalLimit k p v a (hr , hi) (ar , ai) =
  Shear.actualCofinal (λ i → C.re (E.summand k p i))
    (λ i j eq → proj₁ (Rot.summandRespect k p i j eq)) (C.re v) (C.re a) hr ar ,
  Shear.actualCofinal (λ i → C.im (E.summand k p i))
    (λ i j eq → proj₂ (Rot.summandRespect k p i j eq)) (C.im v) (C.im a) hi ai

constant : ∀ v → Seq._isConvergent (λ _ → v)
constant v = v , Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → P.≃-refl})

mulLimit : ∀ f v a → Converges f v → Converges (λ n → a *C f n) (a *C v)
mulLimit f v (C.complex a b) (hr , hi) =
  Seq.xₙ+yₙ→x₀+y₀
    (R._*_ a (C.re v) , Seq.xₙyₙ→x₀y₀ (constant a) (C.re v , hr))
    (R.- (R._*_ b (C.im v)) , Seq.-xₙ→-x₀
      (R._*_ b (C.im v) , Seq.xₙyₙ→x₀y₀ (constant b) (C.im v , hi))) ,
  Seq.xₙ+yₙ→x₀+y₀
    (R._*_ a (C.im v) , Seq.xₙyₙ→x₀y₀ (constant a) (C.im v , hi))
    (R._*_ b (C.re v) , Seq.xₙyₙ→x₀y₀ (constant b) (C.re v , hr))

limitCong : ∀ f g v → (∀ n → f n ≈C g n) → Converges f v → Converges g v
limitCong f g v eq (hr , hi) =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → proj₁ (eq (suc n))}) (C.re v , hr) ,
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → proj₂ (eq (suc n))}) (C.im v , hi)

limitUnique : ∀ f v w → Converges f v → Converges f w → v ≈C w
limitUnique f v w (vr , vi) (wr , wi) = Seq.uniqueness-of-limits vr wr , Seq.uniqueness-of-limits vi wi

twiceLimit : ∀ f v → Converges f v → Converges (λ n → f (Shear.twice n)) v
twiceLimit f v (hr , hi) =
  Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (Seq.subseq* (Shear.twice , (λ n → P.≃-refl) , Shear.twiceIncreasing)) (C.re v , hr) ,
  Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (Seq.subseq* (Shear.twice , (λ n → P.≃-refl) , Shear.twiceIncreasing)) (C.im v , hi)

globalS : ∀ k p v w → ShellConverges k p v → ShellConverges k (G.actS p) w →
  w ≈C (A.powC (U.tau p) k *C v)
globalS k p v w hv hw = limitUnique (prefixC k (G.actS p)) w (A.powC (U.tau p) k *C v)
  (prefixLimit k (G.actS p) w hw)
  (limitCong _ _ _ (λ n → complexSym (prefixS k p n))
    (mulLimit (prefixC k p) v (A.powC (U.tau p) k) (prefixLimit k p v hv)))

globalT : ∀ k p v w a → ShellConverges k p v → ShellConverges k (G.actT p) w →
  ShellAbsConverges k p a → w ≈C v
globalT k p v w a hv hw ha = limitUnique (λ n → prefixC k (G.actT p) (Shear.twice n)) w v
  (twiceLimit (prefixC k (G.actT p)) w (prefixLimit k (G.actT p) w hw))
  (limitCong _ _ _ (λ n → complexSym (prefixT k p n)) (cofinalLimit k p v a hv ha))

-- All four classical lattice generator identities instantiated on
-- the very same original summand and shell limits constructed earlier.
module At (p : U.BishopUpperHalfPlanePoint) where
  module B = Sum.At p
  module BS = Sum.At (G.actS p)
  module BT = Sum.At (G.actT p)
  abs4 = C.complex (Seq.lim B.real4Absolute) (Seq.lim B.imag4Absolute)
  abs6 = C.complex (Seq.lim B.real6Absolute) (Seq.lim B.imag6Absolute)

  G4S : BS.G4 ≈C (A.powC (U.tau p) 4 *C B.G4)
  G4S = globalS 4 p B.G4 BS.G4 (proj₂ B.real4 , proj₂ B.imag4) (proj₂ BS.real4 , proj₂ BS.imag4)

  G6S : BS.G6 ≈C (A.powC (U.tau p) 6 *C B.G6)
  G6S = globalS 6 p B.G6 BS.G6 (proj₂ B.real6 , proj₂ B.imag6) (proj₂ BS.real6 , proj₂ BS.imag6)

  G4T : BT.G4 ≈C B.G4
  G4T = globalT 4 p B.G4 BT.G4 abs4 (proj₂ B.real4 , proj₂ B.imag4)
    (proj₂ BT.real4 , proj₂ BT.imag4) (proj₂ B.real4Absolute , proj₂ B.imag4Absolute)

  G6T : BT.G6 ≈C B.G6
  G6T = globalT 6 p B.G6 BT.G6 abs6 (proj₂ B.real6 , proj₂ B.imag6)
    (proj₂ BT.real6 , proj₂ BT.imag6) (proj₂ B.real6Absolute , proj₂ B.imag6Absolute)
