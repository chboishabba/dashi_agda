module DASHI.Moonshine.JInvariantBishopSquareExhaustionExact where

-- Original square exhaustion = original shell partials, and exact
-- absolute-tail transport through any intermediate unique finite list.
-- The origin is only an omitted index, never a reciprocal.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Integer.Base using (+_)
import Data.Integer.Properties as ZP
open import Data.List.Base using (List; []; _∷_; _++_; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst; trans)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as D
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
open Re using (sum; sumPerm; sumCong; PointRespect)

legacyEmpty : L.⊥ → ⊥
legacyEmpty ()

origin? : (p : L.LatticePoint) → Dec (p ≡ K.origin)
origin? (L.lattice-point m n) with m ZP.≟ (+ 0) | n ZP.≟ (+ 0)
... | yes a | yes b = yes (L.lattice-ext a b)
... | no a | _ = no (λ eq → a (cong L.horizontal eq))
... | yes a | no b = no (λ eq → b (cong L.vertical eq))

raw : (K.NonzeroLatticePoint → ℝ) → L.LatticePoint → ℝ
raw f p with origin? p
... | yes _ = R.0ℝ
... | no neq = f (K.nonzero-lattice-point p (λ h → ⊥-elim (neq h)))

rawRead : ∀ f → PointRespect f → ∀ i → raw f (K.point i) ≃ f i
rawRead f respect i with origin? (K.point i)
... | yes eq = ⊥-elim (legacyEmpty (K.notOrigin i eq))
... | no neq = respect (K.nonzero-lattice-point (K.point i) (λ h → ⊥-elim (neq h))) i refl

rawAbs : ∀ f p → raw (λ i → ∣ f i ∣) p ≃ ∣ raw f p ∣
rawAbs f p with origin? p
... | yes _ = P.≃-symm (P.nonNegx⇒∣x∣≃x P.nonNeg0)
... | no _ = P.≃-refl

insideMono : ∀ n m → n ≤ m → ∀ p → T (S.insideSquare? n p) → T (S.insideSquare? m p)
insideMono n m nm (L.lattice-point a b) h = Equivalence.from T-∧
  (Cut.coordinateInCutoffMonotone n m nm a (proj₁ (Equivalence.to T-∧ h)) ,
   Cut.coordinateInCutoffMonotone n m nm b (proj₂ (Equivalence.to T-∧ h)))

squareSubset : ∀ n m → n ≤ m → ∀ {p} → p ∈ S.squarePoints n → p ∈ S.squarePoints m
squareSubset n m nm {p} h = Re.squareMember m p (insideMono n m nm p (Re.squareSound n p h))

opposite : ∀ b → T b → T (Data.Bool.Base.not b) → ⊥
opposite true h ()
opposite false () h

squarePartition : ∀ n → S.squarePoints (suc n) Perm.↭
  (S.squarePoints n ++ S.successorSquareShell n)
squarePartition n = W.uniqueMembershipEquivalenceToPermutation
  (S.squarePointsUnique (suc n))
  (D.uniqueAppendDisjoint (S.squarePointsUnique n) (S.successorSquareShellUnique n) disjoint)
  forward backward
  where
  disjoint : ∀ {p q} → p ∈ S.squarePoints n → q ∈ S.successorSquareShell n → p ≡ q → ⊥
  disjoint {p} {q} hp hq eq = opposite (S.insideSquare? n q)
    (subst (λ x → T (S.insideSquare? n x)) eq (Re.squareSound n p hp))
    (proj₂ (Equivalence.to T-∧ (Re.shellSound n q hq)))

  forward : ∀ {p} → p ∈ S.squarePoints (suc n) →
    p ∈ (S.squarePoints n ++ S.successorSquareShell n)
  forward {p} h with S.insideSquare? n p in eq
  ... | true = D.appendMemberLeft (Re.squareMember n p (subst T (sym eq) tt))
  ... | false = D.appendMemberRight (S.squarePoints n) (Re.shellMember n p
    (Equivalence.from T-∧ (Re.squareSound (suc n) p h ,
      subst (λ b → T (Data.Bool.Base.not b)) (sym eq) tt)))

  backward : ∀ {p} → p ∈ (S.squarePoints n ++ S.successorSquareShell n) →
    p ∈ S.squarePoints (suc n)
  backward {p} h with ∈-++⁻ (S.squarePoints n) h
  ... | inj₁ hp = squareSubset n (suc n) (NP.n≤1+n n) hp
  ... | inj₂ hp = Re.squareMember (suc n) p (proj₁ (Equivalence.to T-∧ (Re.shellSound n p hp)))

sumAppend : ∀ {X : Set} (f : X → ℝ) ps qs →
  sum f (ps ++ qs) ≃ (sum f ps + sum f qs)
sumAppend f [] qs = P.≃-symm (P.+-identityˡ (sum f qs))
sumAppend f (p ∷ ps) qs = P.≃-trans
  (P.+-cong P.≃-refl (sumAppend f ps qs))
  (P.≃-symm (P.+-assoc (f p) (sum f ps) (sum f qs)))

filterRead : ∀ n f → PointRespect f → ∀ ps →
  sum (Re.guard n f) ps ≃ sum (raw f) (filterᵇ (S.onSuccessorSquareShell? n) ps)
filterRead n f respect [] = P.≃-refl
filterRead n f respect (p ∷ ps) with S.onSuccessorSquareShell? n p in eq
... | false = P.≃-trans (P.+-identityˡ (sum (Re.guard n f) ps)) (filterRead n f respect ps)
... | true = P.+-cong (P.≃-symm (rawRead f respect
    (F.nonzero n p (subst T (sym eq) tt)))) (filterRead n f respect ps)

shellRead : ∀ n f → PointRespect f →
  F.shellComponent n f ≃ sum (raw f) (S.successorSquareShell n)
shellRead n f respect = P.≃-trans (Re.foldRead n f (S.squarePoints (suc n)))
  (filterRead n f respect (S.squarePoints (suc n)))

prefix : (K.NonzeroLatticePoint → ℝ) → Nat → ℝ
prefix f n = sum (raw f) (S.squarePoints n)

prefixRead : ∀ f → PointRespect f → ∀ n →
  prefix f n ≃ Seq.SeriesOf (λ k → F.shellComponent k f) n
prefixRead f respect zero = P.+-identityˡ R.0ℝ
prefixRead f respect (suc n) =
  P.≃-trans (sumPerm (raw f) (squarePartition n))
    (P.≃-trans (sumAppend (raw f) (S.squarePoints n) (S.successorSquareShell n))
      (P.+-cong (prefixRead f respect n) (P.≃-symm (shellRead n f respect))))

prefixConverges : ∀ f → PointRespect f → (v : ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellComponent k f)) v →
  Seq._ConvergesTo_ (prefix f) v
prefixConverges f respect v h = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-symm (prefixRead f respect (suc n))}) (v , h)

absPrefixConverges : ∀ f → PointRespect f → (v : ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellAbsolute k f)) v →
  Seq._ConvergesTo_ (λ n → sum (λ p → ∣ raw f p ∣) (S.squarePoints n)) v
absPrefixConverges f respect v h = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → sumCong (raw (λ i → ∣ f i ∣)) (λ p → ∣ raw f p ∣)
    (S.squarePoints (suc n)) (rawAbs f)})
  (v , prefixConverges (λ i → ∣ f i ∣) (λ i j eq → P.∣-∣-cong (respect i j eq)) v h)

-- The actual unique membership removal owner supplies a remainder list.
-- This gives a two-sided, signed difference bound, not a cardinality proxy.
subsetDecomp : ∀ {X : Set} {ps qs : List X} → Unique ps → Unique qs →
  (∀ {p} → p ∈ ps → p ∈ qs) → Σ (List X) (λ rs → qs Perm.↭ (ps ++ rs))
subsetDecomp {ps = []} {qs} up uq incl = qs , Perm.refl
subsetDecomp {ps = p ∷ ps} {qs} (AP._∷_ fresh rest) uq incl =
  let selected = incl (Any.here refl)
      tail : ∀ {q} → q ∈ ps → q ∈ W.removeAt selected
      tail h = W.otherMemberSurvivesRemoval selected (incl (Any.there h))
        (λ eq → All.lookup fresh h (sym eq))
      rec = subsetDecomp rest (W.removeAtUnique uq selected) tail
  in proj₁ rec , Perm.trans (W.removeAtPermutation selected) (Perm.prep p (proj₂ rec))


sumNN : ∀ {X : Set} (f : X → ℝ) → (∀ p → R.NonNegative (f p)) → ∀ ps → R.NonNegative (sum f ps)
sumNN f h [] = P.nonNeg0
sumNN f h (p ∷ ps) = P.nonNegx,y⇒nonNegx+y (h p) (sumNN f h ps)

sumTriangle : ∀ {X : Set} (f : X → ℝ) ps → R._≤_ ∣ sum f ps ∣ (sum (λ p → ∣ f p ∣) ps)
sumTriangle f [] = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
sumTriangle f (p ∷ ps) = P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (f p) (sum f ps))
  (P.+-mono-≤ P.≤-refl (sumTriangle f ps))

differenceRead : ∀ {X : Set} (f : X → ℝ) {ps qs rs} →
  qs Perm.↭ (ps ++ rs) → (sum f qs - sum f ps) ≃ sum f rs
differenceRead f {ps} {qs} {rs} perm =
  P.≃-trans (P.+-cong (P.≃-trans (sumPerm f perm) (sumAppend f ps rs)) P.≃-refl)
    (let open P.ℝ-Solver in solve 2 (λ p r → (p ⊕ r) ⊖ p ⊜ r) P.≃-refl (sum f ps) (sum f rs))

subsetDifference : ∀ {X : Set} (f : X → ℝ) {ps qs : List X} →
  Unique ps → Unique qs → (∀ {p} → p ∈ ps → p ∈ qs) →
  R._≤_ ∣ sum f qs - sum f ps ∣
    (sum (λ p → ∣ f p ∣) qs - sum (λ p → ∣ f p ∣) ps)
subsetDifference f up uq incl with subsetDecomp up uq incl
... | rs , perm =
  P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (differenceRead f perm)))
    (P.≤-respʳ-≃ (P.≃-symm (differenceRead (λ p → ∣ f p ∣) perm)) (sumTriangle f rs))

subsetMono : ∀ {X : Set} (f : X → ℝ) {ps qs : List X} →
  (∀ p → R.NonNegative (f p)) → Unique ps → Unique qs →
  (∀ {p} → p ∈ ps → p ∈ qs) → R._≤_ (sum f ps) (sum f qs)
subsetMono f {ps} {qs} h up uq incl with subsetDecomp up uq incl
... | rs , perm = P.≤-respʳ-≃ (P.≃-symm (P.≃-trans (sumPerm f perm) (sumAppend f ps rs)))
  (Seq.0≤x⇒y≤y+x (sum f ps) (P.nonNegx⇒0≤x (sumNN f h rs)))

-- Every finite reindexing inside an outer shell budget inherits the
-- same absolute tail; the selected interior is retained exactly.
sandwich : ∀ {X : Set} (f : X → ℝ) {ps qs rs : List X} →
  Unique ps → Unique qs → Unique rs →
  (∀ {p} → p ∈ ps → p ∈ qs) → (∀ {p} → p ∈ qs → p ∈ rs) →
  R._≤_ ∣ sum f qs - sum f ps ∣
    (sum (λ p → ∣ f p ∣) rs - sum (λ p → ∣ f p ∣) ps)
sandwich f {ps} {qs} {rs} up uq ur pq qr =
  P.≤-trans (subsetDifference f up uq pq)
    (P.+-monoˡ-≤ (R.- (sum (λ p → ∣ f p ∣) ps))
      (subsetMono (λ p → ∣ f p ∣) (λ p → P.nonNeg∣x∣ (f p)) uq ur qr))
