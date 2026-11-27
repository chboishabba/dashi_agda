module DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact where

-- SOURCE-WRITTEN, UNCOMPILED. Translate the original descending packet
-- by its actual K. All closed comparisons are native exact arithmetic.
-- No external receipt is used as a proof. Kernel cost is unmeasured.
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Data.List.Base using (map)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Sum.Base using (inj₁)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆; ∣_∣)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163RealSlicePeriodExact as Slice
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163HalfUnitIsolationExact as Iso
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard

Kq : Q.ℚᵘ
Kq = Slice.negCQ

eval : ℝ → List Q.ℚᵘ → ℝ
eval u cs = Iso.horner u (map R._⋆ cs)

-- Multiply the ascending accumulator by K+u, then add c.
step : Q.ℚᵘ → List Q.ℚᵘ → List Q.ℚᵘ
step c [] = c ∷ []
step c (a ∷ as) = (c Q.+ Kq Q.* a) ∷ step a as

shiftFrom : List Q.ℚᵘ → List Q.ℚᵘ → List Q.ℚᵘ
shiftFrom acc [] = acc
shiftFrom acc (c ∷ cs) = shiftFrom (step c acc) cs

shift : List Q.ℚᵘ → List Q.ℚᵘ
shift = shiftFrom []

descending : ℝ → ℝ → List Q.ℚᵘ → ℝ
descending x acc [] = acc
descending x acc (c ∷ cs) = descending x (c ⋆ + x * acc) cs

descCong : (x : ℝ) {a b : ℝ} → a ≃ b →
  (cs : List Q.ℚᵘ) → descending x a cs ≃ descending x b cs
descCong x h [] = h
descCong x h (c ∷ cs) = descCong x (P.+-cong P.≃-refl (P.*-congˡ h)) cs

descPoint : (x y a b : ℝ) → x ≃ y → a ≃ b →
  (cs : List Q.ℚᵘ) → descending x a cs ≃ descending y b cs
descPoint x y a b h e [] = e
descPoint x y a b h e (c ∷ cs) =
  descPoint x y (c ⋆ + x * a) (c ⋆ + y * b) h
    (P.+-cong P.≃-refl (P.*-cong h e)) cs

stepSound : (u : ℝ) (c : Q.ℚᵘ) (cs : List Q.ℚᵘ) →
  eval u (step c cs) ≃ (c ⋆ + (J.K + u) * eval u cs)
stepSound u c [] = let open P.ℝ-Solver in
  solve 3 (λ c k u → c ⊕ u ⊗ Κ Q.0ℚᵘ ⊜ c ⊕ (k ⊕ u) ⊗ Κ Q.0ℚᵘ)
    P.≃-refl (c ⋆) J.K u
stepSound u c (a ∷ as) =
  P.≃-trans
    (P.+-cong (P.≃-trans (P.⋆-distrib-+ c (Kq Q.* a))
      (P.+-cong P.≃-refl (P.⋆-distrib-* Kq a)))
      (P.*-congˡ (stepSound u a as)))
    (let open P.ℝ-Solver in
      solve 5 (λ c k a u t → (c ⊕ k ⊗ a) ⊕ u ⊗ (a ⊕ (k ⊕ u) ⊗ t)
        ⊜ c ⊕ (k ⊕ u) ⊗ (a ⊕ u ⊗ t))
        P.≃-refl (c ⋆) J.K (a ⋆) u (eval u as))

shiftSound : (u : ℝ) (acc cs : List Q.ℚᵘ) →
  eval u (shiftFrom acc cs) ≃ descending (J.K + u) (eval u acc) cs
shiftSound u acc [] = P.≃-refl
shiftSound u acc (c ∷ cs) = P.≃-trans
  (shiftSound u (step c acc) cs)
  (descCong (J.K + u) (stepSound u c acc) cs)

actualShift : (u : ℝ) (cs : List Q.ℚᵘ) →
  eval u (shift cs) ≃ descending (J.K + u) R.0ℝ cs
actualShift u cs = shiftSound u [] cs

head : List Q.ℚᵘ → Q.ℚᵘ
head [] = Q.0ℚᵘ
head (a ∷ _) = a

tail : List Q.ℚᵘ → List Q.ℚᵘ
tail [] = []
tail (_ ∷ cs) = cs

drop : Nat → List Q.ℚᵘ → List Q.ℚᵘ
drop zero cs = cs
drop (suc n) cs = drop n (tail cs)

coeff : Nat → List Q.ℚᵘ → Q.ℚᵘ
coeff n cs = head (drop n cs)

Pshift Sshift : List Q.ℚᵘ
Pshift = shift Packet.diagonal
Sshift = shift Packet.slice

p0 p1 p2 p3 s0 s1 s2 s3 : Q.ℚᵘ
p0 = coeff 0 Pshift
p1 = coeff 1 Pshift
p2 = coeff 2 Pshift
p3 = coeff 3 Pshift
s0 = coeff 0 Sshift
s1 = coeff 1 Sshift
s2 = coeff 2 Sshift
s3 = coeff 3 Sshift

-- Closed rational equality checks; denominator 1 throughout the shift.
-- The exact proof is reflexivity of the integer cross, not a trusted Bool.
pZero : p0 Q.≃ Q.0ℚᵘ
pZero = Q.*≡* refl
pLinearZero : p1 Q.≃ Q.0ℚᵘ
pLinearZero = Q.*≡* refl
sZero : s0 Q.≃ Q.0ℚᵘ
sZero = Q.*≡* refl
sLinearZero : s1 Q.≃ Q.0ℚᵘ
sLinearZero = Q.*≡* refl

quadraticQ : ((+ 41 / 1) Q.* p2) Q.≃ ((+ 163 / 1) Q.* s2)
quadraticQ = Q.*≡* refl

jetQ : (((+ 41 / 1) Q.* p3) Q.- ((+ 326 / 1) Q.* s3)) Q.≃
  (((+ 163 / 1) Q.* Jet.kq) Q.* s2)
jetQ = Q.*≡* refl

quadratic : (((+ 41 / 1) ⋆) * (p2 ⋆)) ≃ (((+ 163 / 1) ⋆) * (s2 ⋆))
quadratic = P.≃-trans (P.≃-symm (P.⋆-distrib-* (+ 41 / 1) p2))
  (P.≃-trans (P.⋆-cong quadraticQ) (P.⋆-distrib-* (+ 163 / 1) s2))

jet : (((+ 41 / 1) ⋆) * (p3 ⋆) - ((+ 326 / 1) ⋆) * (s3 ⋆)) ≃
  (((+ 163 / 1) ⋆) * J.κ * (s2 ⋆))
jet = P.≃-trans
  (P.≃-symm (P.≃-trans (P.⋆-distrib-to-p⋆-q⋆ ((+ 41 / 1) Q.* p3) ((+ 326 / 1) Q.* s3))
    (P.+-cong (P.⋆-distrib-* (+ 41 / 1) p3) (P.-‿cong (P.⋆-distrib-* (+ 326 / 1) s3)))))
  (P.≃-trans (P.⋆-cong jetQ)
    (P.≃-trans (P.⋆-distrib-* ((+ 163 / 1) Q.* Jet.kq) s2)
      (P.*-congʳ (P.⋆-distrib-* (+ 163 / 1) Jet.kq))))

sliceApart : R._≄0 (s2 ⋆)
sliceApart = inj₁ (P.p<q⇒p⋆<q⋆ s2 Q.0ℚᵘ
  (from-yes (s2 QP.<? Q.0ℚᵘ)))

-- Reflect the *literal* 80-term dominance by an exact rational Horner
-- majorant. Retain the negative sign of p2 and s2 separately.
absQ : Q.ℚᵘ → Q.ℚᵘ
absQ (Q.mkℚᵘ (Z.+ n) d) = Q.mkℚᵘ (Z.+ n) d
absQ (Q.mkℚᵘ (Z.-[1+ n ]) d) = Q.mkℚᵘ (Z.+ suc n) d

absPositive : (n d : Nat) → R.NonNegative (Q.mkℚᵘ (Z.+ n) d ⋆)
absPositive n d =
  let instance
        nn : Q.NonNegative (Q.mkℚᵘ (Z.+ n) d)
        nn = Q.nonNeg
  in P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ (Q.mkℚᵘ (Z.+ n) d)
       (QP.nonNegative⁻¹ (Q.mkℚᵘ (Z.+ n) d)))

absEmbed : (q : Q.ℚᵘ) → ∣ q ⋆ ∣ ≃ (absQ q ⋆)
absEmbed (Q.mkℚᵘ (Z.+ n) d) = P.nonNegx⇒∣x∣≃x (absPositive n d)
absEmbed (Q.mkℚᵘ (Z.-[1+ n ]) d) =
  P.≃-trans (P.∣-∣-cong (P.⋆-distrib-neg (Q.mkℚᵘ (Z.+ suc n) d)))
    (P.≃-trans P.∣-x∣≃∣x∣ (P.nonNegx⇒∣x∣≃x (absPositive (suc n) d)))

halfQ : Q.ℚᵘ
halfQ = + 1 / 2

majorantQ : List Q.ℚᵘ → Q.ℚᵘ
majorantQ [] = Q.0ℚᵘ
majorantQ (c ∷ cs) = absQ c Q.+ halfQ Q.* majorantQ cs

majorantEmbed : (cs : List Q.ℚᵘ) →
  (majorantQ cs ⋆) ≃ Iso.majorant (map R._⋆ cs)
majorantEmbed [] = P.≃-refl
majorantEmbed (c ∷ cs) =
  P.≃-trans (P.⋆-distrib-+ (absQ c) (halfQ Q.* majorantQ cs))
    (P.+-cong (P.≃-symm (absEmbed c))
      (P.≃-trans (P.⋆-distrib-* halfQ (majorantQ cs)) (P.*-congˡ (majorantEmbed cs))))

pTail : List Q.ℚᵘ
pTail = drop 3 Pshift

dominanceQ : (halfQ Q.* majorantQ pTail) Q.< Q.-_ p2
dominanceQ = from-yes ((halfQ Q.* majorantQ pTail) QP.<? (Q.-_ p2))

dominance : (Iso.half * Iso.majorant (map R._⋆ pTail)) R.< R.- (p2 ⋆)
dominance = P.<-respˡ-≃
  (P.≃-trans (P.⋆-distrib-* halfQ (majorantQ pTail)) (P.*-congˡ (majorantEmbed pTail)))
  (P.<-respʳ-≃ (P.⋆-distrib-neg p2)
    (P.p<q⇒p⋆<q⋆ (halfQ Q.* majorantQ pTail) (Q.-_ p2) dominanceQ))

evalHead : (u : ℝ) (cs : List Q.ℚᵘ) →
  eval u cs ≃ (head cs ⋆ + u * eval u (tail cs))
evalHead u [] = let open P.ℝ-Solver in
  solve 1 (λ u → Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ ⊕ u ⊗ Κ Q.0ℚᵘ) P.≃-refl u
evalHead u (c ∷ cs) = P.≃-refl

doubleZero : (u : ℝ) (cs : List Q.ℚᵘ) →
  head cs Q.≃ Q.0ℚᵘ → head (tail cs) Q.≃ Q.0ℚᵘ →
  eval u cs ≃ ((u * u) * (coeff 2 cs ⋆ + Iso.tail u (map R._⋆ (drop 3 cs))))
doubleZero u cs h0 h1 =
  P.≃-trans (evalHead u cs)
    (P.≃-trans (P.+-cong (P.⋆-cong h0)
      (P.*-congˡ (P.≃-trans (evalHead u (tail cs))
        (P.+-cong (P.⋆-cong h1) (P.*-congˡ (evalHead u (drop 2 cs)))))))
      (let open P.ℝ-Solver in solve 3
        (λ u a t → Κ Q.0ℚᵘ ⊕ u ⊗ (Κ Q.0ℚᵘ ⊕ u ⊗ (a ⊕ u ⊗ t))
          ⊜ (u ⊗ u) ⊗ (a ⊕ u ⊗ t))
        P.≃-refl u (coeff 2 cs ⋆) (eval u (drop 3 cs))))

-- Native actual-root producer now needs only original analytic diagonal
-- vanishing and the half-unit enclosure. The shifted packet is not input.
rootFromLiteralDiagonal :
  ∣ Iso.offset ∣ R.≤ Iso.half →
  descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ →
  J.CMRoot
rootFromLiteralDiagonal enclosure diagonalZero =
  Iso.rootFromShiftedDiagonal (p2 ⋆) (map R._⋆ pTail) enclosure dominance
    (P.≃-trans (P.≃-symm (doubleZero Iso.offset Pshift pZero pLinearZero))
      (P.≃-trans (actualShift Iso.offset Packet.diagonal)
        (P.≃-trans (descPoint (J.K + Iso.offset) Guard.Root.j R.0ℝ R.0ℝ
          (let open P.ℝ-Solver in solve 2 (λ k j → k ⊕ (j ⊖ k) ⊜ j)
            P.≃-refl J.K Guard.Root.j) P.≃-refl Packet.diagonal) diagonalZero)))

-- Native signed-jet finite premises are now constructed from the same
-- original packet as rootFromLiteralDiagonal, not from fresh numbers.
signedJetFromPacket : (a b : ℝ) →
  R._≄0 (Jet.A J.p a) → J.FirstQJet a → J.SecondQJet b →
  Jet.literalResidual (Jet.A J.p a) (Jet.diskB J.p a b)
    (s2 ⋆) (s3 ⋆) (p2 ⋆) (p3 ⋆) ≃ R.0ℝ →
  J.SignedJet
signedJetFromPacket a b ha h1 h2 =
  Jet.signedJetFromLiteral a b (s2 ⋆) (s3 ⋆) (p2 ⋆) (p3 ⋆)
    ha sliceApart h1 h2 quadratic jet
