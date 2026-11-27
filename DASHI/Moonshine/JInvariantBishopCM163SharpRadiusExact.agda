module DASHI.Moonshine.JInvariantBishopCM163SharpRadiusExact where

-- Source-written. Tight rational enclosure of the original CM radius.
-- Use the original all-index Machin rate, original semantic square root,
-- original exponential series and exp addition. No trigonometric phase
-- or CM root assumption. Rational decisions are native proof terms.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_)
open import Data.Nat.Base using (s≤s; z≤n)
import Data.Nat.Properties as NP
import Data.Nat.Base as Nat
import Data.Integer.Base as Z
open import Relation.Binary.PropositionalEquality using (sym; trans)
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Neg
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as MS
import DASHI.Analysis.BishopMachinGeometricBishopRateExact as MR
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as SQ
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as E
import DASHI.Foundations.BishopExponentialPositiveOrderExact as EP
import DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact as EM
import DASHI.Foundations.BishopExponentialCauchyProductExact as EC
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as EG
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as G
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM

Band : Q.ℚᵘ → ℝ → Q.ℚᵘ → Set
Band l x u = ((l ⋆) ≤ x) × (x ≤ (u ⋆))

rat≤ : (l u : Q.ℚᵘ) → l Q.≤ u → (l ⋆) ≤ (u ⋆)
rat≤ = P.p≤q⇒p⋆≤q⋆

nn : (x : Q.ℚᵘ) → Q.0ℚᵘ Q.≤ x → R.NonNegative (x ⋆)
nn = G.ratNN

-- Signed difference bound, both directions. No real trichotomy.
errorBand : (l u : Q.ℚᵘ) (x y e : ℝ) →
  (l ⋆) ≤ y - e → y + e ≤ (u ⋆) → ∣ x - y ∣ ≤ e → Band l x u
errorBand l u x y e hl hu h =
  let open P.ℝ-Solver
      hi = P.≤-trans (P.x≤∣x∣ {x = x - y}) h
  in P.≤-trans hl (P.≤-respʳ-≃
       (solve 2 (λ x y → y ⊖ (y ⊖ x) ⊜ x) P.≃-refl x y)
       (P.+-monoʳ-≤ y (P.neg-mono-≤ (P.≤-trans
         (P.x≤∣x∣ {x = y - x})
         (P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ x y) h))))) ,
     P.≤-trans (P.≤-respˡ-≃
       (solve 2 (λ x y → y ⊕ (x ⊖ y) ⊜ x) P.≃-refl x y)
       (P.+-monoʳ-≤ y hi)) hu

piL piU sqrtL sqrtU xL xU eL eU rL rU : Q.ℚᵘ
piL = + 31415926535897932384626433832795028841971 / 10000000000000000000000000000000000000000
piU = + 31415926535897932384626433832795028841972 / 10000000000000000000000000000000000000000
sqrtL = + 127671453348037046617109520097808923473823 / 10000000000000000000000000000000000000000
sqrtU = + 127671453348037046617109520097808923473824 / 10000000000000000000000000000000000000000
xL = + 626705781111445621177345056607 / 1000000000000000000000000000000
xU = + 626705781111445621177345056608 / 1000000000000000000000000000000
eL = + 18714354956515889745093173430 / 10000000000000000000000000000
eU = + 18714354956515889745093173431 / 10000000000000000000000000000
rL = + 380898093700765233822623150 / 100000000000000000000000000000000000000000000
rU = + 380898093700765233822623153 / 100000000000000000000000000000000000000000000

stage err : Q.ℚᵘ
stage = MS.qMachinStage 32
err = MS.qPow (+ 1 / 25) 32 Q.* (+ 4 / 1)

piBand : Band piL M.bishopMachinPi piU
piBand = errorBand piL piU M.bishopMachinPi (stage ⋆) (err ⋆)
  (P.≤-respʳ-≃ (P.⋆-distrib-to-p⋆-q⋆ stage err)
    (rat≤ piL (stage Q.- err) (from-yes (piL QP.≤? (stage Q.- err)))))
  (P.≤-respˡ-≃ (P.⋆-distrib-+ stage err)
    (rat≤ (stage Q.+ err) piU (from-yes ((stage Q.+ err) QP.≤? piU))))
  (P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-* (MS.qPow (+ 1 / 25) 32) (+ 4 / 1)))
    (MR.machinBishopFourOver25RationalStage 32))

sqrtBand : Band sqrtL N.r sqrtU
sqrtBand =
  Reflect.squareReflectsOnNonnegative (nn sqrtL (from-yes (Q.0ℚᵘ QP.≤? sqrtL))) G.rootNN
    (P.≤-respˡ-≃ (P.⋆-distrib-* sqrtL sqrtL)
      (P.≤-respʳ-≃ (P.≃-symm (SQ.canonicalFloorSquareRootSquaresToNat 163))
        (rat≤ (sqrtL Q.* sqrtL) (+ 163 / 1) (from-yes ((sqrtL Q.* sqrtL) QP.≤? (+ 163 / 1)))))) ,
  Reflect.squareReflectsOnNonnegative G.rootNN (nn sqrtU (from-yes (Q.0ℚᵘ QP.≤? sqrtU)))
    (P.≤-respʳ-≃ (P.⋆-distrib-* sqrtU sqrtU)
      (P.≤-respˡ-≃ (P.≃-symm (SQ.canonicalFloorSquareRootSquaresToNat 163))
        (rat≤ (+ 163 / 1) (sqrtU Q.* sqrtU) (from-yes ((+ 163 / 1) QP.≤? (sqrtU Q.* sqrtU))))))

scale : Q.ℚᵘ
scale = + 1 / 64

small : ℝ
small = (scale ⋆) * G.exponent

smallBand : Band xL small xU
smallBand =
  let lo = scale Q.* (piL Q.* sqrtL)
      hi = scale Q.* (piU Q.* sqrtU)
      pNN = nn piL (from-yes (Q.0ℚᵘ QP.≤? piL))
      piNN = P.0≤x⇒nonNegx (P.≤-trans (rat≤ Q.0ℚᵘ piL (from-yes (Q.0ℚᵘ QP.≤? piL))) (proj₁ piBand))
      sNN = nn scale (from-yes (Q.0ℚᵘ QP.≤? scale))
      unfoldProd : (a b : Q.ℚᵘ) → ((scale Q.* (a Q.* b)) ⋆) ≃ ((scale ⋆) * ((a ⋆) * (b ⋆)))
      unfoldProd a b = P.≃-trans (P.⋆-distrib-* scale (a Q.* b)) (P.*-congˡ (P.⋆-distrib-* a b))
  in P.≤-trans (rat≤ xL lo (from-yes (xL QP.≤? lo)))
       (P.≤-respˡ-≃ (P.≃-symm (unfoldProd piL sqrtL))
         (P.≤-respʳ-≃ (P.*-congˡ (P.≃-symm G.exponentShape))
           (P.*-monoˡ-≤-nonNeg (P.*-mono-≤ pNN
             (nn sqrtL (from-yes (Q.0ℚᵘ QP.≤? sqrtL))) (proj₁ piBand) (proj₁ sqrtBand)) sNN))) ,
     P.≤-trans (P.≤-respʳ-≃ (P.≃-symm (unfoldProd piU sqrtU))
       (P.≤-respˡ-≃ (P.*-congˡ (P.≃-symm G.exponentShape))
         (P.*-monoˡ-≤-nonNeg (P.*-mono-≤ piNN G.rootNN (proj₂ piBand) (proj₂ sqrtBand)) sNN)))
       (rat≤ hi xU (from-yes (hi QP.≤? xU)))

-- Rational partial sums of the literal expTerm. Range reduction means
-- 32 terms suffice, avoiding a Taylor series at exponent 40.
qTerm : Q.ℚᵘ → Nat → Q.ℚᵘ
qTerm x n = MS.qPow x n Q.* E.inverseFactorial n

qPartial : Q.ℚᵘ → Nat → Q.ℚᵘ
qPartial x zero = Q.0ℚᵘ
qPartial x (suc n) = qPartial x n Q.+ qTerm x n

termRead : (x : Q.ℚᵘ) (n : Nat) → (qTerm x n ⋆) ≃ E.expTerm (x ⋆) n
termRead x n = P.≃-trans (P.⋆-distrib-* (MS.qPow x n) (E.inverseFactorial n))
  (P.*-congʳ (MS.qPowEmbeds x n))

partialRead : (x : Q.ℚᵘ) (n : Nat) → (qPartial x n ⋆) ≃ S.SeriesOf (E.expTerm (x ⋆)) n
partialRead x zero = P.≃-refl
partialRead x (suc n) = P.≃-trans (P.⋆-distrib-+ (qPartial x n) (qTerm x n))
  (P.+-cong (partialRead x n) (termRead x n))

-- Uniform geometric tail, with the first omitted term retained.
-- The ratio is 1/16 for every term from degree 32 onward, for 0<=x<=1.
module ExpTail (x : ℝ) (xNN : R.NonNegative x) (x1 : x ≤ R.1ℝ) where
  t = E.expTerm x
  ps = S.SeriesOf t

  factor : (n : Nat) → t (suc n) ≃ (x * ((+ 1 / suc n) ⋆)) * t n
  factor n =
    P.≃-trans (P.*-congˡ (E.embeddedInverseFactorialSuccessor n))
      (let open P.ℝ-Solver in solve 4 (λ v x r f → (v ⊗ x) ⊗ (r ⊗ f) ⊜ (x ⊗ r) ⊗ (v ⊗ f))
        P.≃-refl (R.pow x n) x ((+ 1 / suc n) ⋆) (E.embed (E.inverseFactorial n)))

  step : (n : Nat) → t (suc (n +N 32)) ≤ ((+ 1 / 16) ⋆) * t (n +N 32)
  step n =
    let j = n +N 32
        recip = ((+ 1 / suc j) ⋆)
        recipNN = nn (+ 1 / suc j) (QP.nonNegative⁻¹ (+ 1 / suc j))
        le : 16 Nat.≤ suc j
        le = NP.≤-trans (from-yes (16 NP.≤? 33)) (s≤s (NP.m≤n+m 32 n))
    in P.≤-respˡ-≃ (P.≃-symm (factor j))
      (P.*-monoʳ-≤-nonNeg
        (P.≤-trans (P.≤-respʳ-≃ (P.*-identityˡ recip)
          (P.*-monoʳ-≤-nonNeg x1 recipNN))
          (rat≤ (+ 1 / suc j) (+ 1 / 16)
            (Q.*≤* (Z.+≤+ (NP.≤-trans
              (NP.≤-reflexive (NP.*-identityˡ 16))
              (NP.≤-trans le (NP.≤-reflexive (sym (NP.*-identityʳ (suc j))))))))))
        (EP.expTermNonnegative xNN j))

  budget : Nat → ℝ
  budget n = ((+ 16 / 15) ⋆) * t (n +N 32)

  pay : (n : Nat) → t (n +N 32) + budget (suc n) ≤ budget n
  pay n = let open P.ℝ-Solver in
    P.≤-respʳ-≃ (solve 1 (λ a → a ⊕ Κ (+ 16 / 15) ⊗ (Κ (+ 1 / 16) ⊗ a) ⊜ Κ (+ 16 / 15) ⊗ a)
      P.≃-refl (t (n +N 32)))
      (P.+-monoʳ-≤ (t (n +N 32)) (P.*-monoˡ-≤-nonNeg (step n)
        (nn (+ 16 / 15) (QP.nonNegative⁻¹ (+ 16 / 15)))))

  invariant : (n : Nat) → ps (n +N 32) + budget n ≤ ps 32 + budget zero
  invariant zero = P.≤-refl
  invariant (suc n) = P.≤-trans
    (P.≤-respˡ-≃ (P.≃-symm (P.+-assoc (ps (n +N 32)) (t (n +N 32)) (budget (suc n))))
      (P.+-monoʳ-≤ (ps (n +N 32)) (pay n))) (invariant n)

  partialUpper : (n : Nat) → ps (n +N 32) ≤ ps 32 + budget zero
  partialUpper n = P.≤-trans
    (S.0≤x⇒y≤y+x (ps (n +N 32))
      (P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y (nn (+ 16 / 15) (QP.nonNegative⁻¹ (+ 16 / 15)))
        (EP.expTermNonnegative xNN (n +N 32))))) (invariant n)

  upper : E.bishopExp x ≤ ps 32 + budget zero
  upper = S.xₙ≤yₙ⇒limxₙ≤limyₙ partialUpper
    (E.bishopExp x , S.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (S.shift-is-subsequence ps 32) (E.bishopExp x , E.bishopExpConverges x))
    ((ps 32 + budget zero) , S.xₙ≃c⇒xₙ→c (λ {(suc n) → P.≃-refl}))

expBand : Band eL (E.bishopExp small) eU
expBand =
  let loNN = nn xL (from-yes (Q.0ℚᵘ QP.≤? xL))
      hiNN = nn xU (from-yes (Q.0ℚᵘ QP.≤? xU))
      smallNN = P.0≤x⇒nonNegx (P.≤-trans (rat≤ Q.0ℚᵘ xL (from-yes (Q.0ℚᵘ QP.≤? xL))) (proj₁ smallBand))
      module T = ExpTail (xU ⋆) hiNN (rat≤ xU Q.1ℚᵘ (from-yes (xU QP.≤? Q.1ℚᵘ)))
      upperQ = qPartial xU 32 Q.+ ((+ 16 / 15) Q.* qTerm xU 32)
      upperRead = P.≃-trans (P.⋆-distrib-+ (qPartial xU 32) ((+ 16 / 15) Q.* qTerm xU 32))
        (P.+-cong (partialRead xU 32)
          (P.≃-trans (P.⋆-distrib-* (+ 16 / 15) (qTerm xU 32)) (P.*-congˡ (termRead xU 32))))
  in P.≤-trans (rat≤ eL (qPartial xL 32) (from-yes (eL QP.≤? qPartial xL 32)))
       (P.≤-trans (P.≤-respˡ-≃ (P.≃-symm (partialRead xL 32))
         (S.xₙisIncreasing⇒xₙ≤limxₙ (EP.expPartialSumsIncreasing loNN) (EP.expSeriesConvergent (xL ⋆)) 32))
         (EM.bishopExpMonotoneNonnegative loNN (proj₁ smallBand))) ,
     P.≤-trans (EM.bishopExpMonotoneNonnegative smallNN (proj₂ smallBand))
       (P.≤-trans (P.≤-respʳ-≃ (P.≃-symm upperRead) T.upper)
         (rat≤ upperQ eU (from-yes (upperQ QP.≤? eU))))

-- Six literal doubling steps. Preserve original exp, not a new constant.
double : ℝ → ℝ
double x = x + x

iter : (ℝ → ℝ) → Nat → ℝ → ℝ
iter f zero x = x
iter f (suc n) x = f (iter f n x)

square : ℝ → ℝ
square x = x * x

expDouble : (n : Nat) (x : ℝ) → E.bishopExp (iter double n x) ≃ iter square n (E.bishopExp x)
expDouble zero x = P.≃-refl
expDouble (suc n) x = P.≃-trans (EC.bishopExpAdd (iter double n x) (iter double n x))
  (P.*-cong (expDouble n x) (expDouble n x))

qSquare : Q.ℚᵘ → Q.ℚᵘ
qSquare x = x Q.* x

qIter : Nat → Q.ℚᵘ → Q.ℚᵘ
qIter zero x = x
qIter (suc n) x = qSquare (qIter n x)

squareBand : (l u : Q.ℚᵘ) (x : ℝ) → Q.0ℚᵘ Q.≤ l → Band l x u →
  Band (qSquare l) (square x) (qSquare u)
squareBand l u x lNN (hl , hu) =
  let xNN = P.0≤x⇒nonNegx (P.≤-trans (rat≤ Q.0ℚᵘ l lNN) hl)
  in P.≤-respˡ-≃ (P.≃-symm (P.⋆-distrib-* l l))
       (P.*-mono-≤ (nn l lNN) (nn l lNN) hl hl) ,
     P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-* u u))
       (P.*-mono-≤ xNN xNN hu hu)

iterBand : (n : Nat) (l u : Q.ℚᵘ) (x : ℝ) → Q.0ℚᵘ Q.≤ l → Band l x u →
  Band (qIter n l) (iter square n x) (qIter n u)
iterBand zero l u x h b = b
iterBand (suc n) l u x h b = squareBand (qIter n l) (qIter n u) (iter square n x)
  (nonneg n l h) (iterBand n l u x h b)
  where
  nonneg : (j : Nat) (q : Q.ℚᵘ) → Q.0ℚᵘ Q.≤ q → Q.0ℚᵘ Q.≤ qIter j q
  nonneg zero q h = h
  nonneg (suc j) q h = Sq.rationalSquareNonnegative (qIter j q)

exponentRecover : iter double 6 small ≃ G.exponent
exponentRecover = let open P.ℝ-Solver in solve 1 (λ x →
  let a = Κ (+ 1 / 64) ⊗ x
      b = a ⊕ a
      c = b ⊕ b
      d = c ⊕ c
      e = d ⊕ d
      f = e ⊕ e
  in f ⊕ f ⊜ x) P.≃-refl G.exponent

bigExpBand : Band (qIter 6 eL) (E.bishopExp G.exponent) (qIter 6 eU)
bigExpBand =
  let h = iterBand 6 eL eU (E.bishopExp small) (from-yes (Q.0ℚᵘ QP.≤? eL)) expBand
      eq = P.≃-trans (P.≃-symm (expDouble 6 small)) (EG.bishopExpCongruent exponentRecover)
  in P.≤-respʳ-≃ eq (proj₁ h) , P.≤-respˡ-≃ eq (proj₂ h)

-- Clear the reciprocal with positivity; no division by a rounded number.
cancelOrder : (v : ℝ) → R.Positive v → ∀ {a b : ℝ} → v * a ≤ v * b → a ≤ b
cancelOrder v hv h = P.≮⇒≥ (λ ba → P.<-irrefl P.≃-refl
  (P.≤-<-trans h (P.*-monoˡ-<-pos hv ba)))

radiusCross : E.bishopExp G.exponent * CM.radius ≃ R.1ℝ
radiusCross = EC.bishopExpTimesNegativeIsOne G.exponent

radiusBand : Band rL CM.radius rU
radiusBand =
  let v = E.bishopExp G.exponent
      vp = P.0<x⇒posx (Neg.expPositive G.exponentPositive)
      rlNN = nn rL (from-yes (Q.0ℚᵘ QP.≤? rL))
      ruNN = nn rU (from-yes (Q.0ℚᵘ QP.≤? rU))
      lo = qIter 6 eL
      hi = qIter 6 eU
      hL = P.≤-trans (P.*-monoʳ-≤-nonNeg (proj₂ bigExpBand) rlNN)
        (P.≤-respˡ-≃ (P.⋆-distrib-* hi rL)
          (rat≤ (hi Q.* rL) Q.1ℚᵘ (from-yes ((hi Q.* rL) QP.≤? Q.1ℚᵘ))))
      hU = P.≤-trans (P.≤-respʳ-≃ (P.⋆-distrib-* lo rU)
        (rat≤ Q.1ℚᵘ (lo Q.* rU) (from-yes (Q.1ℚᵘ QP.≤? (lo Q.* rU)))))
        (P.*-monoʳ-≤-nonNeg (proj₁ bigExpBand) ruNN)
  in cancelOrder v vp (P.≤-respʳ-≃ (P.≃-symm radiusCross) hL) ,
     cancelOrder v vp (P.≤-respˡ-≃ (P.≃-symm radiusCross) hU)
