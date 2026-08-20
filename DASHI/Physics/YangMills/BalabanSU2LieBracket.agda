module DASHI.Physics.YangMills.BalabanSU2LieBracket where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient; oneCoefficient; interpretCoefficient; zeroCoefficientHomomorphic; oneCoefficientHomomorphic )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( q0R; q1R; q2R; q3R; q0P; q1P; q2P; q3P )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_; _*R_; -R_; zeroR; oneR; _+q_; negQ; _*q_; quaternionExt )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra; su2Lie; su2LieExt; lieQuaternion; lieAdd; lieNegate; lieScale )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using (su2Dot)

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

twoP : ∀ {n} → Polynomial n
twoP = oneP :+ oneP

twoR : ℝ
twoR = oneR +R oneR

bracket1R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket1R y₁ z₁ y₂ z₂ = twoR *R ((y₁ *R z₂) +R (-R (z₁ *R y₂)))

bracket2R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket2R z₁ x₁ z₂ x₂ = twoR *R ((z₁ *R x₂) +R (-R (x₁ *R z₂)))

bracket3R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket3R x₁ y₁ x₂ y₂ = twoR *R ((x₁ *R y₂) +R (-R (y₁ *R x₂)))

bracket1P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket1P y₁ z₁ y₂ z₂ = twoP :* ((y₁ :* z₂) :+ (:- (z₁ :* y₂)))

bracket2P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket2P z₁ x₁ z₂ x₂ = twoP :* ((z₁ :* x₂) :+ (:- (x₁ :* z₂)))

bracket3P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket3P x₁ y₁ x₂ y₂ = twoP :* ((x₁ :* y₂) :+ (:- (y₁ :* x₂)))

dotP : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
dotP x₁ y₁ z₁ x₂ y₂ z₂ = ((x₁ :* x₂) :+ (y₁ :* y₂)) :+ (z₁ :* z₂)

lieBracket : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieBracket (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2Lie (bracket1R y₁ z₁ y₂ z₂) (bracket2R z₁ x₁ z₂ x₂) (bracket3R x₁ y₁ x₂ y₂)

------------------------------------------------------------------------
-- Helper/Shadowed definitions for definitional solver equality
------------------------------------------------------------------------

zeroR' : ℝ
zeroR' = interpretCoefficient zeroCoefficient

oneR' : ℝ
oneR' = interpretCoefficient oneCoefficient

twoR' : ℝ
twoR' = oneR' +R oneR'

bracket1R' : ℝ → ℝ → ℝ → ℝ → ℝ
bracket1R' y₁ z₁ y₂ z₂ = twoR' *R ((y₁ *R z₂) +R (-R (z₁ *R y₂)))

bracket2R' : ℝ → ℝ → ℝ → ℝ → ℝ
bracket2R' z₁ x₁ z₂ x₂ = twoR' *R ((z₁ *R x₂) +R (-R (x₁ *R z₂)))

bracket3R' : ℝ → ℝ → ℝ → ℝ → ℝ
bracket3R' x₁ y₁ x₂ y₂ = twoR' *R ((x₁ *R y₂) +R (-R (y₁ *R x₂)))

lieBracket' : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieBracket' (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2Lie (bracket1R' y₁ z₁ y₂ z₂) (bracket2R' z₁ x₁ z₂ x₂) (bracket3R' x₁ y₁ x₂ y₂)

zeroR-eq : zeroR' ≡ zeroR
zeroR-eq = zeroCoefficientHomomorphic

oneR-eq : oneR' ≡ oneR
oneR-eq = oneCoefficientHomomorphic

twoR-eq : twoR' ≡ twoR
twoR-eq = cong₂ _+R_ oneR-eq oneR-eq

bracket1R-eq : ∀ {y₁ z₁ y₂ z₂} → bracket1R' y₁ z₁ y₂ z₂ ≡ bracket1R y₁ z₁ y₂ z₂
bracket1R-eq rewrite twoR-eq = refl

bracket2R-eq : ∀ {z₁ x₁ z₂ x₂} → bracket2R' z₁ x₁ z₂ x₂ ≡ bracket2R z₁ x₁ z₂ x₂
bracket2R-eq rewrite twoR-eq = refl

bracket3R-eq : ∀ {x₁ y₁ x₂ y₂} → bracket3R' x₁ y₁ x₂ y₂ ≡ bracket3R x₁ y₁ x₂ y₂
bracket3R-eq rewrite twoR-eq = refl

lieBracket-eq : ∀ {X Y} → lieBracket' X Y ≡ lieBracket X Y
lieBracket-eq {su2Lie x₁ y₁ z₁} {su2Lie x₂ y₂ z₂}
  rewrite bracket1R-eq {y₁} {z₁} {y₂} {z₂}
        | bracket2R-eq {z₁} {x₁} {z₂} {x₂}
        | bracket3R-eq {x₁} {y₁} {x₂} {y₂}
        = refl

trans₃ : ∀ {a} {A : Set a} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
trans₃ p q r = trans (trans p q) r

------------------------------------------------------------------------
-- Commutator identities proven on helper definitions
------------------------------------------------------------------------

comm0Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  zeroR' ≡ q0R zeroR' x₁ y₁ z₁ zeroR' x₂ y₂ z₂ +R
    (-R (q0R zeroR' x₂ y₂ z₂ zeroR' x₁ y₁ z₁))
comm0Helper = solveComputed 6
  (λ x₁ y₁ z₁ x₂ y₂ z₂ →
    zeroP := q0P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂ :+ (:- (q0P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁)))
  computed

comm0Polynomial : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  zeroR ≡ q0R zeroR x₁ y₁ z₁ zeroR x₂ y₂ z₂ +R
    (-R (q0R zeroR x₂ y₂ z₂ zeroR x₁ y₁ z₁))
comm0Polynomial x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym zeroR-eq) (comm0Helper x₁ y₁ z₁ x₂ y₂ z₂)
    (cong (λ w → q0R w x₁ y₁ z₁ w x₂ y₂ z₂ +R (-R (q0R w x₂ y₂ z₂ w x₁ y₁ z₁))) zeroR-eq)

comm1Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket1R' y₁ z₁ y₂ z₂ ≡ q1R zeroR' x₁ y₁ z₁ zeroR' x₂ y₂ z₂ +R
    (-R (q1R zeroR' x₂ y₂ z₂ zeroR' x₁ y₁ z₁))
comm1Helper = solveComputed 6
  (λ x₁ y₁ z₁ x₂ y₂ z₂ →
    bracket1P y₁ z₁ y₂ z₂ := q1P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂ :+ (:- (q1P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁)))
  computed

comm1Polynomial : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket1R y₁ z₁ y₂ z₂ ≡ q1R zeroR x₁ y₁ z₁ zeroR x₂ y₂ z₂ +R
    (-R (q1R zeroR x₂ y₂ z₂ zeroR x₁ y₁ z₁))
comm1Polynomial x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket1R-eq) (comm1Helper x₁ y₁ z₁ x₂ y₂ z₂)
    (cong (λ w → q1R w x₁ y₁ z₁ w x₂ y₂ z₂ +R (-R (q1R w x₂ y₂ z₂ w x₁ y₁ z₁))) zeroR-eq)

comm2Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket2R' z₁ x₁ z₂ x₂ ≡ q2R zeroR' x₁ y₁ z₁ zeroR' x₂ y₂ z₂ +R
    (-R (q2R zeroR' x₂ y₂ z₂ zeroR' x₁ y₁ z₁))
comm2Helper = solveComputed 6
  (λ x₁ y₁ z₁ x₂ y₂ z₂ →
    bracket2P z₁ x₁ z₂ x₂ := q2P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂ :+ (:- (q2P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁)))
  computed

comm2Polynomial : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket2R z₁ x₁ z₂ x₂ ≡ q2R zeroR x₁ y₁ z₁ zeroR x₂ y₂ z₂ +R
    (-R (q2R zeroR x₂ y₂ z₂ zeroR x₁ y₁ z₁))
comm2Polynomial x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket2R-eq) (comm2Helper x₁ y₁ z₁ x₂ y₂ z₂)
    (cong (λ w → q2R w x₁ y₁ z₁ w x₂ y₂ z₂ +R (-R (q2R w x₂ y₂ z₂ w x₁ y₁ z₁))) zeroR-eq)

comm3Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket3R' x₁ y₁ x₂ y₂ ≡ q3R zeroR' x₁ y₁ z₁ zeroR' x₂ y₂ z₂ +R
    (-R (q3R zeroR' x₂ y₂ z₂ zeroR' x₁ y₁ z₁))
comm3Helper = solveComputed 6
  (λ x₁ y₁ z₁ x₂ y₂ z₂ →
    bracket3P x₁ y₁ x₂ y₂ := q3P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂ :+ (:- (q3P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁)))
  computed

comm3Polynomial : ∀ x₁ y₁ z₁ x₂ y₂ z₂ →
  bracket3R x₁ y₁ x₂ y₂ ≡ q3R zeroR x₁ y₁ z₁ zeroR x₂ y₂ z₂ +R
    (-R (q3R zeroR x₂ y₂ z₂ zeroR x₁ y₁ z₁))
comm3Polynomial x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket3R-eq) (comm3Helper x₁ y₁ z₁ x₂ y₂ z₂)
    (cong (λ w → q3R w x₁ y₁ z₁ w x₂ y₂ z₂ +R (-R (q3R w x₂ y₂ z₂ w x₁ y₁ z₁))) zeroR-eq)

lieBracketQuaternionCommutator : ∀ X Y →
  lieQuaternion (lieBracket X Y) ≡
  (lieQuaternion X *q lieQuaternion Y) +q negQ (lieQuaternion Y *q lieQuaternion X)
lieBracketQuaternionCommutator (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  quaternionExt
    (comm0Polynomial x₁ y₁ z₁ x₂ y₂ z₂)
    (comm1Polynomial x₁ y₁ z₁ x₂ y₂ z₂)
    (comm2Polynomial x₁ y₁ z₁ x₂ y₂ z₂)
    (comm3Polynomial x₁ y₁ z₁ x₂ y₂ z₂)

------------------------------------------------------------------------
-- Antisymmetry, bilinearity, and Jacobi identities
------------------------------------------------------------------------

anti1Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R' y₁ z₁ y₂ z₂ ≡ -R bracket1R' y₂ z₂ y₁ z₁
anti1Helper = solveComputed 6 (λ x₁ y₁ z₁ x₂ y₂ z₂ → bracket1P y₁ z₁ y₂ z₂ := :- (bracket1P y₂ z₂ y₁ z₁)) computed

anti1 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R y₁ z₁ y₂ z₂ ≡ -R bracket1R y₂ z₂ y₁ z₁
anti1 x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket1R-eq) (anti1Helper x₁ y₁ z₁ x₂ y₂ z₂) (cong -R_ bracket1R-eq)

anti2Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R' z₁ x₁ z₂ x₂ ≡ -R bracket2R' z₂ x₂ z₁ x₁
anti2Helper = solveComputed 6 (λ x₁ y₁ z₁ x₂ y₂ z₂ → bracket2P z₁ x₁ z₂ x₂ := :- (bracket2P z₂ x₂ z₁ x₁)) computed

anti2 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R z₁ x₁ z₂ x₂ ≡ -R bracket2R z₂ x₂ z₁ x₁
anti2 x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket2R-eq) (anti2Helper x₁ y₁ z₁ x₂ y₂ z₂) (cong -R_ bracket2R-eq)

anti3Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R' x₁ y₁ x₂ y₂ ≡ -R bracket3R' x₂ y₂ x₁ y₁
anti3Helper = solveComputed 6 (λ x₁ y₁ z₁ x₂ y₂ z₂ → bracket3P x₁ y₁ x₂ y₂ := :- (bracket3P x₂ y₂ x₁ y₁)) computed

anti3 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R x₁ y₁ x₂ y₂ ≡ -R bracket3R x₂ y₂ x₁ y₁
anti3 x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket3R-eq) (anti3Helper x₁ y₁ z₁ x₂ y₂ z₂) (cong -R_ bracket3R-eq)

lieBracketAntisymmetric : ∀ X Y → lieBracket X Y ≡ lieNegate (lieBracket Y X)
lieBracketAntisymmetric (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt (anti1 x₁ y₁ z₁ x₂ y₂ z₂) (anti2 x₁ y₁ z₁ x₂ y₂ z₂) (anti3 x₁ y₁ z₁ x₂ y₂ z₂)

addLeft1Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R' (y₁ +R y₂) (z₁ +R z₂) y₃ z₃ ≡ bracket1R' y₁ z₁ y₃ z₃ +R bracket1R' y₂ z₂ y₃ z₃
addLeft1Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket1P (y₁ :+ y₂) (z₁ :+ z₂) y₃ z₃ := bracket1P y₁ z₁ y₃ z₃ :+ bracket1P y₂ z₂ y₃ z₃) computed

addLeft1 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R (y₁ +R y₂) (z₁ +R z₂) y₃ z₃ ≡ bracket1R y₁ z₁ y₃ z₃ +R bracket1R y₂ z₂ y₃ z₃
addLeft1 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket1R-eq) (addLeft1Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket1R-eq bracket1R-eq)

addLeft2Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R' (z₁ +R z₂) (x₁ +R x₂) z₃ x₃ ≡ bracket2R' z₁ x₁ z₃ x₃ +R bracket2R' z₂ x₂ z₃ x₃
addLeft2Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket2P (z₁ :+ z₂) (x₁ :+ x₂) z₃ x₃ := bracket2P z₁ x₁ z₃ x₃ :+ bracket2P z₂ x₂ z₃ x₃) computed

addLeft2 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R (z₁ +R z₂) (x₁ +R x₂) z₃ x₃ ≡ bracket2R z₁ x₁ z₃ x₃ +R bracket2R z₂ x₂ z₃ x₃
addLeft2 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket2R-eq) (addLeft2Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket2R-eq bracket2R-eq)

addLeft3Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R' (x₁ +R x₂) (y₁ +R y₂) x₃ y₃ ≡ bracket3R' x₁ y₁ x₃ y₃ +R bracket3R' x₂ y₂ x₃ y₃
addLeft3Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket3P (x₁ :+ x₂) (y₁ :+ y₂) x₃ y₃ := bracket3P x₁ y₁ x₃ y₃ :+ bracket3P x₂ y₂ x₃ y₃) computed

addLeft3 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R (x₁ +R x₂) (y₁ +R y₂) x₃ y₃ ≡ bracket3R x₁ y₁ x₃ y₃ +R bracket3R x₂ y₂ x₃ y₃
addLeft3 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket3R-eq) (addLeft3Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket3R-eq bracket3R-eq)

lieBracketAddLeft : ∀ X Y Z → lieBracket (lieAdd X Y) Z ≡ lieAdd (lieBracket X Z) (lieBracket Y Z)
lieBracketAddLeft (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) (su2Lie x₃ y₃ z₃) =
  su2LieExt (addLeft1 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) (addLeft2 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) (addLeft3 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)

addRight1Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R' y₁ z₁ (y₂ +R y₃) (z₂ +R z₃) ≡ bracket1R' y₁ z₁ y₂ z₂ +R bracket1R' y₁ z₁ y₃ z₃
addRight1Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket1P y₁ z₁ (y₂ :+ y₃) (z₂ :+ z₃) := bracket1P y₁ z₁ y₂ z₂ :+ bracket1P y₁ z₁ y₃ z₃) computed

addRight1 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R y₁ z₁ (y₂ +R y₃) (z₂ +R z₃) ≡ bracket1R y₁ z₁ y₂ z₂ +R bracket1R y₁ z₁ y₃ z₃
addRight1 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket1R-eq) (addRight1Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket1R-eq bracket1R-eq)

addRight2Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R' z₁ x₁ (z₂ +R z₃) (x₂ +R x₃) ≡ bracket2R' z₁ x₁ z₂ x₂ +R bracket2R' z₁ x₁ z₃ x₃
addRight2Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket2P z₁ x₁ (z₂ :+ z₃) (x₂ :+ x₃) := bracket2P z₁ x₁ z₂ x₂ :+ bracket2P z₁ x₁ z₃ x₃) computed

addRight2 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R z₁ x₁ (z₂ +R z₃) (x₂ +R x₃) ≡ bracket2R z₁ x₁ z₂ x₂ +R bracket2R z₁ x₁ z₃ x₃
addRight2 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket2R-eq) (addRight2Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket2R-eq bracket2R-eq)

addRight3Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R' x₁ y₁ (x₂ +R x₃) (y₂ +R y₃) ≡ bracket3R' x₁ y₁ x₂ y₂ +R bracket3R' x₁ y₁ x₃ y₃
addRight3Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket3P x₁ y₁ (x₂ :+ x₃) (y₂ :+ y₃) := bracket3P x₁ y₁ x₂ y₂ :+ bracket3P x₁ y₁ x₃ y₃) computed

addRight3 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R x₁ y₁ (x₂ +R x₃) (y₂ +R y₃) ≡ bracket3R x₁ y₁ x₂ y₂ +R bracket3R x₁ y₁ x₃ y₃
addRight3 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (sym bracket3R-eq) (addRight3Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)
    (cong₂ _+R_ bracket3R-eq bracket3R-eq)

lieBracketAddRight : ∀ X Y Z → lieBracket X (lieAdd Y Z) ≡ lieAdd (lieBracket X Y) (lieBracket X Z)
lieBracketAddRight (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) (su2Lie x₃ y₃ z₃) =
  su2LieExt (addRight1 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) (addRight2 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) (addRight3 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃)

scaleLeft1Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R' (s *R y₁) (s *R z₁) y₂ z₂ ≡ s *R bracket1R' y₁ z₁ y₂ z₂
scaleLeft1Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1P (s :* y₁) (s :* z₁) y₂ z₂ := s :* bracket1P y₁ z₁ y₂ z₂) computed

scaleLeft1 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R (s *R y₁) (s *R z₁) y₂ z₂ ≡ s *R bracket1R y₁ z₁ y₂ z₂
scaleLeft1 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket1R-eq) (scaleLeft1Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket1R-eq)

scaleLeft2Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R' (s *R z₁) (s *R x₁) z₂ x₂ ≡ s *R bracket2R' z₁ x₁ z₂ x₂
scaleLeft2Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2P (s :* z₁) (s :* x₁) z₂ x₂ := s :* bracket2P z₁ x₁ z₂ x₂) computed

scaleLeft2 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R (s *R z₁) (s *R x₁) z₂ x₂ ≡ s *R bracket2R z₁ x₁ z₂ x₂
scaleLeft2 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket2R-eq) (scaleLeft2Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket2R-eq)

scaleLeft3Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R' (s *R x₁) (s *R y₁) x₂ y₂ ≡ s *R bracket3R' x₁ y₁ x₂ y₂
scaleLeft3Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3P (s :* x₁) (s :* y₁) x₂ y₂ := s :* bracket3P x₁ y₁ x₂ y₂) computed

scaleLeft3 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R (s *R x₁) (s *R y₁) x₂ y₂ ≡ s *R bracket3R x₁ y₁ x₂ y₂
scaleLeft3 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket3R-eq) (scaleLeft3Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket3R-eq)

lieBracketScaleLeft : ∀ s X Y → lieBracket (lieScale s X) Y ≡ lieScale s (lieBracket X Y)
lieBracketScaleLeft s (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt (scaleLeft1 s x₁ y₁ z₁ x₂ y₂ z₂) (scaleLeft2 s x₁ y₁ z₁ x₂ y₂ z₂) (scaleLeft3 s x₁ y₁ z₁ x₂ y₂ z₂)

scaleRight1Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R' y₁ z₁ (s *R y₂) (s *R z₂) ≡ s *R bracket1R' y₁ z₁ y₂ z₂
scaleRight1Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1P y₁ z₁ (s :* y₂) (s :* z₂) := s :* bracket1P y₁ z₁ y₂ z₂) computed

scaleRight1 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket1R y₁ z₁ (s *R y₂) (s *R z₂) ≡ s *R bracket1R y₁ z₁ y₂ z₂
scaleRight1 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket1R-eq) (scaleRight1Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket1R-eq)

scaleRight2Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R' z₁ x₁ (s *R z₂) (s *R x₂) ≡ s *R bracket2R' z₁ x₁ z₂ x₂
scaleRight2Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2P z₁ x₁ (s :* z₂) (s :* x₂) := s :* bracket2P z₁ x₁ z₂ x₂) computed

scaleRight2 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket2R z₁ x₁ (s *R z₂) (s *R x₂) ≡ s *R bracket2R z₁ x₁ z₂ x₂
scaleRight2 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket2R-eq) (scaleRight2Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket2R-eq)

scaleRight3Helper : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R' x₁ y₁ (s *R x₂) (s *R y₂) ≡ s *R bracket3R' x₁ y₁ x₂ y₂
scaleRight3Helper = solveComputed 7 (λ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3P x₁ y₁ (s :* x₂) (s :* y₂) := s :* bracket3P x₁ y₁ x₂ y₂) computed

scaleRight3 : ∀ s x₁ y₁ z₁ x₂ y₂ z₂ → bracket3R x₁ y₁ (s *R x₂) (s *R y₂) ≡ s *R bracket3R x₁ y₁ x₂ y₂
scaleRight3 s x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃ (sym bracket3R-eq) (scaleRight3Helper s x₁ y₁ z₁ x₂ y₂ z₂) (cong (s *R_) bracket3R-eq)

lieBracketScaleRight : ∀ s X Y → lieBracket X (lieScale s Y) ≡ lieScale s (lieBracket X Y)
lieBracketScaleRight s (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt (scaleRight1 s x₁ y₁ z₁ x₂ y₂ z₂) (scaleRight2 s x₁ y₁ z₁ x₂ y₂ z₂) (scaleRight3 s x₁ y₁ z₁ x₂ y₂ z₂)

------------------------------------------------------------------------
-- Jacobi and skew-adjoint identities
------------------------------------------------------------------------

LHS1-eq : ∀ {y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃} →
  bracket1R y₁ z₁ (bracket2R z₂ x₂ z₃ x₃) (bracket3R x₂ y₂ x₃ y₃) ≡
  bracket1R' y₁ z₁ (bracket2R' z₂ x₂ z₃ x₃) (bracket3R' x₂ y₂ x₃ y₃)
LHS1-eq =
  trans (sym bracket1R-eq)
    (cong₂ (bracket1R' _ _) (sym bracket2R-eq) (sym bracket3R-eq))

LHS2-eq : ∀ {x₁ y₁ z₁ y₂ z₂ x₃ y₃ z₃} →
  bracket1R y₂ z₂ (bracket2R z₃ x₃ z₁ x₁) (bracket3R x₃ y₃ x₁ y₁) ≡
  bracket1R' y₂ z₂ (bracket2R' z₃ x₃ z₁ x₁) (bracket3R' x₃ y₃ x₁ y₁)
LHS2-eq =
  trans (sym bracket1R-eq)
    (cong₂ (bracket1R' _ _) (sym bracket2R-eq) (sym bracket3R-eq))

LHS3-eq : ∀ {x₁ y₁ z₁ x₂ y₂ z₂ y₃ z₃} →
  bracket1R y₃ z₃ (bracket2R z₁ x₁ z₂ x₂) (bracket3R x₁ y₁ x₂ y₂) ≡
  bracket1R' y₃ z₃ (bracket2R' z₁ x₁ z₂ x₂) (bracket3R' x₁ y₁ x₂ y₂)
LHS3-eq =
  trans (sym bracket1R-eq)
    (cong₂ (bracket1R' _ _) (sym bracket2R-eq) (sym bracket3R-eq))

LHS-eq : ∀ {x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃} →
  bracket1R y₁ z₁ (bracket2R z₂ x₂ z₃ x₃) (bracket3R x₂ y₂ x₃ y₃) +R
  (bracket1R y₂ z₂ (bracket2R z₃ x₃ z₁ x₁) (bracket3R x₃ y₃ x₁ y₁) +R
   bracket1R y₃ z₃ (bracket2R z₁ x₁ z₂ x₂) (bracket3R x₁ y₁ x₂ y₂))
  ≡
  bracket1R' y₁ z₁ (bracket2R' z₂ x₂ z₃ x₃) (bracket3R' x₂ y₂ x₃ y₃) +R
  (bracket1R' y₂ z₂ (bracket2R' z₃ x₃ z₁ x₁) (bracket3R' x₃ y₃ x₁ y₁) +R
   bracket1R' y₃ z₃ (bracket2R' z₁ x₁ z₂ x₂) (bracket3R' x₁ y₁ x₂ y₂))
LHS-eq = cong₂ _+R_ LHS1-eq (cong₂ _+R_ LHS2-eq LHS3-eq)

jacobi1Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R' y₁ z₁ (bracket2R' z₂ x₂ z₃ x₃) (bracket3R' x₂ y₂ x₃ y₃) +R
  (bracket1R' y₂ z₂ (bracket2R' z₃ x₃ z₁ x₁) (bracket3R' x₃ y₃ x₁ y₁) +R
   bracket1R' y₃ z₃ (bracket2R' z₁ x₁ z₂ x₂) (bracket3R' x₁ y₁ x₂ y₂)) ≡ zeroR'
jacobi1Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket1P y₁ z₁ (bracket2P z₂ x₂ z₃ x₃) (bracket3P x₂ y₂ x₃ y₃) :+ (bracket1P y₂ z₂ (bracket2P z₃ x₃ z₁ x₁) (bracket3P x₃ y₃ x₁ y₁) :+ bracket1P y₃ z₃ (bracket2P z₁ x₁ z₂ x₂) (bracket3P x₁ y₁ x₂ y₂)) := zeroP) computed

jacobi1 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket1R y₁ z₁ (bracket2R z₂ x₂ z₃ x₃) (bracket3R x₂ y₂ x₃ y₃) +R
  (bracket1R y₂ z₂ (bracket2R z₃ x₃ z₁ x₁) (bracket3R x₃ y₃ x₁ y₁) +R
   bracket1R y₃ z₃ (bracket2R z₁ x₁ z₂ x₂) (bracket3R x₁ y₁ x₂ y₂)) ≡ zeroR
jacobi1 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ LHS-eq (jacobi1Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) zeroR-eq

LHS21-eq : ∀ {z₁ x₁ x₂ y₂ x₃ y₃ z₂ z₃} →
  bracket2R z₁ x₁ (bracket3R x₂ y₂ x₃ y₃) (bracket1R y₂ z₂ y₃ z₃) ≡
  bracket2R' z₁ x₁ (bracket3R' x₂ y₂ x₃ y₃) (bracket1R' y₂ z₂ y₃ z₃)
LHS21-eq =
  trans (sym bracket2R-eq)
    (cong₂ (bracket2R' _ _) (sym bracket3R-eq) (sym bracket1R-eq))

LHS22-eq : ∀ {z₂ x₂ x₃ y₃ x₁ y₁ z₃ z₁} →
  bracket2R z₂ x₂ (bracket3R x₃ y₃ x₁ y₁) (bracket1R y₃ z₃ y₁ z₁) ≡
  bracket2R' z₂ x₂ (bracket3R' x₃ y₃ x₁ y₁) (bracket1R' y₃ z₃ y₁ z₁)
LHS22-eq =
  trans (sym bracket2R-eq)
    (cong₂ (bracket2R' _ _) (sym bracket3R-eq) (sym bracket1R-eq))

LHS23-eq : ∀ {z₃ x₃ x₁ y₁ x₂ y₂ z₁ z₂} →
  bracket2R z₃ x₃ (bracket3R x₁ y₁ x₂ y₂) (bracket1R y₁ z₁ y₂ z₂) ≡
  bracket2R' z₃ x₃ (bracket3R' x₁ y₁ x₂ y₂) (bracket1R' y₁ z₁ y₂ z₂)
LHS23-eq =
  trans (sym bracket2R-eq)
    (cong₂ (bracket2R' _ _) (sym bracket3R-eq) (sym bracket1R-eq))

LHS2-all-eq : ∀ {x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃} →
  bracket2R z₁ x₁ (bracket3R x₂ y₂ x₃ y₃) (bracket1R y₂ z₂ y₃ z₃) +R
  (bracket2R z₂ x₂ (bracket3R x₃ y₃ x₁ y₁) (bracket1R y₃ z₃ y₁ z₁) +R
   bracket2R z₃ x₃ (bracket3R x₁ y₁ x₂ y₂) (bracket1R y₁ z₁ y₂ z₂))
  ≡
  bracket2R' z₁ x₁ (bracket3R' x₂ y₂ x₃ y₃) (bracket1R' y₂ z₂ y₃ z₃) +R
  (bracket2R' z₂ x₂ (bracket3R' x₃ y₃ x₁ y₁) (bracket1R' y₃ z₃ y₁ z₁) +R
   bracket2R' z₃ x₃ (bracket3R' x₁ y₁ x₂ y₂) (bracket1R' y₁ z₁ y₂ z₂))
LHS2-all-eq = cong₂ _+R_ LHS21-eq (cong₂ _+R_ LHS22-eq LHS23-eq)

jacobi2Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R' z₁ x₁ (bracket3R' x₂ y₂ x₃ y₃) (bracket1R' y₂ z₂ y₃ z₃) +R
  (bracket2R' z₂ x₂ (bracket3R' x₃ y₃ x₁ y₁) (bracket1R' y₃ z₃ y₁ z₁) +R
   bracket2R' z₃ x₃ (bracket3R' x₁ y₁ x₂ y₂) (bracket1R' y₁ z₁ y₂ z₂)) ≡ zeroR'
jacobi2Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket2P z₁ x₁ (bracket3P x₂ y₂ x₃ y₃) (bracket1P y₂ z₂ y₃ z₃) :+ (bracket2P z₂ x₂ (bracket3P x₃ y₃ x₁ y₁) (bracket1P y₃ z₃ y₁ z₁) :+ bracket2P z₃ x₃ (bracket3P x₁ y₁ x₂ y₂) (bracket1P y₁ z₁ y₂ z₂)) := zeroP) computed

jacobi2 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket2R z₁ x₁ (bracket3R x₂ y₂ x₃ y₃) (bracket1R y₂ z₂ y₃ z₃) +R
  (bracket2R z₂ x₂ (bracket3R x₃ y₃ x₁ y₁) (bracket1R y₃ z₃ y₁ z₁) +R
   bracket2R z₃ x₃ (bracket3R x₁ y₁ x₂ y₂) (bracket1R y₁ z₁ y₂ z₂)) ≡ zeroR
jacobi2 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ (LHS2-all-eq) (jacobi2Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) zeroR-eq

LHS31-eq : ∀ {x₁ y₁ y₂ z₂ y₃ z₃ x₂ x₃} →
  bracket3R x₁ y₁ (bracket1R y₂ z₂ y₃ z₃) (bracket2R z₂ x₂ z₃ x₃) ≡
  bracket3R' x₁ y₁ (bracket1R' y₂ z₂ y₃ z₃) (bracket2R' z₂ x₂ z₃ x₃)
LHS31-eq =
  trans (sym bracket3R-eq)
    (cong₂ (bracket3R' _ _) (sym bracket1R-eq) (sym bracket2R-eq))

LHS32-eq : ∀ {x₂ y₂ y₃ z₃ y₁ z₁ x₃ x₁} →
  bracket3R x₂ y₂ (bracket1R y₃ z₃ y₁ z₁) (bracket2R z₃ x₃ z₁ x₁) ≡
  bracket3R' x₂ y₂ (bracket1R' y₃ z₃ y₁ z₁) (bracket2R' z₃ x₃ z₁ x₁)
LHS32-eq =
  trans (sym bracket3R-eq)
    (cong₂ (bracket3R' _ _) (sym bracket1R-eq) (sym bracket2R-eq))

LHS33-eq : ∀ {x₃ y₃ y₁ z₁ y₂ z₂ x₂ x₁} →
  bracket3R x₃ y₃ (bracket1R y₁ z₁ y₂ z₂) (bracket2R z₁ x₁ z₂ x₂) ≡
  bracket3R' x₃ y₃ (bracket1R' y₁ z₁ y₂ z₂) (bracket2R' z₁ x₁ z₂ x₂)
LHS33-eq =
  trans (sym bracket3R-eq)
    (cong₂ (bracket3R' _ _) (sym bracket1R-eq) (sym bracket2R-eq))

LHS3-all-eq : ∀ {x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃} →
  bracket3R x₁ y₁ (bracket1R y₂ z₂ y₃ z₃) (bracket2R z₂ x₂ z₃ x₃) +R
  (bracket3R x₂ y₂ (bracket1R y₃ z₃ y₁ z₁) (bracket2R z₃ x₃ z₁ x₁) +R
   bracket3R x₃ y₃ (bracket1R y₁ z₁ y₂ z₂) (bracket2R z₁ x₁ z₂ x₂))
  ≡
  bracket3R' x₁ y₁ (bracket1R' y₂ z₂ y₃ z₃) (bracket2R' z₂ x₂ z₃ x₃) +R
  (bracket3R' x₂ y₂ (bracket1R' y₃ z₃ y₁ z₁) (bracket2R' z₃ x₃ z₁ x₁) +R
   bracket3R' x₃ y₃ (bracket1R' y₁ z₁ y₂ z₂) (bracket2R' z₁ x₁ z₂ x₂))
LHS3-all-eq = cong₂ _+R_ LHS31-eq (cong₂ _+R_ LHS32-eq LHS33-eq)

jacobi3Helper : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R' x₁ y₁ (bracket1R' y₂ z₂ y₃ z₃) (bracket2R' z₂ x₂ z₃ x₃) +R
  (bracket3R' x₂ y₂ (bracket1R' y₃ z₃ y₁ z₁) (bracket2R' z₃ x₃ z₁ x₁) +R
   bracket3R' x₃ y₃ (bracket1R' y₁ z₁ y₂ z₂) (bracket2R' z₁ x₁ z₂ x₂)) ≡ zeroR'
jacobi3Helper = solveComputed 9 (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ → bracket3P x₁ y₁ (bracket1P y₂ z₂ y₃ z₃) (bracket2P z₂ x₂ z₃ x₃) :+ (bracket3P x₂ y₂ (bracket1P y₃ z₃ y₁ z₁) (bracket2P z₃ x₃ z₁ x₁) :+ bracket3P x₃ y₃ (bracket1P y₁ z₁ y₂ z₂) (bracket2P z₁ x₁ z₂ x₂)) := zeroP) computed

jacobi3 : ∀ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
  bracket3R x₁ y₁ (bracket1R y₂ z₂ y₃ z₃) (bracket2R z₂ x₂ z₃ x₃) +R
  (bracket3R x₂ y₂ (bracket1R y₃ z₃ y₁ z₁) (bracket2R z₃ x₃ z₁ x₁) +R
   bracket3R x₃ y₃ (bracket1R y₁ z₁ y₂ z₂) (bracket2R z₁ x₁ z₂ x₂)) ≡ zeroR
jacobi3 x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
  trans₃ LHS3-all-eq (jacobi3Helper x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃) zeroR-eq

skewHelper : ∀ x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ →
  su2Dot (lieBracket' (su2Lie x₀ y₀ z₀) (su2Lie x₁ y₁ z₁)) (su2Lie x₂ y₂ z₂) ≡
  -R (su2Dot (su2Lie x₁ y₁ z₁) (lieBracket' (su2Lie x₀ y₀ z₀) (su2Lie x₂ y₂ z₂)))
skewHelper = solveComputed 9
  (λ x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ →
    dotP (bracket1P y₀ z₀ y₁ z₁) (bracket2P z₀ x₀ z₁ x₁) (bracket3P x₀ y₀ x₁ y₁) x₂ y₂ z₂ :=
    :- (dotP x₁ y₁ z₁ (bracket1P y₀ z₀ y₂ z₂) (bracket2P z₀ x₀ z₂ x₂) (bracket3P x₀ y₀ x₂ y₂)))
  computed

skewPolynomial : ∀ x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ →
  su2Dot (lieBracket (su2Lie x₀ y₀ z₀) (su2Lie x₁ y₁ z₁)) (su2Lie x₂ y₂ z₂) ≡
  -R (su2Dot (su2Lie x₁ y₁ z₁) (lieBracket (su2Lie x₀ y₀ z₀) (su2Lie x₂ y₂ z₂)))
skewPolynomial x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ =
  trans₃
    (cong₂ su2Dot (sym lieBracket-eq) refl)
    (skewHelper x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂)
    (cong -R_ (cong₂ su2Dot refl lieBracket-eq))

lieBracketSkewAdjoint : ∀ Y X Z → su2Dot (lieBracket Y X) Z ≡ -R (su2Dot X (lieBracket Y Z))
lieBracketSkewAdjoint (su2Lie x₀ y₀ z₀) (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  skewPolynomial x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂

adOperator : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adOperator Y X = lieBracket Y X
