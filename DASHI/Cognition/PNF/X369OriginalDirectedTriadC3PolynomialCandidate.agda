module DASHI.Cognition.PNF.X369OriginalDirectedTriadC3PolynomialCandidate where

-- Original X369 F3 exact directed three-channel router identity.
-- Source semantics: LeechTransformer/models/trialectic_wave_prior.py
-- trialectic_router_invariants / directed_trialectic_invariants.
--
-- This is a PROPOSED ℤ polynomial lemma implementation for Agda 2.9.
-- NOT YET included in the 8-target accepted Track B leaf suite.
-- The source uses the Agda stdlib integer ring solver, without postulates.
-- A successful kernel check is needed before any proof-closure claim.
-- The integer polynomial result reflects the real polynomial identity;
-- formal same-object real/float consumer transport is STILL OPEN.
--
-- No claim that original trained model learned a C3 task mechanism.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; _+_; _*_; _-_)
-- Use the typed non-reflective integer polynomial AST, as in the
-- repository's RiemannWeilPairKernelFrobeniusExact. The tactic
-- solve-∀ reifies Expr variables and cannot call ℤ-valued helpers.
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

square : ℤ → ℤ
square x = x * x

qTriad : ℤ → ℤ → ℤ → ℤ
qTriad a b c =
  ((a * a + b * b + c * c) - a * b) - b * c - c * a

rawTriadRotation : ∀ (a b c : ℤ) →
  (b - a) * (b - a) + (c - b) * (c - b) + (a - c) * (a - c)
  ≡ ((+ 2) * (((a * a + b * b + c * c) - a * b) - b * c - c * a))
rawTriadRotation a b c =
  solve 3
    (λ a b c →
      ((((b :- a) :* (b :- a)) :+ ((c :- b) :* (c :- b))) :+ ((a :- c) :* (a :- c)))
      := (con (+ 2) :* ((((((a :* a) :+ (b :* b)) :+ (c :* c)) :- (a :* b)) :- (b :* c)) :- (c :* a))))
    refl a b c

-- This is the original coherent R+ = (b,c,a) squared source
-- displacement. The R- = (c,a,b) action has the same displacement.
originalTriadRotationSquaredDisplacementEqualsTwoQ :
  ∀ (a b c : ℤ) →
  square (b - a) + square (c - b) + square (a - c)
  ≡ ((+ 2) * qTriad a b c)
originalTriadRotationSquaredDisplacementEqualsTwoQ = rawTriadRotation

rawTriadInverseRotation : ∀ (a b c : ℤ) →
  (c - a) * (c - a) + (a - b) * (a - b) + (b - c) * (b - c)
  ≡ ((+ 2) * (((a * a + b * b + c * c) - a * b) - b * c - c * a))
rawTriadInverseRotation a b c =
  solve 3
    (λ a b c →
      ((((c :- a) :* (c :- a)) :+ ((a :- b) :* (a :- b))) :+ ((b :- c) :* (b :- c)))
      := (con (+ 2) :* ((((((a :* a) :+ (b :* b)) :+ (c :* c)) :- (a :* b)) :- (b :* c)) :- (c :* a))))
    refl a b c

originalTriadInverseRotationSquaredDisplacementEqualsTwoQ :
  ∀ (a b c : ℤ) →
  square (c - a) + square (a - b) + square (b - c)
  ≡ ((+ 2) * qTriad a b c)
originalTriadInverseRotationSquaredDisplacementEqualsTwoQ = rawTriadInverseRotation

-- Original directed triple T(x,h)=(self,cyclic,anticyclic).
-- For x=(a,b,c), h=(A,B,C), these are exact original coordinates,
-- not an independently invented C3 phase/synthetic representation.
originalSelf : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
originalSelf a b c A B C = a * A + b * B + c * C

originalCyclic : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
originalCyclic a b c A B C = a * B + b * C + c * A

originalAnticyclic : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
originalAnticyclic a b c A B C = a * C + b * A + c * B

-- After R+: (self,cyclic,anticyclic) maps
-- (self,cyclic,anticyclic) -> (anticyclic,self,cyclic).
-- After R-: -> (cyclic,anticyclic,self).
originalPlusDirectedDisplacementSquared :
  ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
originalPlusDirectedDisplacementSquared a b c A B C =
  let s = originalSelf a b c A B C
      f = originalCyclic a b c A B C
      r = originalAnticyclic a b c A B C
  in square (r - s) + square (s - f) + square (f - r)

originalMinusDirectedDisplacementSquared :
  ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
originalMinusDirectedDisplacementSquared a b c A B C =
  let s = originalSelf a b c A B C
      f = originalCyclic a b c A B C
      r = originalAnticyclic a b c A B C
  in square (f - s) + square (r - f) + square (s - r)

rawPlusFactors : ∀ (a b c A B C : ℤ) →
  ((a * C + b * A + c * B) - (a * A + b * B + c * C)) * ((a * C + b * A + c * B) - (a * A + b * B + c * C)) +
  ((a * A + b * B + c * C) - (a * B + b * C + c * A)) * ((a * A + b * B + c * C) - (a * B + b * C + c * A)) +
  ((a * B + b * C + c * A) - (a * C + b * A + c * B)) * ((a * B + b * C + c * A) - (a * C + b * A + c * B))
  ≡ (+ 2) * (((a * a + b * b + c * c) - a * b) - b * c - c * a) * (((A * A + B * B + C * C) - A * B) - B * C - C * A)
rawPlusFactors a b c A B C =
  solve 6
    (λ a b c A B C →
      (((((((a :* C) :+ (b :* A)) :+ (c :* B)) :- (((a :* A) :+ (b :* B)) :+ (c :* C))) :* ((((a :* C) :+ (b :* A)) :+ (c :* B)) :- (((a :* A) :+ (b :* B)) :+ (c :* C)))) :+ (((((a :* A) :+ (b :* B)) :+ (c :* C)) :- (((a :* B) :+ (b :* C)) :+ (c :* A))) :* ((((a :* A) :+ (b :* B)) :+ (c :* C)) :- (((a :* B) :+ (b :* C)) :+ (c :* A))))) :+ (((((a :* B) :+ (b :* C)) :+ (c :* A)) :- (((a :* C) :+ (b :* A)) :+ (c :* B))) :* ((((a :* B) :+ (b :* C)) :+ (c :* A)) :- (((a :* C) :+ (b :* A)) :+ (c :* B)))))
      := ((con (+ 2) :* ((((((a :* a) :+ (b :* b)) :+ (c :* c)) :- (a :* b)) :- (b :* c)) :- (c :* a))) :* ((((((A :* A) :+ (B :* B)) :+ (C :* C)) :- (A :* B)) :- (B :* C)) :- (C :* A))))
    refl a b c A B C

originalDirectedTriadC3DisplacementSquaredFactors :
  ∀ (a b c A B C : ℤ) →
  originalPlusDirectedDisplacementSquared a b c A B C
  ≡ (+ 2) * qTriad a b c * qTriad A B C
originalDirectedTriadC3DisplacementSquaredFactors = rawPlusFactors

rawMinusFactors : ∀ (a b c A B C : ℤ) →
  ((a * B + b * C + c * A) - (a * A + b * B + c * C)) * ((a * B + b * C + c * A) - (a * A + b * B + c * C)) +
  ((a * C + b * A + c * B) - (a * B + b * C + c * A)) * ((a * C + b * A + c * B) - (a * B + b * C + c * A)) +
  ((a * A + b * B + c * C) - (a * C + b * A + c * B)) * ((a * A + b * B + c * C) - (a * C + b * A + c * B))
  ≡ (+ 2) * (((a * a + b * b + c * c) - a * b) - b * c - c * a) * (((A * A + B * B + C * C) - A * B) - B * C - C * A)
rawMinusFactors a b c A B C =
  solve 6
    (λ a b c A B C →
      (((((((a :* B) :+ (b :* C)) :+ (c :* A)) :- (((a :* A) :+ (b :* B)) :+ (c :* C))) :* ((((a :* B) :+ (b :* C)) :+ (c :* A)) :- (((a :* A) :+ (b :* B)) :+ (c :* C)))) :+ (((((a :* C) :+ (b :* A)) :+ (c :* B)) :- (((a :* B) :+ (b :* C)) :+ (c :* A))) :* ((((a :* C) :+ (b :* A)) :+ (c :* B)) :- (((a :* B) :+ (b :* C)) :+ (c :* A))))) :+ (((((a :* A) :+ (b :* B)) :+ (c :* C)) :- (((a :* C) :+ (b :* A)) :+ (c :* B))) :* ((((a :* A) :+ (b :* B)) :+ (c :* C)) :- (((a :* C) :+ (b :* A)) :+ (c :* B)))))
      := ((con (+ 2) :* ((((((a :* a) :+ (b :* b)) :+ (c :* c)) :- (a :* b)) :- (b :* c)) :- (c :* a))) :* ((((((A :* A) :+ (B :* B)) :+ (C :* C)) :- (A :* B)) :- (B :* C)) :- (C :* A))))
    refl a b c A B C

originalDirectedInverseC3DisplacementSquaredFactors :
  ∀ (a b c A B C : ℤ) →
  originalMinusDirectedDisplacementSquared a b c A B C
  ≡ (+ 2) * qTriad a b c * qTriad A B C
originalDirectedInverseC3DisplacementSquaredFactors = rawMinusFactors

-- The exact first new source-level group-agnostic equality needed
-- for a mixed ±C3 negative control, not a semantic phase theorem.
originalDirectedTriadMixedOrientationEnergyEqualsCoherent :
  ∀ (a b c A B C : ℤ) →
  originalMinusDirectedDisplacementSquared a b c A B C
  ≡ originalPlusDirectedDisplacementSquared a b c A B C
originalDirectedTriadMixedOrientationEnergyEqualsCoherent a b c A B C =
  trans
    (originalDirectedInverseC3DisplacementSquaredFactors a b c A B C)
    (sym (originalDirectedTriadC3DisplacementSquaredFactors a b c A B C))

data OriginalMixedOrientation : Set where
  originalForward : OriginalMixedOrientation
  originalReverse : OriginalMixedOrientation

record OriginalExpertTriad : Set where
  constructor originalExpertTriad
  field
    originalX0 : ℤ
    originalX1 : ℤ
    originalX2 : ℤ
    originalH0 : ℤ
    originalH1 : ℤ
    originalH2 : ℤ

open OriginalExpertTriad public

originalBlockCoherent : OriginalExpertTriad → ℤ
originalBlockCoherent (originalExpertTriad a b c A B C) =
  originalPlusDirectedDisplacementSquared a b c A B C

originalBlockMixed :
  OriginalMixedOrientation → OriginalExpertTriad → ℤ
originalBlockMixed originalForward block = originalBlockCoherent block
originalBlockMixed originalReverse
  (originalExpertTriad a b c A B C) =
  originalMinusDirectedDisplacementSquared a b c A B C

originalBlockMixedEqualsCoherent :
  (orientation : OriginalMixedOrientation) →
  (block : OriginalExpertTriad) →
  originalBlockMixed orientation block ≡ originalBlockCoherent block
originalBlockMixedEqualsCoherent originalForward block = refl
originalBlockMixedEqualsCoherent originalReverse
  (originalExpertTriad a b c A B C) =
  originalDirectedTriadMixedOrientationEnergyEqualsCoherent a b c A B C

-- An arbitrary length list of original triads and their original
-- per-expert history coordinates. All oriented blocks are used once.
originalMixedBlockEnergy :
  List (OriginalMixedOrientation × OriginalExpertTriad) → ℤ
originalMixedBlockEnergy [] = (+ 0)
originalMixedBlockEnergy ((orientation , block) ∷ rest) =
  originalBlockMixed orientation block + originalMixedBlockEnergy rest

originalCoherentBlockEnergy :
  List (OriginalMixedOrientation × OriginalExpertTriad) → ℤ
originalCoherentBlockEnergy [] = (+ 0)
originalCoherentBlockEnergy ((_ , block) ∷ rest) =
  originalBlockCoherent block + originalCoherentBlockEnergy rest

-- Structural induction, not finite enumeration of 2^128 masks.
-- Includes arbitrary per-expert histories with independent C3 +/- masks.
originalMixedTriadC3RouterFeatureEnergyEqualsCoherent :
  (blocks : List (OriginalMixedOrientation × OriginalExpertTriad)) →
  originalMixedBlockEnergy blocks ≡ originalCoherentBlockEnergy blocks
originalMixedTriadC3RouterFeatureEnergyEqualsCoherent [] = refl
originalMixedTriadC3RouterFeatureEnergyEqualsCoherent
  ((orientation , block) ∷ rest)
  rewrite originalBlockMixedEqualsCoherent orientation block
        | originalMixedTriadC3RouterFeatureEnergyEqualsCoherent rest = refl

-- The source's unary C3 invariant features have zero displacement,
-- but neural real values, original trained logits, F3 CE and task
-- semantic actions are intentionally outside this ℤ proof target.
