module DASHI.Core.ApproximateIntertwinerCompositionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact intertwiners compose for free; approximate ones need an error theorem.
-- This module proves the reusable two-stage bound used by causal abstraction,
-- multi-fidelity transitions and aggregation: if each diagram commutes within
-- epsilon and the downstream coarse map is nonexpansive, the composite defect
-- is bounded by the sum of the two stage defects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties as NatP using (≤-trans; +-mono-≤)

record NatDistance (X : Set) : Set₁ where
  constructor natDistance
  field
    distance : X → X → Nat
    triangle :
      ∀ x y z →
      distance x z ≤ distance x y + distance y z

open NatDistance public

record Nonexpansive
    {X Y : Set}
    (dX : NatDistance X)
    (dY : NatDistance Y)
    (map : X → Y) : Set where
  constructor nonexpansive
  field
    doesNotExpand :
      ∀ {x y budget} →
      distance dX x y ≤ budget →
      distance dY (map x) (map y) ≤ budget

open Nonexpansive public

record ApproximateIntertwiner
    {FineIn FineOut CoarseIn CoarseOut : Set}
    (dOut : NatDistance CoarseOut)
    (projectIn : FineIn → CoarseIn)
    (projectOut : FineOut → CoarseOut)
    (fineMap : FineIn → FineOut)
    (coarseMap : CoarseIn → CoarseOut)
    (epsilon : Nat) : Set where
  constructor approximateIntertwiner
  field
    defectBound :
      ∀ fine →
      distance dOut
        (projectOut (fineMap fine))
        (coarseMap (projectIn fine))
      ≤ epsilon

open ApproximateIntertwiner public

composeApproximateIntertwiners :
  ∀ {A B C A' B' C'}
    {dB : NatDistance B'}
    {dC : NatDistance C'}
    {qA : A → A'} {qB : B → B'} {qC : C → C'}
    {f : A → B} {h : B → C}
    {g : A' → B'} {k : B' → C'}
    {epsilon1 epsilon2 : Nat} →
  ApproximateIntertwiner dB qA qB f g epsilon1 →
  ApproximateIntertwiner dC qB qC h k epsilon2 →
  Nonexpansive dB dC k →
  ApproximateIntertwiner
    dC qA qC
    (λ a → h (f a))
    (λ a' → k (g a'))
    (epsilon2 + epsilon1)
composeApproximateIntertwiners first second kNonexpansive =
  approximateIntertwiner compositeBound
  where
    compositeBound :
      ∀ a →
      distance dC
        (qC (h (f a)))
        (k (g (qA a)))
      ≤ epsilon2 + epsilon1
    compositeBound a =
      NatP.≤-trans
        (triangle dC
          (qC (h (f a)))
          (k (qB (f a)))
          (k (g (qA a))))
        (NatP.+-mono-≤
          (defectBound second (f a))
          (doesNotExpand kNonexpansive (defectBound first a)))

record ApproximateIntertwinerBoundary : Set where
  constructor approximateIntertwinerBoundary
  field
    approximateCommutationNeedsDeclaredMetric : Bool
    stageErrorsComposeByAProvedRule : Bool
    downstreamExpansionControlIsNeededForThisBound : Bool
    exactIntertwiningIsTheZeroDefectSpecialCaseConceptually : Bool

canonicalApproximateIntertwinerBoundary : ApproximateIntertwinerBoundary
canonicalApproximateIntertwinerBoundary =
  approximateIntertwinerBoundary true true true true
