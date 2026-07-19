module DASHI.Physics.YangMills.BalabanRandomWalkTerm where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore public using
  (Walk; emptyWalk; _then_; walkLength)

record RandomWalkTerm (Step Scalar : Set) : Set₁ where
  field
    stepWeight : Step → Scalar
    one : Scalar
    multiply : Scalar → Scalar → Scalar

open RandomWalkTerm public

walkWeight :
  ∀ {Step Scalar} → RandomWalkTerm Step Scalar → Walk Step → Scalar
walkWeight bundle emptyWalk = one bundle
walkWeight bundle (step then rest) =
  multiply bundle (stepWeight bundle step) (walkWeight bundle rest)
