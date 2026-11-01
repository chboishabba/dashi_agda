{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact where

------------------------------------------------------------------------
-- R836 / EXECUTABLE SPARSE 3-4-5 SNAPSHOT AND SUPPORT CLASSIFIERS
--
-- This owner turns the R829 certificate rows into literal modal functions.
-- Velocity is nonzero on six reality-paired seed modes.  Projected forcing is
-- nonzero on the eight active 3-4-5 modes.  Outside those finite supports the
-- functions are definitionally zero.
--
-- Together with R834 this proves that complete R224/R230 output-fibre folds may
-- be reduced exactly to the active cells selected here.  The remaining R829
-- same-object leaf is therefore only:
--
--   Audit.projectedNonlinearity(concrete radius-four system) = forcing345
--
-- on the eight active modes, plus the finite active-cell evaluation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; -_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact as Energy
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse

F : C3.RealField _
F = Rational.rationalRealField

infixr 5 _or_
_or_ : Bool → Bool → Bool
true or b = true
false or b = b

infixr 6 _and_
_and_ : Bool → Bool → Bool
true and b = b
false and b = false

isMode : Z3.FourierMode → Z3.FourierMode → Bool
isMode = Output.modeEqual

velocityActive : Z3.FourierMode → Bool
velocityActive mode =
  isMode mode Active.k₁ or
  (isMode mode Active.k₂ or
  (isMode mode Active.k₄ or
  (isMode mode Active.k₅ or
  (isMode mode Active.k₇ or
   isMode mode Active.k₈))))

forcingActive : Z3.FourierMode → Bool
forcingActive mode =
  isMode mode Active.k₁ or
  (isMode mode Active.k₂ or
  (isMode mode Active.k₃ or
  (isMode mode Active.k₄ or
  (isMode mode Active.k₅ or
  (isMode mode Active.k₆ or
  (isMode mode Active.k₇ or
   isMode mode Active.k₈))))))

chooseVector : Bool → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
chooseVector true yes no = yes
chooseVector false yes no = no

velocityPayload : Z3.FourierMode → C3.Complex3 F
velocityPayload mode =
  chooseVector (isMode mode Active.k₁) Energy.u₁
  (chooseVector (isMode mode Active.k₂) Energy.u₂
  (chooseVector (isMode mode Active.k₄) Energy.u₃
  (chooseVector (isMode mode Active.k₅) Energy.u₄
  (chooseVector (isMode mode Active.k₇) Energy.u₅
  (chooseVector (isMode mode Active.k₈) Energy.u₆
    (C3.complex3Zero F))))))

velocity345 : Z3.FourierMode → C3.Complex3 F
velocity345 mode =
  chooseVector (velocityActive mode)
    (velocityPayload mode)
    (C3.complex3Zero F)

-- Two forcing-only rows omitted from R829C's production table because their
-- velocity is zero.
forcing₃ forcing₆ : C3.Complex3 F
forcing₃ =
  Energy.v 0 (- ((+ 224) / 25))
           0 (- ((+ 168) / 25))
           6 (- 50)
forcing₆ =
  Energy.v 0 ((+ 224) / 25)
           0 ((+ 168) / 25)
           6 50

forcingPayload : Z3.FourierMode → C3.Complex3 F
forcingPayload mode =
  chooseVector (isMode mode Active.k₁) Energy.f₁
  (chooseVector (isMode mode Active.k₂) Energy.f₂
  (chooseVector (isMode mode Active.k₃) forcing₃
  (chooseVector (isMode mode Active.k₄) Energy.f₃
  (chooseVector (isMode mode Active.k₅) Energy.f₄
  (chooseVector (isMode mode Active.k₆) forcing₆
  (chooseVector (isMode mode Active.k₇) Energy.f₅
  (chooseVector (isMode mode Active.k₈) Energy.f₆
    (C3.complex3Zero F))))))))

forcing345 : Z3.FourierMode → C3.Complex3 F
forcing345 mode =
  chooseVector (forcingActive mode)
    (forcingPayload mode)
    (C3.complex3Zero F)

------------------------------------------------------------------------
-- Literal active rows.
------------------------------------------------------------------------

velocity₁ : velocity345 Active.k₁ ≡ Energy.u₁
velocity₁ = refl
velocity₂ : velocity345 Active.k₂ ≡ Energy.u₂
velocity₂ = refl
velocity₃ : velocity345 Active.k₃ ≡ C3.complex3Zero F
velocity₃ = refl
velocity₄ : velocity345 Active.k₄ ≡ Energy.u₃
velocity₄ = refl
velocity₅ : velocity345 Active.k₅ ≡ Energy.u₄
velocity₅ = refl
velocity₆ : velocity345 Active.k₆ ≡ C3.complex3Zero F
velocity₆ = refl
velocity₇ : velocity345 Active.k₇ ≡ Energy.u₅
velocity₇ = refl
velocity₈ : velocity345 Active.k₈ ≡ Energy.u₆
velocity₈ = refl

forcing₁Exact : forcing345 Active.k₁ ≡ Energy.f₁
forcing₁Exact = refl
forcing₂Exact : forcing345 Active.k₂ ≡ Energy.f₂
forcing₂Exact = refl
forcing₃Exact : forcing345 Active.k₃ ≡ forcing₃
forcing₃Exact = refl
forcing₄Exact : forcing345 Active.k₄ ≡ Energy.f₃
forcing₄Exact = refl
forcing₅Exact : forcing345 Active.k₅ ≡ Energy.f₄
forcing₅Exact = refl
forcing₆Exact : forcing345 Active.k₆ ≡ forcing₆
forcing₆Exact = refl
forcing₇Exact : forcing345 Active.k₇ ≡ Energy.f₅
forcing₇Exact = refl
forcing₈Exact : forcing345 Active.k₈ ≡ Energy.f₆
forcing₈Exact = refl

velocityInactiveZero :
  (mode : Z3.FourierMode) →
  velocityActive mode ≡ false →
  velocity345 mode ≡ C3.complex3Zero F
velocityInactiveZero mode inactive rewrite inactive = refl

forcingInactiveZero :
  (mode : Z3.FourierMode) →
  forcingActive mode ≡ false →
  forcing345 mode ≡ C3.complex3Zero F
forcingInactiveZero mode inactive rewrite inactive = refl

------------------------------------------------------------------------
-- Exact cell selectors consumed by R834.
------------------------------------------------------------------------

mixedCellActive : Physical.PhysicalTriadIncidence → Bool
mixedCellActive tau =
  velocityActive (Physical.p tau)
    and velocityActive (Physical.q tau)

commutatorCellActive : Physical.PhysicalTriadIncidence → Bool
commutatorCellActive tau =
  forcingActive (Physical.p tau)
    and velocityActive (Physical.q tau)

mixedInactiveReason :
  (tau : Physical.PhysicalTriadIncidence) →
  mixedCellActive tau ≡ false →
  Sparse.MixedInactiveReason velocity345 tau
mixedInactiveReason tau rejected
  with velocityActive (Physical.p tau)
     | velocityActive (Physical.q tau)
... | true | true with rejected
...   | ()
... | true | false =
  Sparse.mixedQVelocityZero
    (velocityInactiveZero (Physical.q tau) refl)
... | false | q =
  Sparse.mixedPVelocityZero
    (velocityInactiveZero (Physical.p tau) refl)

commutatorInactiveReason :
  (tau : Physical.PhysicalTriadIncidence) →
  commutatorCellActive tau ≡ false →
  Sparse.CommutatorInactiveReason velocity345 forcing345 tau
commutatorInactiveReason tau rejected
  with forcingActive (Physical.p tau)
     | velocityActive (Physical.q tau)
... | true | true with rejected
...   | ()
... | true | false =
  Sparse.commQVelocityZero
    (velocityInactiveZero (Physical.q tau) refl)
... | false | q =
  Sparse.commPForcingZero
    (forcingInactiveZero (Physical.p tau) refl)

pruneMixed345 :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector
    (R224.mixedPlusMinus Active.selected345HelicalScalars velocity345)
    items
  ≡
  R224.foldVector
    (R224.mixedPlusMinus Active.selected345HelicalScalars velocity345)
    (Sparse.filterSelected mixedCellActive items)
pruneMixed345 =
  Sparse.pruneMixedFixedOutput
    Active.selected345HelicalScalars
    velocity345 mixedCellActive mixedInactiveReason

pruneCommutator345 :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector
    (R230.forcingCommutatorCell
      Active.selected345HelicalScalars velocity345 forcing345)
    items
  ≡
  R224.foldVector
    (R230.forcingCommutatorCell
      Active.selected345HelicalScalars velocity345 forcing345)
    (Sparse.filterSelected commutatorCellActive items)
pruneCommutator345 =
  Sparse.pruneCommutatorFixedOutput
    Active.selected345HelicalScalars
    velocity345 forcing345
    commutatorCellActive commutatorInactiveReason

round836SparseVelocityExecutable : Bool
round836SparseVelocityExecutable = true

round836SparseForcingExecutable : Bool
round836SparseForcingExecutable = true

round836MixedCompleteFibrePrunesExactly : Bool
round836MixedCompleteFibrePrunesExactly = true

round836CommutatorCompleteFibrePrunesExactly : Bool
round836CommutatorCompleteFibrePrunesExactly = true

round836ProjectedNonlinearitySameObjectClosed : Bool
round836ProjectedNonlinearitySameObjectClosed = false

round836ActiveCellRepositoryEvaluationClosed : Bool
round836ActiveCellRepositoryEvaluationClosed = false

round836ClayPromotion : Bool
round836ClayPromotion = false

round836MixedCompleteFibrePrunesExactlyIsTrue :
  round836MixedCompleteFibrePrunesExactly ≡ true
round836MixedCompleteFibrePrunesExactlyIsTrue = refl
