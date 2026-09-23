{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact where

------------------------------------------------------------------------
-- ROUND606 / R567 FORCING FULL = SELF + EXTERNAL NETWORK FULL
--
-- R605 proves the literal R230 mixed-helicity product-rule forcing splits
-- pointwise into selected-triad self forcing plus external-network forcing.
--
-- R382/R388 identify the forcing used by the literal double-mixed Gram carrier
-- definitionally with that same R230 product-rule forcing.  Therefore the
-- doubleForcing cell itself splits after pairing tau with swap(tau).
--
-- R567's forcingPair is linear in doubleForcing through the real Hermitian
-- cross.  This module pushes the owner split through that scalar and then over
-- the complete fixed-output full square:
--
--   ForcingFull = SelfForcingFull + ExternalForcingFull.
--
-- No energy-conservation claim or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605

F : C3.RealField _
F = Rational.rationalRealField

doublePlusAdd :
  (left right : C3.Complex3 F) →
  R387.doublePlus (C3.complex3Add left right)
  ≡ C3.complex3Add (R387.doublePlus left) (R387.doublePlus right)
doublePlusAdd
    (C3.complex3 lx ly lz)
    (C3.complex3 rx ry rz) =
  Field.complex3Ext
    (complexCoord lx rx)
    (complexCoord ly ry)
    (complexCoord lz rz)
  where
  complexCoord :
    (left right : C3.Complex F) →
    C3.complexAdd
      (C3.complexAdd left right)
      (C3.complexAdd left right)
    ≡
    C3.complexAdd
      (C3.complexAdd left left)
      (C3.complexAdd right right)
  complexCoord
      (C3.complex lr li)
      (C3.complex rr ri) =
    Field.complexExt
      (R.solve 2
        (λ l r → ((l R.⊕ r) R.⊕ (l R.⊕ r))
          R.⊜ ((l R.⊕ l) R.⊕ (r R.⊕ r)))
        refl lr rr)
      (R.solve 2
        (λ l r → ((l R.⊕ r) R.⊕ (l R.⊕ r))
          R.⊜ ((l R.⊕ l) R.⊕ (r R.⊕ r)))
        refl li ri)
    where module R = Ring.Solver F

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Net = R605.FixedSystem physicalSystem S
  module C = R567.CommutatorOnly physicalSystem S

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  selfDoubleForcing :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfDoubleForcing tau =
    C3.complex3Add
      (R387.doublePlus (Net.selfProductRuleCell tau))
      (R387.doublePlus
        (Net.selfProductRuleCell (Symmetry.swapTriad tau)))

  externalDoubleForcing :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalDoubleForcing tau =
    C3.complex3Add
      (R387.doublePlus (Net.externalProductRuleCell tau))
      (R387.doublePlus
        (Net.externalProductRuleCell (Symmetry.swapTriad tau)))

  doubleForcingSplitsSelfExternal :
    (tau : Physical.PhysicalTriadIncidence) →
    D.doubleForcing tau
    ≡ C3.complex3Add
        (selfDoubleForcing tau)
        (externalDoubleForcing tau)
  doubleForcingSplitsSelfExternal tau =
    let
      atTau = Net.fullProductRuleCellSplitsSelfExternal tau
      atSwap =
        Net.fullProductRuleCellSplitsSelfExternal
          (Symmetry.swapTriad tau)
    in
    trans
      (cong₂ C3.complex3Add
        (cong R387.doublePlus atTau)
        (cong R387.doublePlus atSwap))
      (trans
        (cong₂ C3.complex3Add
          (doublePlusAdd
            (Net.selfProductRuleCell tau)
            (Net.externalProductRuleCell tau))
          (doublePlusAdd
            (Net.selfProductRuleCell (Symmetry.swapTriad tau))
            (Net.externalProductRuleCell (Symmetry.swapTriad tau))))
        (regroup
          (R387.doublePlus (Net.selfProductRuleCell tau))
          (R387.doublePlus (Net.externalProductRuleCell tau))
          (R387.doublePlus
            (Net.selfProductRuleCell (Symmetry.swapTriad tau)))
          (R387.doublePlus
            (Net.externalProductRuleCell (Symmetry.swapTriad tau)))))
    where
    regroup :
      (a b c d : C3.Complex3 F) →
      C3.complex3Add
        (C3.complex3Add a b)
        (C3.complex3Add c d)
      ≡
      C3.complex3Add
        (C3.complex3Add a c)
        (C3.complex3Add b d)
    regroup
        (C3.complex3 ax ay az)
        (C3.complex3 bx by bz)
        (C3.complex3 cx cy cz)
        (C3.complex3 dx dy dz) =
      Field.complex3Ext
        (coord ax bx cx dx)
        (coord ay by cy dy)
        (coord az bz cz dz)
      where
      coord :
        (a b c d : C3.Complex F) →
        C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d)
        ≡ C3.complexAdd (C3.complexAdd a c) (C3.complexAdd b d)
      coord
          (C3.complex ar ai)
          (C3.complex br bi)
          (C3.complex cr ci)
          (C3.complex dr di) =
        Field.complexExt
          (R.solve 4
            (λ a b c d →
              ((a R.⊕ b) R.⊕ (c R.⊕ d))
              R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d)))
            refl ar br cr dr)
          (R.solve 4
            (λ a b c d →
              ((a R.⊕ b) R.⊕ (c R.⊕ d))
              R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d)))
            refl ai bi ci di)
        where module R = Ring.Solver F

  selfForcingPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  selfForcingPair alpha beta =
    C.T.Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (selfDoubleForcing alpha)
          (C.Row.doubleCell beta)

  externalForcingPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  externalForcingPair alpha beta =
    C.T.Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (externalDoubleForcing alpha)
          (C.Row.doubleCell beta)

  forcingPairSplitsSelfExternal :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    C.T.forcingPair alpha beta
    ≡ selfForcingPair alpha beta + externalForcingPair alpha beta
  forcingPairSplitsSelfExternal alpha beta =
    trans
      (C.T.forcingPairScalarized alpha beta)
      (trans
        (cong
          (C.T.Swap.pairResolvent alpha beta *_)
          (trans
            (cong
              (λ selected →
                R179.realHermitianCross selected
                  (C.Row.doubleCell beta))
              (doubleForcingSplitsSelfExternal alpha))
            (R291.realCrossAddLeft
              (selfDoubleForcing alpha)
              (externalDoubleForcing alpha)
              (C.Row.doubleCell beta))))
        (solve
          ( C.T.Swap.pairResolvent alpha beta
          ∷ R179.realHermitianCross
              (selfDoubleForcing alpha) (C.Row.doubleCell beta)
          ∷ R179.realHermitianCross
              (externalDoubleForcing alpha) (C.Row.doubleCell beta)
          ∷ [])))

  fullSquarePointwiseAdd :
    (items : List Physical.PhysicalTriadIncidence) →
    R543.fullSquareSum C.T.forcingPair items
    ≡
    R543.fullSquareSum selfForcingPair items
      + R543.fullSquareSum externalForcingPair items
  fullSquarePointwiseAdd [] = refl
  fullSquarePointwiseAdd (alpha ∷ rest)
    rewrite forcingPairSplitsSelfExternal alpha alpha
          | rowAdd alpha rest
          | columnAdd rest alpha
          | fullSquarePointwiseAdd rest =
    solve
      ( selfForcingPair alpha alpha
      ∷ externalForcingPair alpha alpha
      ∷ R539.rowSum selfForcingPair alpha rest
      ∷ R539.rowSum externalForcingPair alpha rest
      ∷ R539.columnSum selfForcingPair rest alpha
      ∷ R539.columnSum externalForcingPair rest alpha
      ∷ R543.fullSquareSum selfForcingPair rest
      ∷ R543.fullSquareSum externalForcingPair rest
      ∷ [])
    where
    rowAdd :
      (selected : Physical.PhysicalTriadIncidence) →
      (items : List Physical.PhysicalTriadIncidence) →
      R539.rowSum C.T.forcingPair selected items
      ≡
      R539.rowSum selfForcingPair selected items
        + R539.rowSum externalForcingPair selected items
    rowAdd selected [] = refl
    rowAdd selected (beta ∷ tail)
      rewrite forcingPairSplitsSelfExternal selected beta
            | rowAdd selected tail =
      solve
        ( selfForcingPair selected beta
        ∷ externalForcingPair selected beta
        ∷ R539.rowSum selfForcingPair selected tail
        ∷ R539.rowSum externalForcingPair selected tail
        ∷ [])

    columnAdd :
      (items : List Physical.PhysicalTriadIncidence) →
      (selected : Physical.PhysicalTriadIncidence) →
      R539.columnSum C.T.forcingPair items selected
      ≡
      R539.columnSum selfForcingPair items selected
        + R539.columnSum externalForcingPair items selected
    columnAdd [] selected = refl
    columnAdd (alpha ∷ tail) selected
      rewrite forcingPairSplitsSelfExternal alpha selected
            | columnAdd tail selected =
      solve
        ( selfForcingPair alpha selected
        ∷ externalForcingPair alpha selected
        ∷ R539.columnSum selfForcingPair tail selected
        ∷ R539.columnSum externalForcingPair tail selected
        ∷ [])

  forcingFull : ℚ
  forcingFull = R543.fullSquareSum C.T.forcingPair fibre

  selfForcingFull : ℚ
  selfForcingFull = R543.fullSquareSum selfForcingPair fibre

  externalForcingFull : ℚ
  externalForcingFull = R543.fullSquareSum externalForcingPair fibre

  forcingFullSplitsSelfExternal :
    forcingFull ≡ selfForcingFull + externalForcingFull
  forcingFullSplitsSelfExternal = fullSquarePointwiseAdd fibre

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round606DoubleForcingSelfExternalSplitClosed : Bool
round606DoubleForcingSelfExternalSplitClosed = true

round606ForcingPairSelfExternalSplitClosed : Bool
round606ForcingPairSelfExternalSplitClosed = true

round606ForcingFullSelfExternalSplitClosed : Bool
round606ForcingFullSelfExternalSplitClosed = true

round606IntroducesEstimate : Bool
round606IntroducesEstimate = false

round606SelfForcingFullPaysA3 : Bool
round606SelfForcingFullPaysA3 = false

round606ExternalForcingFullPaid : Bool
round606ExternalForcingFullPaid = false

round606ForcingFullSelfExternalSplitClosedIsTrue :
  round606ForcingFullSelfExternalSplitClosed ≡ true
round606ForcingFullSelfExternalSplitClosedIsTrue = refl

round606IntroducesEstimateIsFalse :
  round606IntroducesEstimate ≡ false
round606IntroducesEstimateIsFalse = refl

round606SelfForcingFullPaysA3IsFalse :
  round606SelfForcingFullPaysA3 ≡ false
round606SelfForcingFullPaysA3IsFalse = refl

round606ExternalForcingFullPaidIsFalse :
  round606ExternalForcingFullPaid ≡ false
round606ExternalForcingFullPaidIsFalse = refl
