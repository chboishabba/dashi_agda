{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119WilsonCoefficientF2SecondJetExact where

------------------------------------------------------------------------
-- FINITE WILSON INSERTION -> DISCRETE F^2, EXACTLY AT SECOND JET.
--
-- The Eq.(2.23) Wilson-coefficient direction is the literal Wilson action.
-- Independently, the side-four SU(2) finite action has already been evaluated
-- on exact second jets, and every plaquette second variation is the squared
-- forward-difference curl.  Composing those results identifies the FINITE
-- Wilson insertion's quadratic/short-distance coordinate with the literal
-- discrete curvature-square fold.
--
-- No continuum/OPE/anomaly identification occurs here.  After this theorem the
-- surviving F^2 work is specifically the renormalized marked-source completion
-- of this already-identified finite Wilson/curvature coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact as Tangent
import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact as Lift
import DASHI.Physics.YangMills.BalabanSU2SecondJetSUNInstanceExact as Jet
import DASHI.Physics.YangMills.BalabanSU2WilsonActionSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33IdentityCurvatureLocalExact as P33
import DASHI.Physics.Foundations.CMP119Eq223WilsonCoefficientDirectionExact as Eq223

finiteWilsonSecondJetIsDiscreteF2 :
  ∀ tangent →
  Jet.scalarSecondDerivative (Wilson.physicalJetWilsonAction tangent)
  ≡ Lift.literalDiscreteCurlEnergy tangent
finiteWilsonSecondJetIsDiscreteF2 tangent =
  trans
    (Wilson.genericSUNWilsonActionSecondVariationEqualsLiteralFold tangent)
    (P33.identityCurvatureMatchesLiteralWilsonAndCurl tangent)

-- The coefficient-direction theorem and the second-jet identity are independent
-- pieces: the first fixes WHICH finite insertion is produced by Eq.(2.23), while
-- the theorem above fixes its exact quadratic curvature meaning.
eq223FiniteInsertionIsWilson : Bool
eq223FiniteInsertionIsWilson = Eq223.finiteWilsonInsertionNoLongerSemanticDebt

finiteWilsonInsertionHasExactDiscreteF2SecondJet : Bool
finiteWilsonInsertionHasExactDiscreteF2SecondJet = true

remainingF2DebtIsRenormalizedCompletionNotFiniteIdentification : Bool
remainingF2DebtIsRenormalizedCompletionNotFiniteIdentification = true
