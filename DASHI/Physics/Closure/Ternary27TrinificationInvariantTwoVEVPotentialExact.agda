module DASHI.Physics.Closure.Ternary27TrinificationInvariantTwoVEVPotentialExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact as Breaking
import DASHI.Physics.Closure.Ternary27TrinificationTwoVEVMassSpectrumExact as Mass

------------------------------------------------------------------------
-- TRINIFICATION-INVARIANT QUARTIC SELECTING THE TWO-VEV ORBIT
--
-- For two bifundamental 3x3 scalar blocks Phi,Chi transforming as
--
--   Phi -> U_L Phi U_R^dagger,
--   Chi -> U_L Chi U_R^dagger,
--
-- consider the dimensionless comparison potential
--
-- V = (nPhi-1)^2 + (nChi-1)^2
--   + [nPhi^2 - tr((Phi^dagger Phi)^2)]
--   + [nChi^2 - tr((Chi^dagger Chi)^2)]
--   + tr(Phi^dagger Phi Chi^dagger Chi)
--   + [nPhi nChi - tr(Phi Phi^dagger Chi Chi^dagger)].
--
-- Each bracketed/cross term is nonnegative for complex matrices.  At V=0 the
-- two fields have unit norm and rank one, their right vectors are orthogonal,
-- and their left vectors span the same line.  Such a pair is on the common
-- SU(3)_L x SU(3)_R orbit of E_32,E_33.  The executable probe checks the
-- selected pair, random gauge transforms and random nonnegativity samples.
--
-- This is an existence/selectability construction for the trinification gauge
-- symmetry.  It is not claimed to be the unique potential, an E6-invariant
-- potential, or the physically derived scalar sector.
------------------------------------------------------------------------

candidatePotential : String
candidatePotential = "(nPhi-1)^2+(nChi-1)^2+rankPenalty(Phi)+rankPenalty(Chi)+tr(Phi^dagger Phi Chi^dagger Chi)+nPhi*nChi-tr(Phi Phi^dagger Chi Chi^dagger)"

zeroOrbitDescription : String
zeroOrbitDescription = "unit rank-one pair; common left line; orthogonal right lines; gauge orbit of E_32,E_33"

record TrinificationInvariantTwoVEVPotentialLocalReceipt : Set where
  constructor trinification-invariant-two-vev-potential-local-receipt
  field
    sameBifundamentalBlocksUsed : Bool
    selectedE32E33PairHasZeroPotential : Bool
    sampledTermsNonnegative : Bool
    sampledSU3LxSU3RInvariancePaid : Bool
    sampledSelectedOrbitPointsRemainZero : Bool
    algebraicZeroConditionsIdentified : Bool
    zeroConditionsMatchDesiredGaugeOrbit : Bool
    quarticTrinificationGaugeInvariantCandidatePaid : Bool
    fullE6InvariancePaid : Bool
    uniquenessOfPotentialPaid : Bool
    physicalScalarContentPaid : Bool
    physicalCouplingsDerived : Bool
    physicalVEVScaleDerived : Bool
    empiricalHiggsSectorPaid : Bool
    boundary : String
open TrinificationInvariantTwoVEVPotentialLocalReceipt public

canonicalTrinificationInvariantTwoVEVPotentialLocalReceipt : TrinificationInvariantTwoVEVPotentialLocalReceipt
canonicalTrinificationInvariantTwoVEVPotentialLocalReceipt =
  trinification-invariant-two-vev-potential-local-receipt
    true true true true true true true true
    false false false false false false
    "A manifest SU(3)_L x SU(3)_R-invariant quartic candidate has the desired E32,E33 orbit as its zero set under the stated matrix inequalities. This proves selectability within a two-bifundamental scalar model, not that the repo's physical theory contains two scalar 27s, not full E6 invariance, not uniqueness, and not the physical coefficients or VEV scale."

breakingReceipt : Breaking.TrinificationTwoNeutralVEVLocalReceipt
breakingReceipt = Breaking.canonicalTrinificationTwoNeutralVEVLocalReceipt

massReceipt : Mass.TwoVEVMassSpectrumLocalReceipt
massReceipt = Mass.canonicalTwoVEVMassSpectrumLocalReceipt

data CandidateInvariantPotentialCreatesPhysicalHiggsSector : Set where

candidatePotentialDoesNotCreatePhysicalHiggsSector :
  CandidateInvariantPotentialCreatesPhysicalHiggsSector → {A : Set} → A
candidatePotentialDoesNotCreatePhysicalHiggsSector ()
