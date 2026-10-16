module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsJordanTerminalCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsUnitWitnessExact as Unit
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBilinearityWitnessExact as Bilinear
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCubicHomogeneityWitnessExact as Cubic

------------------------------------------------------------------------
-- TERMINAL LOCAL-ALGEBRA COMPILER
--
-- Every field of PaidRationalFirstTitsLaws except the Jordan identity now has
-- a literal source-written inhabitant on the exact rational M3(Q)^3 carrier.
-- This compiler therefore makes the live local algebra wall a SINGLE typed
-- proposition: Laws.JordanIdentity.
--
-- Supplying an actual inhabitant of that proposition compiles definitionally
-- into the complete proof-relevant law package.  No citation, Python receipt,
-- dimension/root computation, or classical Albert theorem can substitute.
------------------------------------------------------------------------

record PaidRationalFirstTitsLawsExceptJordan : Set where
  constructor paid-rational-first-tits-laws-except-jordan
  field
    leftAdditiveWitness : Laws.LeftAdditive
    rightAdditiveWitness : Laws.RightAdditive
    leftHomogeneousWitness : Laws.LeftHomogeneous
    rightHomogeneousWitness : Laws.RightHomogeneous
    commutativeWitness : Laws.Commutative
    leftUnitWitness : Laws.LeftUnit
    rightUnitWitness : Laws.RightUnit
    cubicUnitWitness : Laws.CubicUnit
    cubicHomogeneousWitness : Laws.CubicHomogeneous
open PaidRationalFirstTitsLawsExceptJordan public

canonicalLawsExceptJordan : PaidRationalFirstTitsLawsExceptJordan
canonicalLawsExceptJordan =
  paid-rational-first-tits-laws-except-jordan
    Bilinear.leftAdditiveWitness
    Bilinear.rightAdditiveWitness
    Bilinear.leftHomogeneousWitness
    Bilinear.rightHomogeneousWitness
    Basic.commutativeWitness
    Unit.leftUnitWitness
    Unit.rightUnitWitness
    Basic.cubicUnitWitness
    Cubic.cubicHomogeneousWitness

compilePaidRationalFirstTitsLaws :
  Laws.JordanIdentity → Laws.PaidRationalFirstTitsLaws
compilePaidRationalFirstTitsLaws jordanIdentityWitness =
  record
    { Laws.PaidRationalFirstTitsLaws.leftAdditiveWitness =
        leftAdditiveWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.rightAdditiveWitness =
        rightAdditiveWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.leftHomogeneousWitness =
        leftHomogeneousWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.rightHomogeneousWitness =
        rightHomogeneousWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.commutativeWitness =
        commutativeWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.leftUnitWitness =
        leftUnitWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.rightUnitWitness =
        rightUnitWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.jordanIdentityWitness =
        jordanIdentityWitness
    ; Laws.PaidRationalFirstTitsLaws.cubicUnitWitness =
        cubicUnitWitness canonicalLawsExceptJordan
    ; Laws.PaidRationalFirstTitsLaws.cubicHomogeneousWitness =
        cubicHomogeneousWitness canonicalLawsExceptJordan
    }

record JordanTerminalBoundary : Set where
  constructor jordan-terminal-boundary
  field
    bilinearitySourceWritten : Bool
    commutativitySourceWritten : Bool
    twoSidedUnitSourceWritten : Bool
    cubicUnitSourceWritten : Bool
    cubicHomogeneitySourceWritten : Bool
    allLocalLawsExceptJordanPackaged : Bool
    jordanIdentitySourceWritten : Bool
    fullPaidPackageInhabitedWithoutJordan : Bool
    jordanIdentityAloneCompilesFullPackage : Bool
    externalClassificationCanReplaceJordanWitness : Bool
    exactHeadKernelReceiptPresent : Bool
    boundary : String
open JordanTerminalBoundary public

canonicalBoundary : JordanTerminalBoundary
canonicalBoundary =
  jordan-terminal-boundary
    true true true true true true
    false false true false false
    "The proof-relevant local first-Tits wall is reduced to one proposition: JordanIdentity. All other PaidRationalFirstTitsLaws fields have literal source-written inhabitants and are packaged in canonicalLawsExceptJordan. An inhabitant of JordanIdentity compiles directly to the full paid package. External Albert classification, Python diagnostics, E6/F4 root recognition and source citations cannot replace that inhabitant; exact-head kernel verification remains separate."
