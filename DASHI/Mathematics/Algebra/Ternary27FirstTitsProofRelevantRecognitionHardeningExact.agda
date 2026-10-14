module DASHI.Mathematics.Algebra.Ternary27FirstTitsProofRelevantRecognitionHardeningExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT HARDENING FOR THE SPLIT FIRST-TITS / E6 / F4 LANE
--
-- The first-Tits child branch correctly separates local executable evidence,
-- classical source authority and kernel application.  Two legacy records still
-- encode crucial obligations as fields whose values are themselves `Set`s:
--
--   * `FirstTitsAlbertStructure` names bilinearity/Jordan/cubic receipt TYPES;
--   * `StandardFirstTitsKernelApplicationReceipt` names same-product/cubic and
--     global F4/E6 application receipt TYPES.
--
-- A value of type `Set` is a proposition/type name, not an inhabitant of that
-- proposition.  These wrappers leave the historical API untouched while
-- requiring explicit witnesses before any local/global recognition is treated
-- as paid.  No source citation or Python receipt is upgraded in authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Primitive using (Set₁)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Tits
import DASHI.Mathematics.Algebra.Ternary27FirstTitsGlobalE6F4RecognitionExact as Global

------------------------------------------------------------------------
-- 1. Local algebra structure must carry inhabitants of its algebra-law types.
------------------------------------------------------------------------

record PaidFirstTitsAlbertStructure
    (local : Tits.FirstTitsAlbertStructure) : Set₁ where
  field
    bilinearityWitness : Tits.bilinearityReceipt local
    commutativityWitness : Tits.commutativityReceipt local
    unitWitness : Tits.unitReceipt local
    jordanIdentityWitness : Tits.jordanIdentityReceipt local
    cubicCompatibilityWitness : Tits.cubicCompatibilityReceipt local

open PaidFirstTitsAlbertStructure public

------------------------------------------------------------------------
-- 2. Global classification application must bind the local structure to the
--    standard first-Tits hypotheses and carry inhabitants of every conclusion.
------------------------------------------------------------------------

record PaidStandardFirstTitsKernelApplication
    (legacy : Global.StandardFirstTitsKernelApplicationReceipt) : Set₁ where
  field
    localStructurePaid :
      PaidFirstTitsAlbertStructure (Global.localFirstTitsStructure legacy)

    sameProductAsStandardFirstTitsWitness :
      Global.sameProductAsStandardFirstTitsReceipt legacy

    sameCubicAsStandardFirstTitsWitness :
      Global.sameCubicAsStandardFirstTitsReceipt legacy

    albertHypothesesWitness :
      Global.albertHypothesesReceipt legacy

    automorphismGroupF4Witness :
      Global.automorphismGroupF4Receipt legacy

    normIsometryGroupE6Witness :
      Global.normIsometryGroupE6Receipt legacy

    unitStabilizerF4Witness :
      Global.unitStabilizerF4Receipt legacy

open PaidStandardFirstTitsKernelApplication public

------------------------------------------------------------------------
-- 3. WrongType / attribution firewalls.
------------------------------------------------------------------------

data ClassicalSourceCreatesKernelApplication : Set where
data LocalPythonCreatesKernelApplication : Set where
data TypedAlbertLawCreatesLawWitness : Set where

classicalSourceDoesNotCreateKernelApplication :
  ClassicalSourceCreatesKernelApplication → ⊥
classicalSourceDoesNotCreateKernelApplication ()

localPythonDoesNotCreateKernelApplication :
  LocalPythonCreatesKernelApplication → ⊥
localPythonDoesNotCreateKernelApplication ()

typedAlbertLawDoesNotCreateLawWitness :
  TypedAlbertLawCreatesLawWitness → ⊥
typedAlbertLawDoesNotCreateLawWitness ()

------------------------------------------------------------------------
-- 4. Machine-readable boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    legacyFirstTitsStructureIsProofRelevant : Bool
    legacyKernelApplicationIsProofRelevant : Bool
    paidFirstTitsStructureWrapperAvailable : Bool
    paidKernelApplicationWrapperAvailable : Bool
    classicalSourceReceiptAlonePaysKernelApplication : Bool
    localExecutableReceiptAlonePaysKernelApplication : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  false false
  true true
  false false
