module DASHI.Interop.PrimeSuccessorWitness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import Base369 using (TriTruth)
open import LogicTlurey using (Stage)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.TrackedPrimes as TrackedPrimes

------------------------------------------------------------------------
-- Prime successor witnesses over Stage12.
--
-- The corrected number-theoretic reading is:
--   p       = the new prime lane / new axis / new body
--   p - 1   = the witness-space that proves what p can act on
--   +1      = the successor move from witness-space into the new prime lane
--
-- This module records that rule as a candidate-only Stage12 adapter layer.
-- The spine remains Stage12FibreSurface; prime witnesses sit over it.

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

five : Nat
five = suc four

six : Nat
six = suc five

seven : Nat
seven = suc six

eight : Nat
eight = suc seven

nine : Nat
nine = suc eight

ten : Nat
ten = suc nine

eleven : Nat
eleven = suc ten

twelve : Nat
twelve = suc eleven

thirteen : Nat
thirteen = suc twelve

record PrimeSuccessorWitnessAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedPrimeMetaphysics : Bool
    promotedPrimeMetaphysicsIsFalse : promotedPrimeMetaphysics ≡ false
    promotedQiAuthority : Bool
    promotedQiAuthorityIsFalse : promotedQiAuthority ≡ false
    promotedTaoAuthority : Bool
    promotedTaoAuthorityIsFalse : promotedTaoAuthority ≡ false
    promotedUniversalStageClaim : Bool
    promotedUniversalStageClaimIsFalse : promotedUniversalStageClaim ≡ false

canonicalPrimeSuccessorWitnessAuthorityBits :
  PrimeSuccessorWitnessAuthorityBits
canonicalPrimeSuccessorWitnessAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedPrimeMetaphysics = false
    ; promotedPrimeMetaphysicsIsFalse = refl
    ; promotedQiAuthority = false
    ; promotedQiAuthorityIsFalse = refl
    ; promotedTaoAuthority = false
    ; promotedTaoAuthorityIsFalse = refl
    ; promotedUniversalStageClaim = false
    ; promotedUniversalStageClaimIsFalse = refl
    }

record PrimeSuccessorWitness : Set where
  field
    witnessPrime : TrackedPrimes.SSP
    witnessPrimeLabel : String
    stageWitnessed : Nat
    successorLaw :
      TrackedPrimes.toNat witnessPrime ≡ suc stageWitnessed
    stage12FibreSurface :
      StageQuotient.Stage12FibreSurface
    stage12FibreSurfaceIsCanonical :
      stage12FibreSurface ≡ StageQuotient.canonicalStage12FibreSurface
    symmetryProfile :
      Symmetry.PrimeLaneSymmetryProfile
    symmetryProfileMatchesPrime :
      Symmetry.primeIdentity symmetryProfile ≡ witnessPrime
    witnessSpaceOrder :
      Nat
    witnessSpaceOrderMatchesStage :
      witnessSpaceOrder ≡ stageWitnessed
    primeLaneStagePoint :
      Atlas.StageAtlasZeroToEleven
    primeLaneStagePointMatches :
      primeLaneStagePoint ≡ Symmetry.additiveStage symmetryProfile
    witnessSpaceStagePoint :
      Atlas.StageAtlasZeroToEleven
    witnessSpaceStagePointMatches :
      witnessSpaceStagePoint ≡ Symmetry.unitStage symmetryProfile
    primeLaneResidue :
      Stage
    primeLaneResidueMatches :
      primeLaneResidue ≡
      StageQuotient.Stage12FibreSurface.residue
        stage12FibreSurface
        primeLaneStagePoint
    primeLaneTone :
      TriTruth
    primeLaneToneMatches :
      primeLaneTone ≡
      StageQuotient.Stage12FibreSurface.quotient
        stage12FibreSurface
        primeLaneStagePoint
    witnessSpaceResidue :
      Stage
    witnessSpaceResidueMatches :
      witnessSpaceResidue ≡
      StageQuotient.Stage12FibreSurface.residue
        stage12FibreSurface
        witnessSpaceStagePoint
    witnessSpaceTone :
      TriTruth
    witnessSpaceToneMatches :
      witnessSpaceTone ≡
      StageQuotient.Stage12FibreSurface.quotient
        stage12FibreSurface
        witnessSpaceStagePoint
    authorityBits :
      PrimeSuccessorWitnessAuthorityBits
    interpretation :
      List String

open PrimeSuccessorWitness public
open PrimeSuccessorWitnessAuthorityBits public

canonicalP2PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP2PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p2
    ; witnessPrimeLabel = "p2 witnesses stage 1"
    ; stageWitnessed = one
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.primeLaneSymmetryProfile TrackedPrimes.p2
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = one
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-2
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-1
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "p is the new prime lane / new axis / new body."
      ∷ "p - 1 is the witness-space that proves what p can act on."
      ∷ "2 is the 1-witness because 2 - 1 = 1."
      ∷ []
    }

canonicalP3PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP3PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p3
    ; witnessPrimeLabel = "p3 witnesses stage 2"
    ; stageWitnessed = two
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.primeLaneSymmetryProfile TrackedPrimes.p3
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = two
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-3
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-2
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "3 is the 2-witness / dialectics on binary duality."
      ∷ "Stage 3 is the minimal structure that can witness or mediate the dyad without collapsing either side."
      ∷ []
    }

canonicalP5PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP5PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p5
    ; witnessPrimeLabel = "p5 witnesses stage 4"
    ; stageWitnessed = four
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.primeLaneSymmetryProfile TrackedPrimes.p5
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = four
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-5
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-4
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "5 witnesses the tetralemma / 4-cycle."
      ∷ "The p5 lane is the +1 successor of the four-stage witness ecology."
      ∷ []
    }

canonicalP7PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP7PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p7
    ; witnessPrimeLabel = "p7 witnesses stage 6"
    ; stageWitnessed = six
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.p7PrimeLaneSymmetryProfile
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = six
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-7
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-6
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "6-action ecology +1 = 7-prime lane."
      ∷ "7 witnesses HexTruth / C6 tension."
      ∷ "p7 is not the stage spine; it is the first clean prime-local unit-action exemplar."
      ∷ []
    }

canonicalP11PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP11PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p11
    ; witnessPrimeLabel = "p11 witnesses stage 10"
    ; stageWitnessed = ten
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.p11PrimeLaneSymmetryProfile
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = ten
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-11
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-10
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "11 witnesses the 10-adic visible cycle."
      ∷ "Stage 10 is witnessed by p11; Stage 11 is p11 itself as the new lane."
      ∷ "The atlas-11 / rev-2 seam remains a global carry-depth fact, not a p11-only theorem."
      ∷ []
    }

canonicalP13PrimeSuccessorWitness : PrimeSuccessorWitness
canonicalP13PrimeSuccessorWitness =
  record
    { witnessPrime = TrackedPrimes.p13
    ; witnessPrimeLabel = "p13 witnesses stage 12"
    ; stageWitnessed = twelve
    ; successorLaw = refl
    ; stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; symmetryProfile = Symmetry.primeLaneSymmetryProfile TrackedPrimes.p13
    ; symmetryProfileMatchesPrime = refl
    ; witnessSpaceOrder = twelve
    ; witnessSpaceOrderMatchesStage = refl
    ; primeLaneStagePoint = Atlas.atlas-1
    ; primeLaneStagePointMatches = refl
    ; witnessSpaceStagePoint = Atlas.atlas-0
    ; witnessSpaceStagePointMatches = refl
    ; primeLaneResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; primeLaneResidueMatches = refl
    ; primeLaneTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; primeLaneToneMatches = refl
    ; witnessSpaceResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; witnessSpaceResidueMatches = refl
    ; witnessSpaceTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; witnessSpaceToneMatches = refl
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    ; interpretation =
        "13 witnesses the full Stage12 atlas."
      ∷ "p13 is the natural full Stage12 witness after p7 because 13 - 1 = 12."
      ∷ "Within the 0..11 atlas the witness-space projects to atlas-0 and the new prime lane projects to atlas-1."
      ∷ []
    }

canonicalPrimeSuccessorWitnesses : List PrimeSuccessorWitness
canonicalPrimeSuccessorWitnesses =
  canonicalP2PrimeSuccessorWitness
  ∷ canonicalP3PrimeSuccessorWitness
  ∷ canonicalP5PrimeSuccessorWitness
  ∷ canonicalP7PrimeSuccessorWitness
  ∷ canonicalP11PrimeSuccessorWitness
  ∷ canonicalP13PrimeSuccessorWitness
  ∷ []
