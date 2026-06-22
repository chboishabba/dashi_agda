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

data WitnessKind : Set where
  identityWitness : WitnessKind
  primeAxisWitness : WitnessKind
  primePowerDepthWitness : WitnessKind
  compositeCouplingWitness : WitnessKind

data FactorAxis : Set where
  axis-2 : FactorAxis
  axis-3 : FactorAxis
  axis-5 : FactorAxis
  axis-7 : FactorAxis
  axis-11 : FactorAxis
  axis-13 : FactorAxis

record FactorValuation : Set where
  field
    axis : FactorAxis
    exponent : Nat
    label : String

record StageSuccessorWitness : Set where
  field
    stage : Nat
    witness : Nat
    successorLaw : witness ≡ suc stage
    stagePoint : Atlas.StageAtlasZeroToEleven
    stagePointMatches :
      stagePoint ≡ Symmetry.stageCoordinateFromNatModulo12 stage
    projectedWitnessPoint : Atlas.StageAtlasZeroToEleven
    projectedWitnessPointMatches :
      projectedWitnessPoint ≡ Symmetry.stageCoordinateFromNatModulo12 witness
    stageResidue : Stage
    stageResidueMatches :
      stageResidue ≡
      StageQuotient.Stage12FibreSurface.residue
        StageQuotient.canonicalStage12FibreSurface
        stagePoint
    stageTone : TriTruth
    stageToneMatches :
      stageTone ≡
      StageQuotient.Stage12FibreSurface.quotient
        StageQuotient.canonicalStage12FibreSurface
        stagePoint
    projectedWitnessResidue : Stage
    projectedWitnessResidueMatches :
      projectedWitnessResidue ≡
      StageQuotient.Stage12FibreSurface.residue
        StageQuotient.canonicalStage12FibreSurface
        projectedWitnessPoint
    projectedWitnessTone : TriTruth
    projectedWitnessToneMatches :
      projectedWitnessTone ≡
      StageQuotient.Stage12FibreSurface.quotient
        StageQuotient.canonicalStage12FibreSurface
        projectedWitnessPoint
    witnessKind : WitnessKind
    factorSupport : List FactorValuation
    interpretation : List String
    authorityBits : PrimeSuccessorWitnessAuthorityBits

open StageSuccessorWitness public
open FactorValuation public

axis2-1 : FactorValuation
axis2-1 =
  record { axis = axis-2 ; exponent = one ; label = "v2=1" }

axis2-2 : FactorValuation
axis2-2 =
  record { axis = axis-2 ; exponent = two ; label = "v2=2" }

axis2-3 : FactorValuation
axis2-3 =
  record { axis = axis-2 ; exponent = three ; label = "v2=3" }

axis3-1 : FactorValuation
axis3-1 =
  record { axis = axis-3 ; exponent = one ; label = "v3=1" }

axis3-2 : FactorValuation
axis3-2 =
  record { axis = axis-3 ; exponent = two ; label = "v3=2" }

axis5-1 : FactorValuation
axis5-1 =
  record { axis = axis-5 ; exponent = one ; label = "v5=1" }

axis7-1 : FactorValuation
axis7-1 =
  record { axis = axis-7 ; exponent = one ; label = "v7=1" }

axis11-1 : FactorValuation
axis11-1 =
  record { axis = axis-11 ; exponent = one ; label = "v11=1" }

axis13-1 : FactorValuation
axis13-1 =
  record { axis = axis-13 ; exponent = one ; label = "v13=1" }

canonicalStage0SuccessorWitness : StageSuccessorWitness
canonicalStage0SuccessorWitness =
  record
    { stage = zero
    ; witness = one
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-0
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-1
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; projectedWitnessToneMatches = refl
    ; witnessKind = identityWitness
    ; factorSupport = []
    ; interpretation =
        "0 = unmarked ground; 1 = the first mark / identity witness."
      ∷ "Stage 0 is witnessed by 1 with empty p-adic support."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage1SuccessorWitness : StageSuccessorWitness
canonicalStage1SuccessorWitness =
  record
    { stage = one
    ; witness = two
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-1
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-2
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-1
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primeAxisWitness
    ; factorSupport = axis2-1 ∷ []
    ; interpretation =
        "1 is witnessed by 2 because 2 is the first nontrivial prime lane."
      ∷ "Prime witness means +1 opens a new irreducible axis."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage2SuccessorWitness : StageSuccessorWitness
canonicalStage2SuccessorWitness =
  record
    { stage = two
    ; witness = three
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-2
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-3
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-2
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primeAxisWitness
    ; factorSupport = axis3-1 ∷ []
    ; interpretation =
        "2 is witnessed by 3: dyadic polarity receives a mediating prime lane."
      ∷ "3 is the 2-witness / dialectics on binary duality."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage3SuccessorWitness : StageSuccessorWitness
canonicalStage3SuccessorWitness =
  record
    { stage = three
    ; witness = four
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-3
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-4
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-3
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primePowerDepthWitness
    ; factorSupport = axis2-2 ∷ []
    ; interpretation =
        "3 is witnessed by 4 = 2^2, so the successor deepens the dyadic axis instead of opening a new prime lane."
      ∷ "Prime-power witness means +1 increases valuation depth along an existing axis."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage4SuccessorWitness : StageSuccessorWitness
canonicalStage4SuccessorWitness =
  record
    { stage = four
    ; witness = five
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-4
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-5
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-4
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primeAxisWitness
    ; factorSupport = axis5-1 ∷ []
    ; interpretation =
        "4 is witnessed by 5: the fourfold process receives a new irreducible lane."
      ∷ "5 is the prime successor witness of the tetralemma / 4-cycle ecology."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage5SuccessorWitness : StageSuccessorWitness
canonicalStage5SuccessorWitness =
  record
    { stage = five
    ; witness = six
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-5
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-6
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-5
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; projectedWitnessToneMatches = refl
    ; witnessKind = compositeCouplingWitness
    ; factorSupport = axis2-1 ∷ axis3-1 ∷ []
    ; interpretation =
        "5 is witnessed by 6 = 2*3, the first coupled-axis witness."
      ∷ "Composite witness means +1 couples previously opened axes instead of introducing a new prime lane."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage6SuccessorWitness : StageSuccessorWitness
canonicalStage6SuccessorWitness =
  record
    { stage = six
    ; witness = seven
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-6
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-7
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-6
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primeAxisWitness
    ; factorSupport = axis7-1 ∷ []
    ; interpretation =
        "6 is witnessed by 7: HexTruth / active tension receives the p7 prime lane."
      ∷ "6-action ecology +1 = 7-prime lane."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage7SuccessorWitness : StageSuccessorWitness
canonicalStage7SuccessorWitness =
  record
    { stage = seven
    ; witness = eight
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-7
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-8
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-7
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-8
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-8
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primePowerDepthWitness
    ; factorSupport = axis2-3 ∷ []
    ; interpretation =
        "7 is witnessed by 8 = 2^3, so the successor over-deepens the binary axis rather than opening a new prime lane."
      ∷ "8 is a dyadic-depth witness and therefore a structural failed-gluing risk, not a person label."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage8SuccessorWitness : StageSuccessorWitness
canonicalStage8SuccessorWitness =
  record
    { stage = eight
    ; witness = nine
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-8
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-9
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-8
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-8
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-9
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-9
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primePowerDepthWitness
    ; factorSupport = axis3-2 ∷ []
    ; interpretation =
        "8 is witnessed by 9 = 3^2, so the successor refines the triadic axis."
      ∷ "9 is a triadic-depth repair / closure witness after the failed-gluing risk at 8."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage9SuccessorWitness : StageSuccessorWitness
canonicalStage9SuccessorWitness =
  record
    { stage = nine
    ; witness = ten
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-9
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-10
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-9
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-9
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; projectedWitnessToneMatches = refl
    ; witnessKind = compositeCouplingWitness
    ; factorSupport = axis2-1 ∷ axis5-1 ∷ []
    ; interpretation =
        "9 is witnessed by 10 = 2*5, a carry-body coupling between the dyadic lane and the p5 decision lane."
      ∷ "10 is the first decimal-style carry body rather than a new prime lane."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage10SuccessorWitness : StageSuccessorWitness
canonicalStage10SuccessorWitness =
  record
    { stage = ten
    ; witness = eleven
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-10
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-11
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-10
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; projectedWitnessToneMatches = refl
    ; witnessKind = primeAxisWitness
    ; factorSupport = axis11-1 ∷ []
    ; interpretation =
        "10 is witnessed by 11: the 10-cycle receives the p11 prime lane."
      ∷ "p11 is not only stage 11; it is the new prime body whose unit ecology has size 10."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStage11SuccessorWitness : StageSuccessorWitness
canonicalStage11SuccessorWitness =
  record
    { stage = eleven
    ; witness = twelve
    ; successorLaw = refl
    ; stagePoint = Atlas.atlas-11
    ; stagePointMatches = refl
    ; projectedWitnessPoint = Atlas.atlas-0
    ; projectedWitnessPointMatches = refl
    ; stageResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; stageResidueMatches = refl
    ; stageTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-11
    ; stageToneMatches = refl
    ; projectedWitnessResidue = StageQuotient.Stage12FibreSurface.residue StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; projectedWitnessResidueMatches = refl
    ; projectedWitnessTone = StageQuotient.Stage12FibreSurface.quotient StageQuotient.canonicalStage12FibreSurface Atlas.atlas-0
    ; projectedWitnessToneMatches = refl
    ; witnessKind = compositeCouplingWitness
    ; factorSupport = axis2-2 ∷ axis3-1 ∷ []
    ; interpretation =
        "11 is witnessed by 12 = 2^2*3, a manifold composite rather than a new prime lane."
      ∷ "The stage-11 manifold is coordinated by a coupled atlas witness that projects back to atlas-0 inside the 0..11 window."
      ∷ []
    ; authorityBits = canonicalPrimeSuccessorWitnessAuthorityBits
    }

canonicalStageSuccessorWitnesses : List StageSuccessorWitness
canonicalStageSuccessorWitnesses =
  canonicalStage0SuccessorWitness
  ∷ canonicalStage1SuccessorWitness
  ∷ canonicalStage2SuccessorWitness
  ∷ canonicalStage3SuccessorWitness
  ∷ canonicalStage4SuccessorWitness
  ∷ canonicalStage5SuccessorWitness
  ∷ canonicalStage6SuccessorWitness
  ∷ canonicalStage7SuccessorWitness
  ∷ canonicalStage8SuccessorWitness
  ∷ canonicalStage9SuccessorWitness
  ∷ canonicalStage10SuccessorWitness
  ∷ canonicalStage11SuccessorWitness
  ∷ []

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

stage12ClosurePrimeWitness : PrimeSuccessorWitness
stage12ClosurePrimeWitness = canonicalP13PrimeSuccessorWitness
