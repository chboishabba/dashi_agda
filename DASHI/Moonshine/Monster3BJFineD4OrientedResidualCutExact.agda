module DASHI.Moonshine.Monster3BJFineD4OrientedResidualCutExact where

------------------------------------------------------------------------
-- ORIGINAL SOURCES / SOURCE-ROLE BOUNDARY
-- Barraclough--Wilson (2007), DOI 10.1112/S1461157000001352:
-- N(3B) character table/quotient; ATLAS and Breuer/CTblLib: class values.
-- PRIOR REPO OWNERS:
-- TernaryMonsterSymmetryCandidateExact (D4 irrep species);
-- D4SO3NineIrrepRestrictionExact (D4 ordinary character table);
-- Monster3BPhaseTransportExact (centre inversion swaps zeta phases);
-- IIT PR #1148 (MODIFIED, nongeometric 8-trit A2-similitude D4);
-- JFine/Monster PR #1250 (actual 2A/4B/6D/12G class screening).
-- New pure finite CHARACTERS: residual with A1 = -19 (not an honest
-- D4 module) versus positive signed-monomial candidate 53:
--     11 A2 + 7 B1 + 7 B2 + 14 E2.
-- The signed monomial action C3-covariance is proved by finite Python,
-- not by these source-written Agda equality proofs.
-- No external Monster actual subgroup, faithful 78, actual Hom
-- intertwiner, or physical interpretation is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as Character
import DASHI.Moonshine.Monster3BPhaseTransportExact as Phase

-- The complete residual is a POSITIVE D4 ordinary character.
signedResidualIrrepMultiplicity : D4.D4IrrepKind → Nat
signedResidualIrrepMultiplicity D4.A1 = 0
signedResidualIrrepMultiplicity D4.A2 = 11
signedResidualIrrepMultiplicity D4.B1 = 7
signedResidualIrrepMultiplicity D4.B2 = 7
signedResidualIrrepMultiplicity D4.E2 = 14

signedResidualDimension :
  signedResidualIrrepMultiplicity D4.A1
  + signedResidualIrrepMultiplicity D4.A2
  + signedResidualIrrepMultiplicity D4.B1
  + signedResidualIrrepMultiplicity D4.B2
  + 2 * signedResidualIrrepMultiplicity D4.E2 ≡ 53
signedResidualDimension = refl

signedResidualClassTrace : Character.D4RotationClass → ℤ
signedResidualClassTrace class =
  Character.scaleInt 11 (Character.d4Character D4.A2 class)
  +ℤ Character.scaleInt 7 (Character.d4Character D4.B1 class)
  +ℤ Character.scaleInt 7 (Character.d4Character D4.B2 class)
  +ℤ Character.scaleInt 14 (Character.d4Character D4.E2 class)

signedResidualIdentityTrace :
  signedResidualClassTrace Character.identityClass ≡ + 53
signedResidualIdentityTrace = refl

signedResidualHalfTurnTrace :
  signedResidualClassTrace Character.centralHalfTurnClass ≡ -[1+ 2 ]
signedResidualHalfTurnTrace = refl

signedResidualQuarterTrace :
  signedResidualClassTrace Character.quarterTurnPairClass ≡ -[1+ 2 ]
signedResidualQuarterTrace = refl

signedResidualAxisMirrorTrace :
  signedResidualClassTrace Character.axisHalfTurnPairClass ≡ -[1+ 10 ]
signedResidualAxisMirrorTrace = refl

signedResidualDiagonalMirrorTrace :
  signedResidualClassTrace Character.diagonalHalfTurnPairClass ≡ -[1+ 10 ]
signedResidualDiagonalMirrorTrace = refl

-- Source-selected global phase rule already owned by PhaseTransport.
fullNormalizerSwapsIndividualZeta :
  Phase.transportPhase Phase.invertsGenerator Phase.zetaPhase
  ≡ Phase.zetaSquaredPhase
fullNormalizerSwapsIndividualZeta = Phase.invertingModeSwapsZeta

-- Character arithmetic does not supply an actual Monster W_zeta
-- action or an H4-left-regular equivariant monomial lift.
record AdmissionBoundary : Set where
  constructor admissionBoundary
  field
    previouslySourcedCharacterTableReused : Bool
    previouslySourcedD4IrrepsReused : Bool
    orientedGSpSourceActionModelReused : Bool
    fullMonsterD4NegativeNineteenNoGoLocallyExecuted : Bool
    signedResidual53CharacterDecompositionSourceWritten : Bool
    C3CovariantFiniteOrbitRepairLocallyExecuted : Bool
    fullRegularH4MonomialIntertwinerConstructed : Bool
    actualMonsterNormalizerEmbeddingProduced : Bool
    actual6SuzSelected78FullCharacterReceiptObserved : Bool
    thisAgdaModuleKernelTypechecked : Bool

currentAdmission : AdmissionBoundary
currentAdmission = admissionBoundary
  true true true true true true false false false false
