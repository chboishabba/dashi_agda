module DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact where

------------------------------------------------------------------------
-- ROUND120 / PHYSICAL SHARED-OUTPUT PURE COMMUTATOR PARTNER
--
-- The Lean cross-triad calculation reported for
-- RequestProject/NavierStokes/WaleffeExternalCrossTriadCells.lean identifies
-- the highest-alpha partner on one output fibre as
--
--   a |-> k-a.
--
-- On the repository's ordered physical-incidence carrier this is exactly the
-- existing p/q swap.  The important point is that one must add the TWO
-- ORDERED GALERKIN VECTORS first.  Their sum is the stored ordered-pair
-- interaction, and Round106 already proves for helical inputs that this vector
-- is *exactly*
--
--   (lambda_q-lambda_p) P_k (u_p x u_q).
--
-- Thus the apparent Round114 antisymmetry defect vanishes at this partner
-- scale: the pair is a pure multiplier-difference commutator, not a
-- multiplier-difference term plus an independent remainder.
--
-- This file closes that same-object Agda vector identity and its tested
-- quartic-cell form.  No estimate, absolute value, Bony routing, shell count,
-- or cutoff factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111

record PhysicalHelicalOutputPair
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor physical-helical-output-pair
  field
    outputNonzero : Z3.NonZeroMode (Physical.k tau)
    signedEigenP signedEigenQ : C3.Complex F
    curlEigenP :
      Conv.curlFromWave
        (C3.modeVector E (Physical.p tau))
        (Audit.velocity system (Physical.p tau))
      ≡ C3.complex3Scale signedEigenP
          (Audit.velocity system (Physical.p tau))
    curlEigenQ :
      Conv.curlFromWave
        (C3.modeVector E (Physical.q tau))
        (Audit.velocity system (Physical.q tau))
      ≡ C3.complex3Scale signedEigenQ
          (Audit.velocity system (Physical.q tau))

open PhysicalHelicalOutputPair public

asRound106Data :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  PhysicalHelicalOutputPair system tau →
  R106.ProjectedHelicalPairData E I
    (Physical.p tau) (Physical.q tau) (Physical.k tau)
asRound106Data {system = system} {tau = tau} H =
  R106.projected-helical-pair-data
    (Physical.resonance tau)
    (outputNonzero H)
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (signedEigenP H)
    (signedEigenQ H)
    (curlEigenP H)
    (curlEigenQ H)

partnerVectorSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
partnerVectorSum system tau =
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))

pureCommutatorVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  PhysicalHelicalOutputPair system tau → C3.Complex3 F
pureCommutatorVector {E = E} {I = I} system tau H =
  C3.complex3Scale
    (C3.complexSubtract (signedEigenQ H) (signedEigenP H))
    (C3.lerayProject3 E I (Physical.k tau)
      (Cross.complex3Cross
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))))

sharedOutputPartnerSumIsPureMultiplierDifference :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (H : PhysicalHelicalOutputPair system tau) →
  partnerVectorSum system tau ≡ pureCommutatorVector system tau H
sharedOutputPartnerSumIsPureMultiplierDifference system tau H =
  trans
    (sym (R111.selfForcingKIsTwoSelectedOrderedTerms system tau))
    (R106.projectedHelicalOrderedPairVector (asRound106Data H))

quarticCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F → C3.Complex F
quarticCell system forcing testCross =
  C3.hermitianPairing3 (Audit.projectedOrderedTerm system forcing) testCross

partnerQuarticCellSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F → C3.Complex F
partnerQuarticCellSum system tau testCross =
  C3.complexAdd
    (quarticCell system tau testCross)
    (quarticCell system (Symmetry.swapTriad tau) testCross)

partnerQuarticCellSumIsPureCommutatorPairing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (H : PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F) →
  partnerQuarticCellSum system tau testCross
  ≡ C3.hermitianPairing3 (pureCommutatorVector system tau H) testCross
partnerQuarticCellSumIsPureCommutatorPairing system tau H testCross =
  trans
    (sym
      (Additive.hermitianPairingAddLeft
        (Audit.projectedOrderedTerm system tau)
        (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))
        testCross))
    (cong
      (λ forcing → C3.hermitianPairing3 forcing testCross)
      (sharedOutputPartnerSumIsPureMultiplierDifference system tau H))

round120PhysicalSharedOutputPartnerIsSwap : Bool
round120PhysicalSharedOutputPartnerIsSwap = true

round120PureMultiplierDifferenceVectorClosed : Bool
round120PureMultiplierDifferenceVectorClosed = true

round120PureQuarticCommutatorPairingClosed : Bool
round120PureQuarticCommutatorPairingClosed = true

round120IndependentAntisymmetryDefectSurvives : Bool
round120IndependentAntisymmetryDefectSurvives = false

round120UnrestrictedCriticalCommutatorPaymentClosed : Bool
round120UnrestrictedCriticalCommutatorPaymentClosed = false

round120PureMultiplierDifferenceVectorClosedIsTrue :
  round120PureMultiplierDifferenceVectorClosed ≡ true
round120PureMultiplierDifferenceVectorClosedIsTrue = refl

round120PureQuarticCommutatorPairingClosedIsTrue :
  round120PureQuarticCommutatorPairingClosed ≡ true
round120PureQuarticCommutatorPairingClosedIsTrue = refl

round120IndependentAntisymmetryDefectSurvivesIsFalse :
  round120IndependentAntisymmetryDefectSurvives ≡ false
round120IndependentAntisymmetryDefectSurvivesIsFalse = refl

round120UnrestrictedCriticalCommutatorPaymentClosedIsFalse :
  round120UnrestrictedCriticalCommutatorPaymentClosed ≡ false
round120UnrestrictedCriticalCommutatorPaymentClosedIsFalse = refl
