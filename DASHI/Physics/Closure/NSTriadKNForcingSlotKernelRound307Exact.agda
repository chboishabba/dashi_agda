module DASHI.Physics.Closure.NSTriadKNForcingSlotKernelRound307Exact where

------------------------------------------------------------------------
-- ROUND307 / R230 FORCING COMMUTATOR IS THE EXISTING R167 SLOT KERNEL
--
-- R306 identifies the doubled forcing cell with a helicity-slot difference.
-- R223 already proves, for any transverse pair (a,b),
--
--   i * slotKernel(nhat_p,nhat_q,a,b)
--     = 2 (a+ x b- - a- x b+).
--
-- Therefore, once the physical modal forcing at p is transverse, the literal
-- R230 cell satisfies
--
--   2 F_pq = i * slotKernel(nhat_p,nhat_q,N_p,u_q).
--
-- 2026 SAME-OBJECT CORRECTION
-- ---------------------------
-- Round30 already proves that the repository's ACTUAL exhaustive Leray-
-- projected nonlinear coefficient `Audit.projectedNonlinearity system p` is
-- transverse at every nonzero p. `Audit.integerEmbedding system` is
-- definitionally the same E indexing the finite system. Hence the old
-- transversality-weld flag was stale: the forcing-side compiler is already
-- available. The only cell hypotheses retained below are exactly the ones the
-- physical consumer must provide: p is nonzero and the q-velocity is
-- transverse. No all-cell/global claim is inferred from the compiler itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuadraticKernelRound223Exact as R223
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306

record TransverseForcingVelocityPair
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (p q : Z3.FourierMode)
    (forcingP velocityQ : C3.Complex3 F) : Set r where
  constructor transverse-forcing-velocity-pair
  field
    transverseForcing : Helical.Transverse E p forcingP
    transverseVelocity : Helical.Transverse E q velocityQ

open TransverseForcingVelocityPair public

asRound223Pair :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {p q : Z3.FourierMode}
    {forcingP velocityQ : C3.Complex3 F} →
  TransverseForcingVelocityPair E I S L H p q forcingP velocityQ →
  R223.PhysicalHelicityPair E I S L H p q forcingP velocityQ
asRound223Pair P =
  R223.physical-helicity-pair
    (transverseForcing P)
    (transverseVelocity P)

projectedNSForcingVelocityPair :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.p tau) →
  Helical.Transverse E (Physical.q tau)
    (Audit.velocity system (Physical.q tau)) →
  TransverseForcingVelocityPair E I S L H
    (Physical.p tau) (Physical.q tau)
    (Audit.projectedNonlinearity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
projectedNSForcingVelocityPair system tau pNonzero qTransverse =
  transverse-forcing-velocity-pair
    (R30.projectedNonlinearityTransverseExact
      system (Physical.p tau) pNonzero)
    qTransverse

doubledForcingCellIsIOuterSlotKernel :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence)
    (P : TransverseForcingVelocityPair E I S L H
      (Physical.p tau) (Physical.q tau)
      (forcing (Physical.p tau)) (velocity (Physical.q tau))) →
  R306.doubleR230Cell S velocity forcing tau
  ≡
  C3.complex3Scale (C3.complexI F)
    (R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (forcing (Physical.p tau))
      (velocity (Physical.q tau)))
doubledForcingCellIsIOuterSlotKernel
    {E = E} {S = S} velocity forcing tau P =
  trans
    (R306.doubleR230CellIsHelicityCommutator S velocity forcing tau)
    (trans
      (R223.helicitySlotDifferenceIsDoubleMixedHelicity
        (Helical.helicalProjectorPlus _ _ S
          (Physical.p tau) (forcing (Physical.p tau)))
        (Helical.helicalProjectorMinus _ _ S
          (Physical.p tau) (forcing (Physical.p tau)))
        (Helical.helicalProjectorPlus _ _ S
          (Physical.q tau) (velocity (Physical.q tau)))
        (Helical.helicalProjectorMinus _ _ S
          (Physical.q tau) (velocity (Physical.q tau))))
      (sym
        (R223.iQuadraticKernelIsDoubleMixedHelicity
          (Physical.p tau) (Physical.q tau)
          (forcing (Physical.p tau)) (velocity (Physical.q tau))
          (asRound223Pair P))))

doubledProjectedNSForcingCellIsIOuterSlotKernel :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (pNonzero : Z3.NonZeroMode (Physical.p tau))
    (qTransverse : Helical.Transverse E (Physical.q tau)
      (Audit.velocity system (Physical.q tau))) →
  R306.doubleR230Cell S
    (Audit.velocity system)
    (Audit.projectedNonlinearity system)
    tau
  ≡
  C3.complex3Scale (C3.complexI F)
    (R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (Audit.projectedNonlinearity system (Physical.p tau))
      (Audit.velocity system (Physical.q tau)))
doubledProjectedNSForcingCellIsIOuterSlotKernel
    system tau pNonzero qTransverse =
  doubledForcingCellIsIOuterSlotKernel
    (Audit.velocity system)
    (Audit.projectedNonlinearity system)
    tau
    (projectedNSForcingVelocityPair system tau pNonzero qTransverse)

round307R230ForcingUsesExistingOuterSlotKernel : Bool
round307R230ForcingUsesExistingOuterSlotKernel = true

round307OuterHHNullGeometryReusable : Bool
round307OuterHHNullGeometryReusable = true

round307ProjectedNSForcingTransversalityCompilerClosed : Bool
round307ProjectedNSForcingTransversalityCompilerClosed = true

-- Compatibility status, now interpreted as the forcing-side same-object weld.
-- Global availability of p-nonzero/q-transverse hypotheses remains a separate
-- physical-family question and is not smuggled into this flag.
round307PhysicalProjectedNSForcingTransversalityWeldClosed : Bool
round307PhysicalProjectedNSForcingTransversalityWeldClosed = true

round307AllOuterCellsMeetCompilerHypotheses : Bool
round307AllOuterCellsMeetCompilerHypotheses = false

round307OuterSlotKernelAlonePaysFullCriticalCone : Bool
round307OuterSlotKernelAlonePaysFullCriticalCone = false

round307PackageAClosed : Bool
round307PackageAClosed = false

round307ClayPromotion : Bool
round307ClayPromotion = false

round307ProjectedNSForcingTransversalityCompilerClosedIsTrue :
  round307ProjectedNSForcingTransversalityCompilerClosed ≡ true
round307ProjectedNSForcingTransversalityCompilerClosedIsTrue = refl

round307PhysicalProjectedNSForcingTransversalityWeldClosedIsTrue :
  round307PhysicalProjectedNSForcingTransversalityWeldClosed ≡ true
round307PhysicalProjectedNSForcingTransversalityWeldClosedIsTrue = refl

round307AllOuterCellsMeetCompilerHypothesesIsFalse :
  round307AllOuterCellsMeetCompilerHypotheses ≡ false
round307AllOuterCellsMeetCompilerHypothesesIsFalse = refl
