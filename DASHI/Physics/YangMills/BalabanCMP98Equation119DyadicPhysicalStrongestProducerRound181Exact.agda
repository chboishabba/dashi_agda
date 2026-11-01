{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPhysicalStrongestProducerRound181Exact where

------------------------------------------------------------------------
-- ROUND181 A1 BIDI: EXISTING DYADIC PHYSICAL LOG + FEDERBUSH FAMILY -> EQ119
--
-- The selected-cut lane was useful for reconstructing principal-image
-- admission from explicit link defects.  But the existing CMP109 dyadic
-- physical owner already carries `PhysicalSU2PrincipalLogMeaning`, whose
-- `smallFieldImage` theorem gives principal-image admission directly from its
-- physical small-field predicate.
--
-- Round180 welds that owner's transported-relative group element to the literal
-- CMP98 object U(Gamma_{c,x}) U(c)^-1.  Round177 generates the full differential
-- / adjoint calculus from the old Federbush convention family.  Therefore the
-- shortest BIDI producer no longer needs a separate selected-cut recognition
-- object or the scalar `1/24 <= selected cut radius` comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalPrincipalImageRound157Exact as R157
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPrintedYWeldRound180Exact as R180
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as Dyadic

existingFederbushLeftRightFamily :
  R177.ExistingFederbushConventionFamily →
  R154.UniformLeftRightDexpFamily Lie.SU2LieAlgebra
existingFederbushLeftRightFamily family =
  R159.asUniformLeftRightDexpFamily
    (R177.asUniformAdjointDifferentialCalculus family)

dyadicPhysicalOneStepDerivative :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : R180.CMP98CMP109DyadicRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
dyadicPhysicalOneStepDerivative source inputs weld family =
  R157.physicalPrincipalImageOneStepDerivative
    (R158.asRound152Source source)
    (Dyadic.principalLogMeaning inputs)
    (R180.asRound157PhysicalBridge source inputs weld)
    (existingFederbushLeftRightFamily family)

dyadicPhysicalMultiscaleDerivative :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : R180.CMP98CMP109DyadicRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
dyadicPhysicalMultiscaleDerivative source inputs weld family =
  R157.physicalPrincipalImageMultiscaleDerivative
    (R158.asRound152Source source)
    (Dyadic.principalLogMeaning inputs)
    (R180.asRound157PhysicalBridge source inputs weld)
    (existingFederbushLeftRightFamily family)

cmp98Equation119DyadicPhysicalStrongestProducerRound181Level : ProofLevel
cmp98Equation119DyadicPhysicalStrongestProducerRound181Level = machineChecked

literalCMP98DyadicRelativeSameObjectRound181Level : ProofLevel
literalCMP98DyadicRelativeSameObjectRound181Level = conditional
