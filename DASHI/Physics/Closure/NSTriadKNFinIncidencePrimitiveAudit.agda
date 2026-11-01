module DASHI.Physics.Closure.NSTriadKNFinIncidencePrimitiveAudit where

------------------------------------------------------------------------
-- Audit of the Fin incidence constructors against the primitive
-- forced-tail, adversarial, and transition obligations.
--
-- This file is deliberately a sidecar.  It does not replace an existing
-- postulate or promote a downstream receipt.  A witness below is valid
-- only for the declared Fin carrier itself.  The target records at the end
-- state the extra equalities and scaled weight bounds needed to connect that
-- carrier to an abstract incidence family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _*_; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FT
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FTFin
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds as FTNat
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adv
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdvFin
import DASHI.Physics.Closure.NSTriadKNAdversarialRowConcreteBounds as AdvRow
import DASHI.Physics.Closure.NSTriadKNAdversarialColumnConcreteBounds as AdvCol
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Tr
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TrFin
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteBounds as TrBound

------------------------------------------------------------------------
-- Forced-tail: facts that follow from the declared Fin carriers.
------------------------------------------------------------------------

forcedTailFinHeadCarrierCount :
  (c : FT.ForcedTailClass) -> (N : Nat) -> Nat
forcedTailFinHeadCarrierCount c N = FT.forcedTailHeadCountBound c N

forcedTailFinTailCarrierCount :
  (c : FT.ForcedTailClass) -> (N : Nat) -> Nat
forcedTailFinTailCarrierCount c N = FT.forcedTailTailCountBound c N

forcedTailFinHeadCarrierBound :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  forcedTailFinHeadCarrierCount c N ≤ FT.forcedTailHeadCountBound c N
forcedTailFinHeadCarrierBound _ _ = ≤-refl

forcedTailFinTailCarrierBound :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  forcedTailFinTailCarrierCount c N ≤ FT.forcedTailTailCountBound c N
forcedTailFinTailCarrierBound _ _ = ≤-refl

forcedTailFinParameterCarrierCount :
  (c : FT.ForcedTailClass) -> (N : Nat) -> Nat
forcedTailFinParameterCarrierCount c N =
  forcedTailFinHeadCarrierCount c N * forcedTailFinTailCarrierCount c N

forcedTailFinIncidenceCarrierCount :
  (c : FT.ForcedTailClass) -> (N : Nat) -> Nat
forcedTailFinIncidenceCarrierCount c N =
  FT.forcedTailFiberConstant c * forcedTailFinParameterCarrierCount c N

-- This is the A-bound for the declared Fin carrier count, not for an
-- arbitrary abstract incidence family.
forcedTailFinIncidenceFiberBound :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  forcedTailFinIncidenceCarrierCount c N ≤
  FT.forcedTailFiberConstant c * forcedTailFinParameterCarrierCount c N
forcedTailFinIncidenceFiberBound _ _ = ≤-refl

forcedTailFinHeadTailProductIsMultiplicity :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  forcedTailFinHeadCarrierCount c N * forcedTailFinTailCarrierCount c N
    ≡ FT.forcedTailMultiplicityBound c N
forcedTailFinHeadTailProductIsMultiplicity _ _ = refl

forcedTailFinHeadTailProductBound :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  forcedTailFinHeadCarrierCount c N * forcedTailFinTailCarrierCount c N
    ≤ FT.forcedTailMultiplicityBound c N
forcedTailFinHeadTailProductBound _ _ = ≤-refl

-- Existing division-free proxy arithmetic is constructive Nat arithmetic.
-- It is not an actual magnitude theorem and is intentionally named as a
-- proxy witness here.
forcedTailFinN2ProxyArithmetic :
  (c : FT.ForcedTailClass) -> (N : Nat) ->
  FTNat.forcedTailN2ScaledLHS c N ≤ FTNat.forcedTailN2ScaledRHS c N
forcedTailFinN2ProxyArithmetic = FTNat.forcedTailN2ScaledArithmetic

------------------------------------------------------------------------
-- Adversarial: the same carrier-only audit.
------------------------------------------------------------------------

adversarialFinHeadCarrierCount :
  (c : Adv.AdversarialClass) -> (N : Nat) -> Nat
adversarialFinHeadCarrierCount c N = Adv.adversarialRowCountBound c N

adversarialFinTailCarrierCount :
  (c : Adv.AdversarialClass) -> (N : Nat) -> Nat
adversarialFinTailCarrierCount c N = Adv.adversarialColumnCountBound c N

adversarialFinHeadCarrierBound :
  (c : Adv.AdversarialClass) -> (N : Nat) ->
  adversarialFinHeadCarrierCount c N ≤ Adv.adversarialRowCountBound c N
adversarialFinHeadCarrierBound _ _ = ≤-refl

adversarialFinTailCarrierBound :
  (c : Adv.AdversarialClass) -> (N : Nat) ->
  adversarialFinTailCarrierCount c N ≤ Adv.adversarialColumnCountBound c N
adversarialFinTailCarrierBound _ _ = ≤-refl

adversarialFinParameterCarrierCount :
  (c : Adv.AdversarialClass) -> (N : Nat) -> Nat
adversarialFinParameterCarrierCount c N =
  adversarialFinHeadCarrierCount c N * adversarialFinTailCarrierCount c N

adversarialFinIncidenceCarrierCount :
  (c : Adv.AdversarialClass) -> (N : Nat) -> Nat
adversarialFinIncidenceCarrierCount c N =
  AdvFin.adversarialFiberConstant c * adversarialFinParameterCarrierCount c N

adversarialFinIncidenceFiberBound :
  (c : Adv.AdversarialClass) -> (N : Nat) ->
  adversarialFinIncidenceCarrierCount c N ≤
  AdvFin.adversarialFiberConstant c * adversarialFinParameterCarrierCount c N
adversarialFinIncidenceFiberBound _ _ = ≤-refl

------------------------------------------------------------------------
-- Transition: the same carrier-only audit.
------------------------------------------------------------------------

transitionFinHeadCarrierCount :
  (c : Tr.TransitionClass) -> (N : Nat) -> Nat
transitionFinHeadCarrierCount c N = Tr.transitionRowCountBound c N

transitionFinTailCarrierCount :
  (c : Tr.TransitionClass) -> (N : Nat) -> Nat
transitionFinTailCarrierCount c N = Tr.transitionColumnCountBound c N

transitionFinHeadCarrierBound :
  (c : Tr.TransitionClass) -> (N : Nat) ->
  transitionFinHeadCarrierCount c N ≤ Tr.transitionRowCountBound c N
transitionFinHeadCarrierBound _ _ = ≤-refl

transitionFinTailCarrierBound :
  (c : Tr.TransitionClass) -> (N : Nat) ->
  transitionFinTailCarrierCount c N ≤ Tr.transitionColumnCountBound c N
transitionFinTailCarrierBound _ _ = ≤-refl

transitionFinParameterCarrierCount :
  (c : Tr.TransitionClass) -> (N : Nat) -> Nat
transitionFinParameterCarrierCount c N =
  transitionFinHeadCarrierCount c N * transitionFinTailCarrierCount c N

transitionFinIncidenceCarrierCount :
  (c : Tr.TransitionClass) -> (N : Nat) -> Nat
transitionFinIncidenceCarrierCount c N =
  TrFin.transitionFiberConstant c * transitionFinParameterCarrierCount c N

transitionFinIncidenceFiberBound :
  (c : Tr.TransitionClass) -> (N : Nat) ->
  transitionFinIncidenceCarrierCount c N ≤
  TrFin.transitionFiberConstant c * transitionFinParameterCarrierCount c N
transitionFinIncidenceFiberBound _ _ = ≤-refl

------------------------------------------------------------------------
-- Exact missing assumptions.
------------------------------------------------------------------------

-- A carrier equivalence is the missing bridge between an abstract family
-- and a concrete Fin constructor.  A count equality alone would not show
-- that the abstract incidences have the same encoding or residue data.
record FinCarrierRealization (Abstract Concrete : Set) : Set where
  field
    toConcrete : Abstract -> Concrete
    toAbstract : Concrete -> Abstract
    roundTripAbstract :
      (x : Abstract) -> toAbstract (toConcrete x) ≡ x
    roundTripConcrete :
      (x : Concrete) -> toConcrete (toAbstract x) ≡ x

-- A/B1/B2 become useful only after the abstract counts are identified with
-- the declared Fin carrier counts.  This record is a target, not a proof of
-- that identification.
record ForcedTailFinRealizationTarget
    (c : FT.ForcedTailClass) (N : Nat) : Set₁ where
  field
    abstractIncidenceFamily : Set
    incidenceRealization :
      FinCarrierRealization abstractIncidenceFamily
        (FTFin.ForcedTailTriadIncidence c N)
    abstractIncidenceCount : Nat
    abstractHeadCount : Nat
    abstractTailCount : Nat
    incidenceCountIsFinCarrierCount :
      abstractIncidenceCount ≡ forcedTailFinIncidenceCarrierCount c N
    headCountIsFinCarrierCount :
      abstractHeadCount ≡ forcedTailFinHeadCarrierCount c N
    tailCountIsFinCarrierCount :
      abstractTailCount ≡ forcedTailFinTailCarrierCount c N

-- C and D need a kernel/envelope factorisation and a scaled inequality;
-- neither is determined by Fin membership.
record ForcedTailScaledMagnitudeTarget
    (c : FT.ForcedTailClass) (N : Nat) : Set where
  field
    kernelWeightTimesDenominator :
      FTFin.ForcedTailTriadIncidence c N -> Nat
    envelopeWeightTimesDenominator :
      FTFin.ForcedTailTriadIncidence c N -> Nat
    kernelEnvelopeBound :
      (tau : FTFin.ForcedTailTriadIncidence c N) ->
      kernelWeightTimesDenominator tau ≤ envelopeWeightTimesDenominator tau
    classEnvelopeBound :
      (tau : FTFin.ForcedTailTriadIncidence c N) ->
      envelopeWeightTimesDenominator tau ≤
      FT.forcedTailClassProductN2Constant c

-- E's proxy arithmetic can be promoted only after the actual scaled
-- magnitude is identified with the proxy numerator/denominator model.
record ForcedTailN2InstantiationTarget
    (c : FT.ForcedTailClass) (N : Nat) : Set where
  field
    actualScaledMagnitudeNumerator : Nat
    actualScaledMagnitudeNumeratorIsProxy :
      actualScaledMagnitudeNumerator ≡ 1
    actualMultiplicityIsFinCarrierCount :
      FT.forcedTailMultiplicityBound c N
        ≡ forcedTailFinParameterCarrierCount c N

record AdversarialFinRealizationTarget
    (c : Adv.AdversarialClass) (N : Nat) : Set₁ where
  field
    abstractIncidenceFamily : Set
    incidenceRealization :
      FinCarrierRealization abstractIncidenceFamily
        (AdvFin.AdversarialTriadIncidence c N)
    abstractIncidenceCount : Nat
    abstractRowCount : Nat
    abstractColumnCount : Nat
    incidenceCountIsFinCarrierCount :
      abstractIncidenceCount ≡ adversarialFinIncidenceCarrierCount c N
    rowCountIsFinCarrierCount :
      abstractRowCount ≡ adversarialFinHeadCarrierCount c N
    columnCountIsFinCarrierCount :
      abstractColumnCount ≡ adversarialFinTailCarrierCount c N

record AdversarialScaledMagnitudeTarget
    (c : Adv.AdversarialClass) (N : Nat) : Set where
  field
    rowKernelWeightTimesDenominator :
      AdvFin.AdversarialTriadIncidence c N -> Nat
    rowKernelWeightTimesDenominatorBound :
      (tau : AdvFin.AdversarialTriadIncidence c N) ->
      rowKernelWeightTimesDenominator tau ≤ 1
    columnKernelWeightTimesDenominator :
      AdvFin.AdversarialTriadIncidence c N -> Nat
    columnKernelWeightTimesDenominatorBound :
      (tau : AdvFin.AdversarialTriadIncidence c N) ->
      columnKernelWeightTimesDenominator tau ≤ 1
    rowCountMagnitudeProductBound :
      adversarialFinHeadCarrierCount c N ≤
      AdvRow.adversarialRowProductN2Constant c *
        AdvRow.adversarialRowDenominator c N
    columnCountMagnitudeProductBound :
      adversarialFinTailCarrierCount c N ≤
      AdvCol.adversarialColumnProductN1Constant c *
        AdvCol.adversarialColumnDenominator c N

record TransitionFinRealizationTarget
    (c : Tr.TransitionClass) (N : Nat) : Set₁ where
  field
    abstractIncidenceFamily : Set
    incidenceRealization :
      FinCarrierRealization abstractIncidenceFamily
        (TrFin.TransitionTriadIncidence c N)
    abstractIncidenceCount : Nat
    abstractRowCount : Nat
    abstractColumnCount : Nat
    incidenceCountIsFinCarrierCount :
      abstractIncidenceCount ≡ transitionFinIncidenceCarrierCount c N
    rowCountIsFinCarrierCount :
      abstractRowCount ≡ transitionFinHeadCarrierCount c N
    columnCountIsFinCarrierCount :
      abstractColumnCount ≡ transitionFinTailCarrierCount c N

record TransitionScaledMagnitudeTarget
    (c : Tr.TransitionClass) (N : Nat) : Set where
  field
    kernelWeightTimesDenominator :
      TrFin.TransitionTriadIncidence c N -> Nat
    piProductScaleBound :
      (tau : TrFin.TransitionTriadIncidence c N) ->
      kernelWeightTimesDenominator tau ≤ 1
    magnitudeEnvelopeBound :
      (tau : TrFin.TransitionTriadIncidence c N) ->
      kernelWeightTimesDenominator tau ≤ 1
    rowCountMagnitudeProductBound :
      transitionFinHeadCarrierCount c N ≤
      TrBound.transitionRowProductN1Constant c *
        TrBound.transitionMagnitudeDenominator c N
    columnCountMagnitudeProductBound :
      transitionFinTailCarrierCount c N ≤
      TrBound.transitionColumnProductN1Constant c *
        TrBound.transitionMagnitudeDenominator c N

------------------------------------------------------------------------
-- Machine-readable audit result.  The false fields mean "not derivable
-- from Fin encodings in this sidecar", not that the corresponding theorem
-- is false.
------------------------------------------------------------------------

record NSTriadKNFinIncidencePrimitiveAuditStatus : Set where
  field
    forcedTailFinFiberBoundProved : Bool
    forcedTailFinHeadBoundProved : Bool
    forcedTailFinTailBoundProved : Bool
    forcedTailFinProductProved : Bool
    forcedTailFinProxyN2ArithmeticProved : Bool
    forcedTailKernelBoundFromFin : Bool
    forcedTailClassEnvelopeFromFin : Bool
    forcedTailActualN2BoundFromFin : Bool
    adversarialFinRowBoundProved : Bool
    adversarialFinColumnBoundProved : Bool
    adversarialMagnitudeFromFin : Bool
    transitionFinRowBoundProved : Bool
    transitionFinColumnBoundProved : Bool
    transitionMagnitudeFromFin : Bool

currentNSTriadKNFinIncidencePrimitiveAuditStatus :
  NSTriadKNFinIncidencePrimitiveAuditStatus
currentNSTriadKNFinIncidencePrimitiveAuditStatus =
  record
    { forcedTailFinFiberBoundProved = true
    ; forcedTailFinHeadBoundProved = true
    ; forcedTailFinTailBoundProved = true
    ; forcedTailFinProductProved = true
    ; forcedTailFinProxyN2ArithmeticProved = true
    ; forcedTailKernelBoundFromFin = false
    ; forcedTailClassEnvelopeFromFin = false
    ; forcedTailActualN2BoundFromFin = false
    ; adversarialFinRowBoundProved = true
    ; adversarialFinColumnBoundProved = true
    ; adversarialMagnitudeFromFin = false
    ; transitionFinRowBoundProved = true
    ; transitionFinColumnBoundProved = true
    ; transitionMagnitudeFromFin = false
    }
