module DASHI.Physics.Closure.NSTriadKNComparableFixedOutputTwoSidedCollarRound213Exact where

------------------------------------------------------------------------
-- ROUND213 / TWO-SIDED FIXED-WIDTH CC SHELL COLLAR
--
-- Round210 gives the upper side for every fixed-output comparable partner:
--
--   j_p <= j_k + 2*Csep
--   j_q <= j_k + 2*Csep.
--
-- Round212 gives the resonance-side converse on one input:
--
--   j_k <= 1+j_p  OR  j_k <= 1+j_q.
--
-- The literal CC classifier says the two input shells differ by at most Csep
-- in either direction.  Therefore whichever input controls the output pulls
-- the other one with it, giving
--
--   j_k <= j_p + (Csep+1)
--   j_k <= j_q + (Csep+1).
--
-- Thus a fixed-output CC interaction is genuinely confined to a constant-width
-- dyadic collar around the output, independently of the Galerkin cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComparableShellLocalizationRound203Exact as R203
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputUpperCollarRound210Exact as R210
import DASHI.Physics.Closure.NSTriadKNResonantOutputShellTriangleRound212Exact as R212

F = R187.F

backwardCollar : Nat
backwardCollar = Shell.Csep + 1

onePlusToBackwardCollar :
  ∀ n → 1 + n ≤ n + backwardCollar
onePlusToBackwardCollar n =
  let
    onePlusN≤ : n + 1 ≤ n + (1 + Shell.Csep)
    onePlusN≤ =
      NatP.+-monoʳ-≤ n (NatP.m≤m+n 1 Shell.Csep)
  in
  subst
    (1 + n ≤_)
    (cong (n +_) (NatP.+-comm 1 Shell.Csep))
    (subst
      (_≤ n + (1 + Shell.Csep))
      (NatP.+-comm n 1)
      onePlusN≤)

record FixedOutputComparableTwoSidedCollar
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entry : R207.FixedOutputLocalizedComparablePartner system output) : Set where
  constructor fixed-output-comparable-two-sided-collar
  field
    upperCollar : R210.FixedOutputComparableUpperCollar entry

    outputAtMostBackwardCollarAboveP :
      Shell.shellIndex output
      ≤ Shell.shellIndex
          (Physical.p
            (R204.incidence
              (R205.localizedComparable (R207.partner entry))))
        + backwardCollar

    outputAtMostBackwardCollarAboveQ :
      Shell.shellIndex output
      ≤ Shell.shellIndex
          (Physical.q
            (R204.incidence
              (R205.localizedComparable (R207.partner entry))))
        + backwardCollar

open FixedOutputComparableTwoSidedCollar public

fixedOutputComparableTwoSidedCollar :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entry : R207.FixedOutputLocalizedComparablePartner system output) →
  FixedOutputComparableTwoSidedCollar entry
fixedOutputComparableTwoSidedCollar {output = output} entry =
  let
    localized = R205.localizedComparable (R207.partner entry)
    tau = R204.incidence localized
    collar = R204.shellLocalization localized

    outputShellAgreement :
      Shell.shellIndex (Physical.k tau) ≡ Shell.shellIndex output
    outputShellAgreement = cong Shell.shellIndex (R207.outputAgreement entry)

    resonanceWitness = R212.resonantOutputShellTracksOneInput tau
  in
  case resonanceWitness of λ where
    (inj₁ outputViaP) →
      let
        outputViaP' :
          Shell.shellIndex output ≤ 1 + Shell.shellIndex (Physical.p tau)
        outputViaP' = subst
          (_≤ 1 + Shell.shellIndex (Physical.p tau))
          outputShellAgreement outputViaP

        outputNearP :
          Shell.shellIndex output
          ≤ Shell.shellIndex (Physical.p tau) + backwardCollar
        outputNearP = NatP.≤-trans outputViaP'
          (onePlusToBackwardCollar (Shell.shellIndex (Physical.p tau)))

        outputViaQRaw :
          Shell.shellIndex output
          ≤ 1 + (Shell.shellIndex (Physical.q tau) + Shell.Csep)
        outputViaQRaw = NatP.≤-trans outputViaP'
          (NatP.+-monoʳ-≤ 1 (R203.pNotFarAboveQ collar))

        outputNearQ :
          Shell.shellIndex output
          ≤ Shell.shellIndex (Physical.q tau) + backwardCollar
        outputNearQ = subst
          (Shell.shellIndex output ≤_)
          (NatP.+-assoc (Shell.shellIndex (Physical.q tau)) Shell.Csep 1)
          (subst
            (Shell.shellIndex output ≤_)
            (NatP.+-comm 1 (Shell.shellIndex (Physical.q tau) + Shell.Csep))
            outputViaQRaw)
      in
      fixed-output-comparable-two-sided-collar
        (R210.fixedOutputComparableUpperCollar entry)
        outputNearP
        outputNearQ

    (inj₂ outputViaQ) →
      let
        outputViaQ' :
          Shell.shellIndex output ≤ 1 + Shell.shellIndex (Physical.q tau)
        outputViaQ' = subst
          (_≤ 1 + Shell.shellIndex (Physical.q tau))
          outputShellAgreement outputViaQ

        outputNearQ :
          Shell.shellIndex output
          ≤ Shell.shellIndex (Physical.q tau) + backwardCollar
        outputNearQ = NatP.≤-trans outputViaQ'
          (onePlusToBackwardCollar (Shell.shellIndex (Physical.q tau)))

        outputViaPRaw :
          Shell.shellIndex output
          ≤ 1 + (Shell.shellIndex (Physical.p tau) + Shell.Csep)
        outputViaPRaw = NatP.≤-trans outputViaQ'
          (NatP.+-monoʳ-≤ 1 (R203.qNotFarAboveP collar))

        outputNearP :
          Shell.shellIndex output
          ≤ Shell.shellIndex (Physical.p tau) + backwardCollar
        outputNearP = subst
          (Shell.shellIndex output ≤_)
          (NatP.+-assoc (Shell.shellIndex (Physical.p tau)) Shell.Csep 1)
          (subst
            (Shell.shellIndex output ≤_)
            (NatP.+-comm 1 (Shell.shellIndex (Physical.p tau) + Shell.Csep))
            outputViaPRaw)
      in
      fixed-output-comparable-two-sided-collar
        (R210.fixedOutputComparableUpperCollar entry)
        outputNearP
        outputNearQ
  where
  open import Function.Base using (case_of_)

round213FixedOutputCCTwoSidedCollarClosed : Bool
round213FixedOutputCCTwoSidedCollarClosed = true

round213CCTwoSidedCollarCutoffIndependent : Bool
round213CCTwoSidedCollarCutoffIndependent = true

round213CCResidualPaymentClosed : Bool
round213CCResidualPaymentClosed = false

round213PackageAClosed : Bool
round213PackageAClosed = false

round213ClayPromotion : Bool
round213ClayPromotion = false

round213FixedOutputCCTwoSidedCollarClosedIsTrue :
  round213FixedOutputCCTwoSidedCollarClosed ≡ true
round213FixedOutputCCTwoSidedCollarClosedIsTrue = refl
