module DASHI.Physics.Closure.NSTriadKNComparableFixedOutputUpperCollarRound210Exact where

------------------------------------------------------------------------
-- ROUND210 / BIDIRECTIONAL CUT: FIXED-OUTPUT CC INPUTS LIE BELOW k+2Csep
--
-- Forward producer side:
--   Round203 proves p and q are mutually Csep-comparable and that at least one
--   input is no more than Csep shells above the output.
--
-- Backward consumer side:
--   Round209 reduces the remaining CC problem to an outputwise quartic
--   residual budget.  A literal finite pair count is not required there;
--   what is useful is a cutoff-independent output-relative shell envelope.
--
-- Combining the two Round203 inequalities gives, for a fixed output k,
--
--   j_p <= j_k + 2 Csep
--   j_q <= j_k + 2 Csep.
--
-- This is deliberately one-sided.  No false lower collar or finite shell-count
-- claim is introduced.  The lower tail remains available for weighted-energy
-- summation in the next analytic producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; cong; sym; trans)

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

F = R187.F

twoCsep : Nat
twoCsep = Shell.Csep + Shell.Csep

record FixedOutputComparableUpperCollar
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entry : R207.FixedOutputLocalizedComparablePartner system output) : Set where
  constructor fixed-output-comparable-upper-collar
  field
    pAtMostTwoCollarsAboveOutput :
      Shell.shellIndex
        (Physical.p
          (R204.incidence
            (R205.localizedComparable (R207.partner entry))))
      ≤ Shell.shellIndex output + twoCsep

    qAtMostTwoCollarsAboveOutput :
      Shell.shellIndex
        (Physical.q
          (R204.incidence
            (R205.localizedComparable (R207.partner entry))))
      ≤ Shell.shellIndex output + twoCsep

open FixedOutputComparableUpperCollar public

fixedOutputComparableUpperCollar :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entry : R207.FixedOutputLocalizedComparablePartner system output) →
  FixedOutputComparableUpperCollar entry
fixedOutputComparableUpperCollar {output = output} entry =
  let
    localized = R205.localizedComparable (R207.partner entry)
    tau = R204.incidence localized
    collar = R204.shellLocalization localized

    outputShellAgreement :
      Shell.shellIndex (Physical.k tau) ≡ Shell.shellIndex output
    outputShellAgreement = cong Shell.shellIndex (R207.outputAgreement entry)

    pToOutputPlusC :
      Shell.shellIndex (Physical.p tau)
      ≤ Shell.shellIndex output + Shell.Csep →
      Shell.shellIndex (Physical.p tau)
      ≤ Shell.shellIndex output + twoCsep
    pToOutputPlusC pBound =
      NatP.≤-trans pBound
        (NatP.+-monoʳ-≤
          (Shell.shellIndex output + Shell.Csep)
          (NatP.m≤m+n Shell.Csep Shell.Csep))

    qToOutputPlusC :
      Shell.shellIndex (Physical.q tau)
      ≤ Shell.shellIndex output + Shell.Csep →
      Shell.shellIndex (Physical.q tau)
      ≤ Shell.shellIndex output + twoCsep
    qToOutputPlusC qBound =
      NatP.≤-trans qBound
        (NatP.+-monoʳ-≤
          (Shell.shellIndex output + Shell.Csep)
          (NatP.m≤m+n Shell.Csep Shell.Csep))

    outputAnchor = R203.oneInputNotFarAboveOutput collar
  in
  case outputAnchor of λ where
    (inj₁ pNearK) →
      let
        pNearOutput :
          Shell.shellIndex (Physical.p tau)
          ≤ Shell.shellIndex output + Shell.Csep
        pNearOutput = subst
          (λ j → Shell.shellIndex (Physical.p tau) ≤ j + Shell.Csep)
          outputShellAgreement pNearK

        qViaP :
          Shell.shellIndex (Physical.q tau)
          ≤ (Shell.shellIndex output + Shell.Csep) + Shell.Csep
        qViaP = NatP.≤-trans
          (R203.qNotFarAboveP collar)
          (NatP.+-monoʳ-≤ Shell.Csep pNearOutput)

        qFinal :
          Shell.shellIndex (Physical.q tau)
          ≤ Shell.shellIndex output + twoCsep
        qFinal = subst
          (Shell.shellIndex (Physical.q tau) ≤_)
          (NatP.+-assoc (Shell.shellIndex output) Shell.Csep Shell.Csep)
          qViaP
      in
      fixed-output-comparable-upper-collar
        (pToOutputPlusC pNearOutput)
        qFinal

    (inj₂ qNearK) →
      let
        qNearOutput :
          Shell.shellIndex (Physical.q tau)
          ≤ Shell.shellIndex output + Shell.Csep
        qNearOutput = subst
          (λ j → Shell.shellIndex (Physical.q tau) ≤ j + Shell.Csep)
          outputShellAgreement qNearK

        pViaQ :
          Shell.shellIndex (Physical.p tau)
          ≤ (Shell.shellIndex output + Shell.Csep) + Shell.Csep
        pViaQ = NatP.≤-trans
          (R203.pNotFarAboveQ collar)
          (NatP.+-monoʳ-≤ Shell.Csep qNearOutput)

        pFinal :
          Shell.shellIndex (Physical.p tau)
          ≤ Shell.shellIndex output + twoCsep
        pFinal = subst
          (Shell.shellIndex (Physical.p tau) ≤_)
          (NatP.+-assoc (Shell.shellIndex output) Shell.Csep Shell.Csep)
          pViaQ
      in
      fixed-output-comparable-upper-collar
        pFinal
        (qToOutputPlusC qNearOutput)

round210BothCCInputsUpperLocalizedToFixedOutput : Bool
round210BothCCInputsUpperLocalizedToFixedOutput = true

round210IntroducesLowerShellCollar : Bool
round210IntroducesLowerShellCollar = false

round210IntroducesCutoffShellCount : Bool
round210IntroducesCutoffShellCount = false

round210SameOutputCCResidualBudgetClosed : Bool
round210SameOutputCCResidualBudgetClosed = false

round210PackageAClosed : Bool
round210PackageAClosed = false

round210ClayPromotion : Bool
round210ClayPromotion = false

round210BothCCInputsUpperLocalizedToFixedOutputIsTrue :
  round210BothCCInputsUpperLocalizedToFixedOutput ≡ true
round210BothCCInputsUpperLocalizedToFixedOutputIsTrue = refl

round210IntroducesLowerShellCollarIsFalse :
  round210IntroducesLowerShellCollar ≡ false
round210IntroducesLowerShellCollarIsFalse = refl
