module DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact where

------------------------------------------------------------------------
-- R205 -> R574/R446 SAME-OBJECT PARTNER-DIFFERENCE ADAPTER
--
-- R205 owns the literal localized comparable raw-curl partner block and R181
-- compresses that block to one physical Complex3 cell by pairCell.  R574 owns
-- a completely generic two-vector difference carrier and sends its difference
-- to R446's positive-rate Hermitian Cauchy PSD carrier.
--
-- This file specializes those generic constructions to two actual R205
-- compressed partner cells.  The key point is purely same-object:
--
--   value (R574.toDifferenceCell574 (... alpha beta ...))
--     = pairCell(R205.comparablePartnerCell alpha)
--       - pairCell(R205.comparablePartnerCell beta).
--
-- Round177 already proves that the raw directional slot kernel is invariant
-- under the simultaneous p/q + velocity swap.  Hence each R205 partner block
-- is exactly two copies of ONE canonical slot kernel K_tau, and therefore
--
--   B_tau = 2 K_tau,
--   B_alpha - B_beta = 2 (K_alpha - K_beta),
--
-- represented below as exact vector addition rather than a new scalar carrier.
--
-- On the tighter R207 fixed-output carrier, Round176 then rewrites every
-- canonical K_tau through the SAME selected output vector.  The fixed-output
-- slot formula is bilinear in its two velocity arguments, so the difference
-- between two physical slots telescopes exactly into one left-amplitude
-- increment plus one right-amplitude increment:
--
--   Phi_k(a,b) - Phi_k(c,d)
--     = Phi_k(a-c,b) + Phi_k(c,b-d).
--
-- This is the first quotient-facing normalization: raw output labels are
-- erased, while the amplitude data actually seen by the slot kernel are
-- retained exactly.
--
-- No norm estimate, radial/Pluecker estimate, centered second-moment estimate,
-- cutoff aggregation, spacetime estimate, or Clay promotion is introduced.
-- The next genuine analytic splice is a quantitative estimate on the two
-- exact amplitude-increment branches above.  R128's radial/Pluecker identity
-- is a geometric donor for that theorem, not by itself a lower separation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlOutputDefectFactorizationRound176Exact as R176
import DASHI.Physics.Closure.NSTriadKNHHDualDefectUnconditionalPointwiseRound177Exact as R177
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact as R574

F = R205.F

compressedPartnerVector :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system → C3.Complex3 F
compressedPartnerVector partner =
  R181.pairCell (R205.comparablePartnerCell partner)

compressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system →
  C3.Complex3 F
compressedPartnerDifference alpha beta =
  C3.complex3Subtract
    (compressedPartnerVector alpha)
    (compressedPartnerVector beta)

------------------------------------------------------------------------
-- P0 / Canonical single-slot compression.
------------------------------------------------------------------------

compressedPartnerSlotKernel :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system → C3.Complex3 F
compressedPartnerSlotKernel partner =
  R186.rawCurlCell (R205.rawCurlData partner)

compressedPartnerSlotKernelDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system →
  C3.Complex3 F
compressedPartnerSlotKernelDifference alpha beta =
  C3.complex3Subtract
    (compressedPartnerSlotKernel alpha)
    (compressedPartnerSlotKernel beta)

compressedPartnerSwapKernelIsSlotKernel :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (partner : R205.LocalizedComparableRawCurlPartner system) →
  R186.rawCurlSwapCell (R205.rawCurlData partner)
  ≡ compressedPartnerSlotKernel partner
compressedPartnerSwapKernelIsSlotKernel {E = E} {system = system} partner =
  sym
    (R177.rawKernelSwapInvariant
      (C3.modeVector E (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
      (Audit.velocity system (Physical.p tau))
      (Audit.velocity system (Physical.q tau)))
  where
  tau = R204.incidence (R205.localizedComparable partner)

compressedPartnerIsDoubleSlotKernel :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (partner : R205.LocalizedComparableRawCurlPartner system) →
  compressedPartnerVector partner
  ≡ C3.complex3Add
      (compressedPartnerSlotKernel partner)
      (compressedPartnerSlotKernel partner)
compressedPartnerIsDoubleSlotKernel partner =
  cong
    (C3.complex3Add (compressedPartnerSlotKernel partner))
    (compressedPartnerSwapKernelIsSlotKernel partner)

-- Generic additive identity used only to expose
--   (K_a + K_a) - (K_b + K_b) = (K_a - K_b) + (K_a - K_b).
doubleSubtractIsDoubleDifference :
  (A B : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Add A A)
    (C3.complex3Add B B)
  ≡ C3.complex3Add
      (C3.complex3Subtract A B)
      (C3.complex3Subtract A B)
doubleSubtractIsDoubleDifference
    (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
  Field.complex3Ext
    (coord ax bx) (coord ay by) (coord az bz)
  where
  module R = Ring.Solver F

  coord : (a b : C3.Complex F) →
    C3.complexSubtract (C3.complexAdd a a) (C3.complexAdd b b)
    ≡ C3.complexAdd (C3.complexSubtract a b) (C3.complexSubtract a b)
  coord a b =
    R.solve 2
      (λ a b →
        ((a R.⊕ a) R.⊕ (R.⊝ (b R.⊕ b)))
        R.⊜
        ((a R.⊕ (R.⊝ b)) R.⊕ (a R.⊕ (R.⊝ b))))
      refl a b

compressedPartnerDifferenceIsDoubleSlotKernelDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  compressedPartnerDifference alpha beta
  ≡ C3.complex3Add
      (compressedPartnerSlotKernelDifference alpha beta)
      (compressedPartnerSlotKernelDifference alpha beta)
compressedPartnerDifferenceIsDoubleSlotKernelDifference alpha beta
  rewrite compressedPartnerIsDoubleSlotKernel alpha
        | compressedPartnerIsDoubleSlotKernel beta =
  doubleSubtractIsDoubleDifference
    (compressedPartnerSlotKernel alpha)
    (compressedPartnerSlotKernel beta)

------------------------------------------------------------------------
-- P1a / Fixed-output quotient normalization through the literal output vector.
------------------------------------------------------------------------

literalSlotFormulaAtWave :
  C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
literalSlotFormulaAtWave waveK uP uQ =
  C3.complex3Subtract
    (C3.complex3Add
      (C3.complex3Scale (C3.bilinearDot3 waveK uQ) uP)
      (C3.complex3Scale (C3.bilinearDot3 uP waveK) uQ))
    (C3.complex3Scale (C3.bilinearDot3 uP uQ) waveK)

literalOutputSlotFormula :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
literalOutputSlotFormula E output =
  literalSlotFormulaAtWave (C3.modeVector E output)

literalSlotFormulaDifferenceTelescopesLeft :
  (waveK a b c d : C3.Complex3 F) →
  C3.complex3Subtract
    (literalSlotFormulaAtWave waveK a b)
    (literalSlotFormulaAtWave waveK c d)
  ≡ C3.complex3Add
      (literalSlotFormulaAtWave waveK (C3.complex3Subtract a c) b)
      (literalSlotFormulaAtWave waveK c (C3.complex3Subtract b d))
literalSlotFormulaDifferenceTelescopesLeft
    (C3.complex3 kx ky kz)
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz)
    (C3.complex3 dx dy dz) =
  Field.complex3Ext
    (R.solve 15 goalX refl
      kx ky kz ax ay az bx by bz cx cy cz dx dy dz)
    (R.solve 15 goalY refl
      kx ky kz ax ay az bx by bz cx cy cz dx dy dz)
    (R.solve 15 goalZ refl
      kx ky kz ax ay az bx by bz cx cy cz dx dy dz)
  where
  module R = Ring.Solver F

  dot = λ x y z X Y Z →
    ((x R.⊗ X) R.⊕ (y R.⊗ Y)) R.⊕ (z R.⊗ Z)

  sub = λ x y → x R.⊕ (R.⊝ y)

  phiX = λ kx ky kz ax ay az bx by bz →
    (((dot kx ky kz bx by bz R.⊗ ax)
      R.⊕ (dot ax ay az kx ky kz R.⊗ bx))
      R.⊕ (R.⊝ (dot ax ay az bx by bz R.⊗ kx)))

  phiY = λ kx ky kz ax ay az bx by bz →
    (((dot kx ky kz bx by bz R.⊗ ay)
      R.⊕ (dot ax ay az kx ky kz R.⊗ by))
      R.⊕ (R.⊝ (dot ax ay az bx by bz R.⊗ ky)))

  phiZ = λ kx ky kz ax ay az bx by bz →
    (((dot kx ky kz bx by bz R.⊗ az)
      R.⊕ (dot ax ay az kx ky kz R.⊗ bz))
      R.⊕ (R.⊝ (dot ax ay az bx by bz R.⊗ kz)))

  goalX = λ kx ky kz ax ay az bx by bz cx cy cz dx dy dz →
    (phiX kx ky kz ax ay az bx by bz
      R.⊕ (R.⊝ (phiX kx ky kz cx cy cz dx dy dz)))
    R.⊜
    (phiX kx ky kz
      (sub ax cx) (sub ay cy) (sub az cz)
      bx by bz
      R.⊕
      phiX kx ky kz
        cx cy cz
        (sub bx dx) (sub by dy) (sub bz dz))

  goalY = λ kx ky kz ax ay az bx by bz cx cy cz dx dy dz →
    (phiY kx ky kz ax ay az bx by bz
      R.⊕ (R.⊝ (phiY kx ky kz cx cy cz dx dy dz)))
    R.⊜
    (phiY kx ky kz
      (sub ax cx) (sub ay cy) (sub az cz)
      bx by bz
      R.⊕
      phiY kx ky kz
        cx cy cz
        (sub bx dx) (sub by dy) (sub bz dz))

  goalZ = λ kx ky kz ax ay az bx by bz cx cy cz dx dy dz →
    (phiZ kx ky kz ax ay az bx by bz
      R.⊕ (R.⊝ (phiZ kx ky kz cx cy cz dx dy dz)))
    R.⊜
    (phiZ kx ky kz
      (sub ax cx) (sub ay cy) (sub az cz)
      bx by bz
      R.⊕
      phiZ kx ky kz
        cx cy cz
        (sub bx dx) (sub by dy) (sub bz dz))

literalOutputSlotFormulaDifferenceTelescopesLeft :
  (E : C3.IntegerEmbedding F) →
  (output : Z3.FourierMode) →
  (a b c d : C3.Complex3 F) →
  C3.complex3Subtract
    (literalOutputSlotFormula E output a b)
    (literalOutputSlotFormula E output c d)
  ≡ C3.complex3Add
      (literalOutputSlotFormula E output (C3.complex3Subtract a c) b)
      (literalOutputSlotFormula E output c (C3.complex3Subtract b d))
literalOutputSlotFormulaDifferenceTelescopesLeft E output =
  literalSlotFormulaDifferenceTelescopesLeft (C3.modeVector E output)

fixedOutputSlotKernelIsLiteralOutputFormula :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entry : R207.FixedOutputLocalizedComparablePartner system output) →
  let partner = R207.partner entry
      tau = R204.incidence (R205.localizedComparable partner)
      uP = Audit.velocity system (Physical.p tau)
      uQ = Audit.velocity system (Physical.q tau)
  in
  compressedPartnerSlotKernel partner
  ≡ literalOutputSlotFormula E output uP uQ
fixedOutputSlotKernelIsLiteralOutputFormula
    {E = E} {system = system} {output = output} entry =
  let
    partner = R207.partner entry
    data = R205.rawCurlData partner
    tau = R204.incidence (R205.localizedComparable partner)
    uP = Audit.velocity system (Physical.p tau)
    uQ = Audit.velocity system (Physical.q tau)

    physical =
      R176.rawPQSlotKernelFactorsThroughLiteralOutput
        E uP uQ
        (Physical.resonance tau)
        (R186.pTransverse data)
        (R186.qTransverse data)

    outputTransport =
      cong
        (λ selectedOutput → literalOutputSlotFormula E selectedOutput uP uQ)
        (R207.outputAgreement entry)
  in
  trans physical outputTransport

fixedOutputSlotKernelDifferenceIsLiteralOutputFormulaDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (alpha beta : R207.FixedOutputLocalizedComparablePartner system output) →
  let alphaPartner = R207.partner alpha
      betaPartner = R207.partner beta
      alphaTau = R204.incidence (R205.localizedComparable alphaPartner)
      betaTau = R204.incidence (R205.localizedComparable betaPartner)
      alphaUP = Audit.velocity system (Physical.p alphaTau)
      alphaUQ = Audit.velocity system (Physical.q alphaTau)
      betaUP = Audit.velocity system (Physical.p betaTau)
      betaUQ = Audit.velocity system (Physical.q betaTau)
  in
  compressedPartnerSlotKernelDifference alphaPartner betaPartner
  ≡ C3.complex3Subtract
      (literalOutputSlotFormula E output alphaUP alphaUQ)
      (literalOutputSlotFormula E output betaUP betaUQ)
fixedOutputSlotKernelDifferenceIsLiteralOutputFormulaDifference alpha beta =
  cong₂ C3.complex3Subtract
    (fixedOutputSlotKernelIsLiteralOutputFormula alpha)
    (fixedOutputSlotKernelIsLiteralOutputFormula beta)

------------------------------------------------------------------------
-- Existing R574/R446 same-object specialization.
------------------------------------------------------------------------

toR574PartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  (rate : ℚ) →
  Positive rate →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system →
  R574.CauchyVectorPairCell574
toR574PartnerDifference rate ratePositive alpha beta =
  R574.cauchy-vector-pair-cell-574
    rate
    (compressedPartnerVector alpha)
    (compressedPartnerVector beta)
    ratePositive

r574DifferenceIsCompressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  C3.complex3Subtract
    (R574.left574
      (toR574PartnerDifference rate ratePositive alpha beta))
    (R574.right574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ compressedPartnerDifference alpha beta
r574DifferenceIsCompressedPartnerDifference rate ratePositive alpha beta = refl

r446DifferenceValueIsCompressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  R446.value
    (R574.toDifferenceCell574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ compressedPartnerDifference alpha beta
r446DifferenceValueIsCompressedPartnerDifference rate ratePositive alpha beta = refl

r446DifferenceRateIsSelectedRate :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  R446.rate
    (R574.toDifferenceCell574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ rate
r446DifferenceRateIsSelectedRate rate ratePositive alpha beta = refl

------------------------------------------------------------------------
-- Fail-closed status.
------------------------------------------------------------------------

roundCenteredPartnerR205ToR574DifferenceSameObjectClosed : Bool
roundCenteredPartnerR205ToR574DifferenceSameObjectClosed = true

roundCenteredPartnerR574ToR446DifferenceSameObjectClosed : Bool
roundCenteredPartnerR574ToR446DifferenceSameObjectClosed = true

roundCenteredPartnerDoubleSlotKernelCompressionClosed : Bool
roundCenteredPartnerDoubleSlotKernelCompressionClosed = true

roundCenteredPartnerDoubleSlotKernelDifferenceClosed : Bool
roundCenteredPartnerDoubleSlotKernelDifferenceClosed = true

roundCenteredPartnerFixedOutputSlotQuotientNormalizationClosed : Bool
roundCenteredPartnerFixedOutputSlotQuotientNormalizationClosed = true

roundCenteredPartnerFixedOutputSlotDifferenceTelescopeClosed : Bool
roundCenteredPartnerFixedOutputSlotDifferenceTelescopeClosed = true

roundCenteredPartnerRadialPlueckerDefectWeldClosed : Bool
roundCenteredPartnerRadialPlueckerDefectWeldClosed = false

roundCenteredPartnerCenteredPairCellConstructed : Bool
roundCenteredPartnerCenteredPairCellConstructed = false

roundCenteredPartnerCutoffUniformAggregateClosed : Bool
roundCenteredPartnerCutoffUniformAggregateClosed = false

roundCenteredPartnerClayPromotion : Bool
roundCenteredPartnerClayPromotion = false

roundCenteredPartnerR205ToR574DifferenceSameObjectClosedIsTrue :
  roundCenteredPartnerR205ToR574DifferenceSameObjectClosed ≡ true
roundCenteredPartnerR205ToR574DifferenceSameObjectClosedIsTrue = refl

roundCenteredPartnerR574ToR446DifferenceSameObjectClosedIsTrue :
  roundCenteredPartnerR574ToR446DifferenceSameObjectClosed ≡ true
roundCenteredPartnerR574ToR446DifferenceSameObjectClosedIsTrue = refl

roundCenteredPartnerDoubleSlotKernelCompressionClosedIsTrue :
  roundCenteredPartnerDoubleSlotKernelCompressionClosed ≡ true
roundCenteredPartnerDoubleSlotKernelCompressionClosedIsTrue = refl

roundCenteredPartnerDoubleSlotKernelDifferenceClosedIsTrue :
  roundCenteredPartnerDoubleSlotKernelDifferenceClosed ≡ true
roundCenteredPartnerDoubleSlotKernelDifferenceClosedIsTrue = refl

roundCenteredPartnerFixedOutputSlotQuotientNormalizationClosedIsTrue :
  roundCenteredPartnerFixedOutputSlotQuotientNormalizationClosed ≡ true
roundCenteredPartnerFixedOutputSlotQuotientNormalizationClosedIsTrue = refl

roundCenteredPartnerFixedOutputSlotDifferenceTelescopeClosedIsTrue :
  roundCenteredPartnerFixedOutputSlotDifferenceTelescopeClosed ≡ true
roundCenteredPartnerFixedOutputSlotDifferenceTelescopeClosedIsTrue = refl

roundCenteredPartnerRadialPlueckerDefectWeldClosedIsFalse :
  roundCenteredPartnerRadialPlueckerDefectWeldClosed ≡ false
roundCenteredPartnerRadialPlueckerDefectWeldClosedIsFalse = refl

roundCenteredPartnerClayPromotionIsFalse :
  roundCenteredPartnerClayPromotion ≡ false
roundCenteredPartnerClayPromotionIsFalse = refl
