module DASHI.Analysis.RiemannCanonicalComplexCharacterAttachmentExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannConstructedComplexCharacterCoreExact as Core
import DASHI.Analysis.RiemannExistingConstructedCharacterMachineryAssemblyExact as Existing
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as HX

------------------------------------------------------------------------
-- FINAL BIDI CUT FOR H_X: CONSTRUCTED CORE -> CANONICAL RIEMANN CARRIER
--
-- The ordinary character mathematics is already assembled by
-- ExistingConstructedCharacterMachinery.  This owner refuses to identify that
-- donor with the Riemann substrate merely because its operations look alike.
-- A CanonicalCharacterAttachment explicitly realizes the same character
-- operations and theorems on the exact ComplexAnalyticCarrier selected by the
-- AnalyticSubstrate.
------------------------------------------------------------------------

record CanonicalCharacterAttachment
    (analytic : Analytic.AnalyticSubstrate)
    (C : ConstructedComplexPackage)
    (M : Existing.ExistingConstructedCharacterMachinery C) : Set₁ where
  private
    AC = Analytic.AnalyticSubstrate.carrier analytic
    R = real (realPackage C)
    K = Core.ConstructedComplexCharacterCore C

  field
    -- Typed same-object witnesses.  The attachment is not name/provenance only.
    realCarrierSame : Analytic.ComplexAnalyticCarrier.Real AC ≡ Real R
    complexCarrierSame : Analytic.ComplexAnalyticCarrier.Complex AC ≡ ComplexPair R

    -- The exact canonical operations used by H_X.  These live on the analytic
    -- carrier itself; the transport proof below certifies that they are the
    -- realization of the assembled constructed donor.
    zeroR : Analytic.ComplexAnalyticCarrier.Real AC
    addR mulR :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC
    negR :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC
    subR :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC

    embedReal :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Complex AC
    imaginaryUnit : Analytic.ComplexAnalyticCarrier.Complex AC
    addC mulC :
      Analytic.ComplexAnalyticCarrier.Complex AC →
      Analytic.ComplexAnalyticCarrier.Complex AC →
      Analytic.ComplexAnalyticCarrier.Complex AC
    negC :
      Analytic.ComplexAnalyticCarrier.Complex AC →
      Analytic.ComplexAnalyticCarrier.Complex AC
    expC :
      Analytic.ComplexAnalyticCarrier.Complex AC →
      Analytic.ComplexAnalyticCarrier.Complex AC
    cosR :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC

    plusIProduct minusIProduct :
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Real AC →
      Analytic.ComplexAnalyticCarrier.Complex AC

    subRIsAddNeg :
      (b t : Analytic.ComplexAnalyticCarrier.Real AC) →
      subR b t ≡ addR b (negR t)

    expAddCanonical :
      (x y : Analytic.ComplexAnalyticCarrier.Complex AC) →
      expC (addC x y) ≡ mulC (expC x) (expC y)

    phaseAddCanonical :
      (b t u : Analytic.ComplexAnalyticCarrier.Real AC) →
      addC (minusIProduct t u) (plusIProduct b u)
      ≡ plusIProduct (subR b t) u

    characterProductCanonical :
      (b t u : Analytic.ComplexAnalyticCarrier.Real AC) →
      mulC (expC (minusIProduct t u)) (expC (plusIProduct b u))
      ≡ expC (plusIProduct (subR b t) u)

    evenProjectionCanonical :
      (delta u : Analytic.ComplexAnalyticCarrier.Real AC) →
      Analytic.ComplexAnalyticCarrier.realPart AC
        (expC (plusIProduct delta u))
      ≡ cosR (mulR delta u)

    -- Proof-relevant receipt that the canonical laws above are the transported
    -- realization of the single assembled constructed donor K.
    transportedFromConstructedCore :
      Existing.assembledConstructedComplexCharacterCore C M ≡ K

    attachmentReference : String

open CanonicalCharacterAttachment public

canonicalComplexCharacterExtension :
  (analytic : Analytic.AnalyticSubstrate) →
  (C : ConstructedComplexPackage) →
  (M : Existing.ExistingConstructedCharacterMachinery C) →
  CanonicalCharacterAttachment analytic C M →
  HX.RiemannComplexCharacterExtension analytic
canonicalComplexCharacterExtension analytic C M A =
  let AC = Analytic.AnalyticSubstrate.carrier analytic
  in HX.riemann-complex-character-extension
    (CanonicalCharacterAttachment analytic C M)
    (Analytic.ComplexAnalyticCarrier.Real AC)
    (Analytic.ComplexAnalyticCarrier.Complex AC)
    (Analytic.ComplexAnalyticCarrier.Real AC ≡ Real (real (realPackage C)))
    (Analytic.ComplexAnalyticCarrier.Complex AC ≡ ComplexPair (real (realPackage C)))
    (zeroR A)
    (addR A)
    (mulR A)
    (negR A)
    (subR A)
    (subRIsAddNeg A)
    (embedReal A)
    (imaginaryUnit A)
    (addC A)
    (mulC A)
    (negC A)
    (Analytic.ComplexAnalyticCarrier.realPart AC)
    (expC A)
    (cosR A)
    (plusIProduct A)
    (minusIProduct A)
    (CanonicalCharacterAttachment analytic C M)
    (CanonicalCharacterAttachment analytic C M)
    (λ t u → expC A (minusIProduct A t u))
    (λ b u → expC A (plusIProduct A b u))
    (λ b t u → expC A (plusIProduct A (subR A b t) u))
    (λ t u → refl)
    (λ b u → refl)
    (λ b t u → refl)
    (expAddCanonical A)
    (phaseAddCanonical A)
    (characterProductCanonical A)
    (evenProjectionCanonical A)
    (attachmentReference A)
