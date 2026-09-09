module DASHI.Analysis.RiemannG2LiteralCellwiseNearUpperExact where

------------------------------------------------------------------------
-- LITERAL CELLWISE UPPERS -> GENERIC FINAL-NEAR UPPER
--
-- A numerical certificate does not need exact transcendental equality for each
-- literal zero cell.  For the certified RH route it is enough to prove a
-- one-sided enclosure
--
--   cellResponse sigma <= cellUpper sigma
--
-- over the exact finite enumeration.  Additive monotonicity then yields
--
--   nearResponseAt(J) <= fold(cellUpper).
--
-- This is strictly weaker and more executable than identifying a machine fold
-- exactly with the transcendental finite sum.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2GenericNearUpperClusterResponseCompilerExact as Generic

foldValues :
  forall {S : NearFar.OrderedAdditiveNearFarSurface} {Index : Set} ->
  NearFar.Scalar S ->
  (Index -> NearFar.Scalar S) ->
  List Index ->
  NearFar.Scalar S
foldValues {S = S} zero value [] = zero
foldValues {S = S} zero value (i ∷ is) =
  NearFar.add S (value i) (foldValues zero value is)

record LiteralNearEnumeration
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput) : Set₁ where
  field
    finalZero : NearFar.Scalar S
    literalIndices : List (Literal.ZeroIndex kernel)

    literalFiniteSumIsEnumeratedFold :
      Literal.finiteNearSum kernel (Literal.cellResponse kernel)
      ≡ foldValues finalZero (Literal.cellResponse kernel) literalIndices

    enumerationReference : String

open LiteralNearEnumeration public

record LiteralCellwiseUpper
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput)
    (enumeration : LiteralNearEnumeration offInput kernel) : Set₁ where
  field
    cellUpper : Literal.ZeroIndex kernel -> NearFar.Scalar S

    literalCellBelowUpper :
      (sigma : Literal.ZeroIndex kernel) ->
      NearFar._≤_ S
        (Literal.cellResponse kernel sigma)
        (cellUpper sigma)

    upperReference : String

open LiteralCellwiseUpper public

upperFold :
  forall {S transport offInput kernel enumeration} ->
  LiteralCellwiseUpper
    {S = S} {transport = transport}
    offInput kernel enumeration ->
  NearFar.Scalar S
upperFold {enumeration = enumeration} upper =
  foldValues
    (finalZero enumeration)
    (cellUpper upper)
    (literalIndices enumeration)

enumeratedExactFoldBelowUpperFold :
  forall {S transport offInput kernel enumeration} ->
  (upper : LiteralCellwiseUpper
    {S = S} {transport = transport}
    offInput kernel enumeration) ->
  (indices : List (Literal.ZeroIndex kernel)) ->
  NearFar._≤_ S
    (foldValues
      (finalZero enumeration)
      (Literal.cellResponse kernel)
      indices)
    (foldValues
      (finalZero enumeration)
      (cellUpper upper)
      indices)
enumeratedExactFoldBelowUpperFold
    {S = S} {offInput = offInput} {enumeration = enumeration}
    upper [] =
  Direct.sourceOrderReflexive offInput (finalZero enumeration)
enumeratedExactFoldBelowUpperFold
    {S = S} {offInput = offInput} {kernel = kernel}
    {enumeration = enumeration} upper (sigma ∷ rest) =
  NearFar.addMonotone S
    (literalCellBelowUpper upper sigma)
    (enumeratedExactFoldBelowUpperFold upper rest)

finalNearBelowCellwiseUpper :
  forall {S transport offInput kernel enumeration} ->
  (upper : LiteralCellwiseUpper
    {S = S} {transport = transport}
    offInput kernel enumeration) ->
  NearFar._≤_ S
    (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
    (upperFold upper)
finalNearBelowCellwiseUpper
    {S = S} {offInput = offInput} {kernel = kernel}
    {enumeration = enumeration} upper =
  subst
    (λ lower -> NearFar._≤_ S lower (upperFold upper))
    (sym finalNearIsEnumeratedFold)
    (enumeratedExactFoldBelowUpperFold upper (literalIndices enumeration))
  where
  finalNearIsEnumeratedFold :
    Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
    ≡ foldValues
        (finalZero enumeration)
        (Literal.cellResponse kernel)
        (literalIndices enumeration)
  finalNearIsEnumeratedFold =
    trans
      (Literal.finalNearResponseIsLiteralFiniteSum kernel)
      (literalFiniteSumIsEnumeratedFold enumeration)

compileCellwiseFinalNearUpper :
  forall {S transport offInput kernel enumeration} ->
  (upper : LiteralCellwiseUpper
    {S = S} {transport = transport}
    offInput kernel enumeration) ->
  Generic.FinalNearUpper offInput
compileCellwiseFinalNearUpper upper = record
  { Generic.upperValue = upperFold upper
  ; Generic.nearResponseBelowUpper = finalNearBelowCellwiseUpper upper
  ; Generic.upperReference = upperReference upper
  }

record LiteralCellwiseNearUpperBoundary : Set where
  constructor literal-cellwise-near-upper-boundary
  field
    exactTranscendentalCellEqualityRequired : Bool
    exactTranscendentalCellEqualityRequiredIsFalse :
      exactTranscendentalCellEqualityRequired ≡ false

    oneSidedCellEnclosuresSuffice : Bool
    oneSidedCellEnclosuresSufficeIsTrue :
      oneSidedCellEnclosuresSuffice ≡ true

    exactFiniteEnumerationSemanticsStillRequired : Bool
    exactFiniteEnumerationSemanticsStillRequiredIsTrue :
      exactFiniteEnumerationSemanticsStillRequired ≡ true

    finiteSumMonotonicityIsCompilerOutput : Bool
    finiteSumMonotonicityIsCompilerOutputIsTrue :
      finiteSumMonotonicityIsCompilerOutput ≡ true

    resultingNearUpperFeedsGenericClusterCompiler : Bool
    resultingNearUpperFeedsGenericClusterCompilerIsTrue :
      resultingNearUpperFeedsGenericClusterCompiler ≡ true

    strictClusterResponseMarginPaidHere : Bool
    strictClusterResponseMarginPaidHereIsFalse :
      strictClusterResponseMarginPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralCellwiseNearUpperBoundary : LiteralCellwiseNearUpperBoundary
canonicalLiteralCellwiseNearUpperBoundary =
  literal-cellwise-near-upper-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Prefer one-sided interval/cell certificates over exact transcendental machine equality. Once R1 and an exact list realization of the finite near kernel are available, prove each literal reflection-paired cell is below a certified upper. Finite additive monotonicity compiles nearResponseAt(J)<=fold(cellUpper), which feeds the implementation-neutral near-upper ClusterResponse compiler. The independent strict ClusterResponse margin remains the analytic theorem and RH is not derived here."
