module DASHI.Physics.Closure.NSAdjacentOnlyFormalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Formal adjacent-only Navier-Stokes projection receipt.
--
-- This receipt makes explicit the finite carrier arithmetic used by the
-- adjacent-only diagnostic.  Cross-base and non-adjacent same-base terms are
-- zero by projection.  The adjacent/non-adjacent split itself is a proved
-- finite arithmetic fact about the three checked band indices, not a
-- assumed analytic estimate.  No Clay, terminal, or global regularity
-- promotion is introduced here.

data NSPrimeBase : Set where
  base2 :
    NSPrimeBase

  base3 :
    NSPrimeBase

  base5 :
    NSPrimeBase

canonicalNSPrimeBases :
  List NSPrimeBase
canonicalNSPrimeBases =
  base2
  ∷ base3
  ∷ base5
  ∷ []

data NSBand : Set where
  band0 :
    NSBand

  band1 :
    NSBand

  band2 :
    NSBand

canonicalNSBands :
  List NSBand
canonicalNSBands =
  band0
  ∷ band1
  ∷ band2
  ∷ []

data SameBase : NSPrimeBase → NSPrimeBase → Set where
  sameBase2 :
    SameBase base2 base2

  sameBase3 :
    SameBase base3 base3

  sameBase5 :
    SameBase base5 base5

data CrossBase : NSPrimeBase → NSPrimeBase → Set where
  cross23 :
    CrossBase base2 base3

  cross25 :
    CrossBase base2 base5

  cross32 :
    CrossBase base3 base2

  cross35 :
    CrossBase base3 base5

  cross52 :
    CrossBase base5 base2

  cross53 :
    CrossBase base5 base3

data AdjacentBand : NSBand → NSBand → Set where
  adjacent01 :
    AdjacentBand band0 band1

  adjacent10 :
    AdjacentBand band1 band0

  adjacent12 :
    AdjacentBand band1 band2

  adjacent21 :
    AdjacentBand band2 band1

data NonAdjacentSameBand : NSBand → NSBand → Set where
  nonAdjacent00 :
    NonAdjacentSameBand band0 band0

  nonAdjacent02 :
    NonAdjacentSameBand band0 band2

  nonAdjacent11 :
    NonAdjacentSameBand band1 band1

  nonAdjacent20 :
    NonAdjacentSameBand band2 band0

  nonAdjacent22 :
    NonAdjacentSameBand band2 band2

data ProjectedStretchingCoefficient : Set where
  zeroCoefficient :
    ProjectedStretchingCoefficient

  adjacentCoefficient :
    ProjectedStretchingCoefficient

projectedStretching :
  NSPrimeBase →
  NSPrimeBase →
  NSBand →
  NSBand →
  ProjectedStretchingCoefficient
projectedStretching base2 base2 band0 band1 =
  adjacentCoefficient
projectedStretching base2 base2 band1 band0 =
  adjacentCoefficient
projectedStretching base2 base2 band1 band2 =
  adjacentCoefficient
projectedStretching base2 base2 band2 band1 =
  adjacentCoefficient
projectedStretching base3 base3 band0 band1 =
  adjacentCoefficient
projectedStretching base3 base3 band1 band0 =
  adjacentCoefficient
projectedStretching base3 base3 band1 band2 =
  adjacentCoefficient
projectedStretching base3 base3 band2 band1 =
  adjacentCoefficient
projectedStretching base5 base5 band0 band1 =
  adjacentCoefficient
projectedStretching base5 base5 band1 band0 =
  adjacentCoefficient
projectedStretching base5 base5 band1 band2 =
  adjacentCoefficient
projectedStretching base5 base5 band2 band1 =
  adjacentCoefficient
projectedStretching _ _ _ _ =
  zeroCoefficient

crossBaseProjectionZero :
  {p q : NSPrimeBase} →
  {m n : NSBand} →
  CrossBase p q →
  projectedStretching p q m n ≡ zeroCoefficient
crossBaseProjectionZero {m = band0} {n = band0} cross23 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross23 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross23 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross23 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross23 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross23 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross23 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross23 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross23 = refl
crossBaseProjectionZero {m = band0} {n = band0} cross25 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross25 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross25 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross25 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross25 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross25 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross25 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross25 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross25 = refl
crossBaseProjectionZero {m = band0} {n = band0} cross32 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross32 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross32 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross32 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross32 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross32 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross32 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross32 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross32 = refl
crossBaseProjectionZero {m = band0} {n = band0} cross35 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross35 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross35 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross35 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross35 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross35 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross35 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross35 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross35 = refl
crossBaseProjectionZero {m = band0} {n = band0} cross52 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross52 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross52 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross52 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross52 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross52 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross52 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross52 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross52 = refl
crossBaseProjectionZero {m = band0} {n = band0} cross53 = refl
crossBaseProjectionZero {m = band0} {n = band1} cross53 = refl
crossBaseProjectionZero {m = band0} {n = band2} cross53 = refl
crossBaseProjectionZero {m = band1} {n = band0} cross53 = refl
crossBaseProjectionZero {m = band1} {n = band1} cross53 = refl
crossBaseProjectionZero {m = band1} {n = band2} cross53 = refl
crossBaseProjectionZero {m = band2} {n = band0} cross53 = refl
crossBaseProjectionZero {m = band2} {n = band1} cross53 = refl
crossBaseProjectionZero {m = band2} {n = band2} cross53 = refl

nonAdjacentSameBaseProjectionZero :
  {p q : NSPrimeBase} →
  {m n : NSBand} →
  SameBase p q →
  NonAdjacentSameBand m n →
  projectedStretching p q m n ≡ zeroCoefficient
nonAdjacentSameBaseProjectionZero sameBase2 nonAdjacent00 = refl
nonAdjacentSameBaseProjectionZero sameBase2 nonAdjacent02 = refl
nonAdjacentSameBaseProjectionZero sameBase2 nonAdjacent11 = refl
nonAdjacentSameBaseProjectionZero sameBase2 nonAdjacent20 = refl
nonAdjacentSameBaseProjectionZero sameBase2 nonAdjacent22 = refl
nonAdjacentSameBaseProjectionZero sameBase3 nonAdjacent00 = refl
nonAdjacentSameBaseProjectionZero sameBase3 nonAdjacent02 = refl
nonAdjacentSameBaseProjectionZero sameBase3 nonAdjacent11 = refl
nonAdjacentSameBaseProjectionZero sameBase3 nonAdjacent20 = refl
nonAdjacentSameBaseProjectionZero sameBase3 nonAdjacent22 = refl
nonAdjacentSameBaseProjectionZero sameBase5 nonAdjacent00 = refl
nonAdjacentSameBaseProjectionZero sameBase5 nonAdjacent02 = refl
nonAdjacentSameBaseProjectionZero sameBase5 nonAdjacent11 = refl
nonAdjacentSameBaseProjectionZero sameBase5 nonAdjacent20 = refl
nonAdjacentSameBaseProjectionZero sameBase5 nonAdjacent22 = refl

nonAdjacentIsNotAdjacent :
  {m n : NSBand} →
  NonAdjacentSameBand m n →
  AdjacentBand m n →
  ⊥
nonAdjacentIsNotAdjacent nonAdjacent00 ()
nonAdjacentIsNotAdjacent nonAdjacent02 ()
nonAdjacentIsNotAdjacent nonAdjacent11 ()
nonAdjacentIsNotAdjacent nonAdjacent20 ()
nonAdjacentIsNotAdjacent nonAdjacent22 ()

adjacentSameBaseSurvivesProjection :
  {p q : NSPrimeBase} →
  {m n : NSBand} →
  SameBase p q →
  AdjacentBand m n →
  projectedStretching p q m n ≡ adjacentCoefficient
adjacentSameBaseSurvivesProjection sameBase2 adjacent01 = refl
adjacentSameBaseSurvivesProjection sameBase2 adjacent10 = refl
adjacentSameBaseSurvivesProjection sameBase2 adjacent12 = refl
adjacentSameBaseSurvivesProjection sameBase2 adjacent21 = refl
adjacentSameBaseSurvivesProjection sameBase3 adjacent01 = refl
adjacentSameBaseSurvivesProjection sameBase3 adjacent10 = refl
adjacentSameBaseSurvivesProjection sameBase3 adjacent12 = refl
adjacentSameBaseSurvivesProjection sameBase3 adjacent21 = refl
adjacentSameBaseSurvivesProjection sameBase5 adjacent01 = refl
adjacentSameBaseSurvivesProjection sameBase5 adjacent10 = refl
adjacentSameBaseSurvivesProjection sameBase5 adjacent12 = refl
adjacentSameBaseSurvivesProjection sameBase5 adjacent21 = refl

data AdjacentOnlyArithmeticConstraint : Set where
  finiteThreeBandArithmeticConstraint :
    (({p q : NSPrimeBase} →
      {m n : NSBand} →
      SameBase p q →
      AdjacentBand m n →
      projectedStretching p q m n ≡ adjacentCoefficient) →
     ({m n : NSBand} →
      NonAdjacentSameBand m n →
      AdjacentBand m n →
      ⊥) →
     AdjacentOnlyArithmeticConstraint)

arithmeticConstraintOnVortexStretchingResult :
  AdjacentOnlyArithmeticConstraint
arithmeticConstraintOnVortexStretchingResult =
  finiteThreeBandArithmeticConstraint
    adjacentSameBaseSurvivesProjection
    nonAdjacentIsNotAdjacent

data NSAdjacentOnlyFormalStatus : Set where
  adjacentOnlyImportedDiagnosticAccepted :
    NSAdjacentOnlyFormalStatus

  crossBaseTermsProjectedToZero :
    NSAdjacentOnlyFormalStatus

  nonAdjacentSameBaseTermsProjectedToZero :
    NSAdjacentOnlyFormalStatus

  finiteThreeBandArithmeticConstraintProved :
    NSAdjacentOnlyFormalStatus

  primeLPExactInvarianceStillObstructed :
    NSAdjacentOnlyFormalStatus

  noNSPromotion :
    NSAdjacentOnlyFormalStatus

canonicalNSAdjacentOnlyFormalStatus :
  List NSAdjacentOnlyFormalStatus
canonicalNSAdjacentOnlyFormalStatus =
  adjacentOnlyImportedDiagnosticAccepted
  ∷ crossBaseTermsProjectedToZero
  ∷ nonAdjacentSameBaseTermsProjectedToZero
  ∷ finiteThreeBandArithmeticConstraintProved
  ∷ primeLPExactInvarianceStillObstructed
  ∷ noNSPromotion
  ∷ []

data NSAdjacentOnlyFormalPromotion : Set where

nsAdjacentOnlyFormalPromotionImpossibleHere :
  NSAdjacentOnlyFormalPromotion →
  ⊥
nsAdjacentOnlyFormalPromotionImpossibleHere ()

nsAdjacentOnlyFormalStatement : String
nsAdjacentOnlyFormalStatement =
  "NS adjacent-only formal receipt: same-base adjacent bands survive the carrier projection; cross-base and non-adjacent same-base terms are zero by projection; the finite three-band adjacent/non-adjacent split is proved arithmetically; Clay, terminal, and global regularity promotions remain false."

record NSAdjacentOnlyFormalReceipt : Setω where
  field
    exactPrimeLPInvarianceStillObstructed :
      Bool

    exactPrimeLPInvarianceStillObstructedIsTrue :
      exactPrimeLPInvarianceStillObstructed ≡ true

    exactCommutationStillAbsent :
      Bool

    exactCommutationStillAbsentIsTrue :
      exactCommutationStillAbsent ≡ true

    bases :
      List NSPrimeBase

    basesAreCanonical :
      bases ≡ canonicalNSPrimeBases

    bands :
      List NSBand

    bandsAreCanonical :
      bands ≡ canonicalNSBands

    status :
      List NSAdjacentOnlyFormalStatus

    statusIsCanonical :
      status ≡ canonicalNSAdjacentOnlyFormalStatus

    adjacentOnlyVortexStretching :
      Bool

    adjacentOnlyVortexStretchingIsTrue :
      adjacentOnlyVortexStretching ≡ true

    crossBaseInteractionsZeroByProjection :
      Bool

    crossBaseInteractionsZeroByProjectionIsTrue :
      crossBaseInteractionsZeroByProjection ≡ true

    crossBaseProjectionTheorem :
      {p q : NSPrimeBase} →
      {m n : NSBand} →
      CrossBase p q →
      projectedStretching p q m n ≡ zeroCoefficient

    nonAdjacentSameBaseZeroByProjection :
      Bool

    nonAdjacentSameBaseZeroByProjectionIsTrue :
      nonAdjacentSameBaseZeroByProjection ≡ true

    nonAdjacentSameBaseProjectionTheorem :
      {p q : NSPrimeBase} →
      {m n : NSBand} →
      SameBase p q →
      NonAdjacentSameBand m n →
      projectedStretching p q m n ≡ zeroCoefficient

    arithmeticConstraintOnVortexStretching :
      Bool

    arithmeticConstraintOnVortexStretchingIsTrue :
      arithmeticConstraintOnVortexStretching ≡ true

    arithmeticConstraintWitness :
      AdjacentOnlyArithmeticConstraint

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsAdjacentOnlyFormalStatement

    promotionFlags :
      List NSAdjacentOnlyFormalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSAdjacentOnlyFormalReceipt public

canonicalNSAdjacentOnlyFormalReceipt :
  NSAdjacentOnlyFormalReceipt
canonicalNSAdjacentOnlyFormalReceipt =
  record
    { exactPrimeLPInvarianceStillObstructed =
        true
    ; exactPrimeLPInvarianceStillObstructedIsTrue =
        refl
    ; exactCommutationStillAbsent =
        true
    ; exactCommutationStillAbsentIsTrue =
        refl
    ; bases =
        canonicalNSPrimeBases
    ; basesAreCanonical =
        refl
    ; bands =
        canonicalNSBands
    ; bandsAreCanonical =
        refl
    ; status =
        canonicalNSAdjacentOnlyFormalStatus
    ; statusIsCanonical =
        refl
    ; adjacentOnlyVortexStretching =
        true
    ; adjacentOnlyVortexStretchingIsTrue =
        refl
    ; crossBaseInteractionsZeroByProjection =
        true
    ; crossBaseInteractionsZeroByProjectionIsTrue =
        refl
    ; crossBaseProjectionTheorem =
        crossBaseProjectionZero
    ; nonAdjacentSameBaseZeroByProjection =
        true
    ; nonAdjacentSameBaseZeroByProjectionIsTrue =
        refl
    ; nonAdjacentSameBaseProjectionTheorem =
        nonAdjacentSameBaseProjectionZero
    ; arithmeticConstraintOnVortexStretching =
        true
    ; arithmeticConstraintOnVortexStretchingIsTrue =
        refl
    ; arithmeticConstraintWitness =
        arithmeticConstraintOnVortexStretchingResult
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; statement =
        nsAdjacentOnlyFormalStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "adjacentOnlyVortexStretching=true is recorded and fixed in this receipt"
        ∷ "crossBaseInteractionsZeroByProjection=true with an explicit finite projection theorem"
        ∷ "nonAdjacentSameBaseZeroByProjection=true with an explicit finite projection theorem"
        ∷ "arithmeticConstraintOnVortexStretching=true is witnessed by the finite three-band adjacent/non-adjacent arithmetic result"
        ∷ "Prime-LP exact flow invariance and exact commutation remain obstructed"
        ∷ "Clay, terminal, and global regularity promotions remain false"
        ∷ []
    }

adjacentOnlyVortexStretchingTrue :
  adjacentOnlyVortexStretching canonicalNSAdjacentOnlyFormalReceipt ≡ true
adjacentOnlyVortexStretchingTrue =
  refl

crossBaseInteractionsZeroByProjectionTrue :
  crossBaseInteractionsZeroByProjection canonicalNSAdjacentOnlyFormalReceipt ≡ true
crossBaseInteractionsZeroByProjectionTrue =
  refl

nonAdjacentSameBaseZeroByProjectionTrue :
  nonAdjacentSameBaseZeroByProjection canonicalNSAdjacentOnlyFormalReceipt ≡ true
nonAdjacentSameBaseZeroByProjectionTrue =
  refl

arithmeticConstraintOnVortexStretchingTrue :
  arithmeticConstraintOnVortexStretching canonicalNSAdjacentOnlyFormalReceipt ≡ true
arithmeticConstraintOnVortexStretchingTrue =
  refl

nsAdjacentOnlyClayStillFalse :
  clayNavierStokesPromoted canonicalNSAdjacentOnlyFormalReceipt ≡ false
nsAdjacentOnlyClayStillFalse =
  refl

nsAdjacentOnlyTerminalStillFalse :
  terminalClaimPromoted canonicalNSAdjacentOnlyFormalReceipt ≡ false
nsAdjacentOnlyTerminalStillFalse =
  refl

nsAdjacentOnlyGlobalRegularityStillFalse :
  globalRegularityPromoted canonicalNSAdjacentOnlyFormalReceipt ≡ false
nsAdjacentOnlyGlobalRegularityStillFalse =
  refl

nsAdjacentOnlyNoPromotion :
  NSAdjacentOnlyFormalPromotion →
  ⊥
nsAdjacentOnlyNoPromotion =
  nsAdjacentOnlyFormalPromotionImpossibleHere
