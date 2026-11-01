module DASHI.Base369Monster3BRegularResidualValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as Character
import DASHI.Moonshine.Monster3BLiteralThreePhaseRegularResidualBidiExact as Literal

characterBulkExact :
  Character.RegularC3ResidualBoundary.characterRegularBulkIsExact
    Character.canonicalRegularC3ResidualBoundary ≡ true
characterBulkExact = refl

characterResidualExact :
  Character.RegularC3ResidualBoundary.characterResidual53Exact
    Character.canonicalRegularC3ResidualBoundary ≡ true
characterResidualExact = refl

characterDoesNotCreateSubmodule :
  Character.RegularC3ResidualBoundary.characterEqualityAloneCreatesSubmodule
    Character.canonicalRegularC3ResidualBoundary ≡ false
characterDoesNotCreateSubmodule = refl

literalThreePhasesSameCentralAction :
  Literal.LiteralThreePhaseResidualBoundary.allThreeLiteralPhaseFibresUseSameCentralAction
    Literal.canonicalLiteralThreePhaseResidualBoundary ≡ true
literalThreePhasesSameCentralAction = refl

fixedRegularRecognitionStillLive :
  Literal.LiteralThreePhaseResidualBoundary.fixedRegular729Times90RecognitionIsLive
    Literal.canonicalLiteralThreePhaseResidualBoundary ≡ true
fixedRegularRecognitionStillLive = refl

fixedResidualComplementStillLive :
  Literal.LiteralThreePhaseResidualBoundary.fixedResidual53ComplementIsLive
    Literal.canonicalLiteralThreePhaseResidualBoundary ≡ true
fixedResidualComplementStillLive = refl

albertNotInferredFromDimension :
  Literal.LiteralThreePhaseResidualBoundary.residual53IsAlbertByDimension
    Literal.canonicalLiteralThreePhaseResidualBoundary ≡ false
albertNotInferredFromDimension = refl
