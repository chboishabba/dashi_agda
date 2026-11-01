module DASHI.Physics.Closure.NSTriadKNMixedHelicityQuarticFluxHomogeneityRound289Exact where

------------------------------------------------------------------------
-- ROUND289 / HOMOGENEITY AUDIT BEFORE PROMOTING THE TEMPORAL-FLUX ROUTE
--
-- R227's literal mixed-helicity output is quadratic in velocity:
--
--   M_k(u) = sum_{p+q=k} u_p^+ x u_q^- .
--
-- Hence its squared mass Q_k=||M_k||^2 and every same-time Gram cross term
-- between two R227 cells have amplitude degree four.
--
-- R230 gives the exact product-rule tangent for an arbitrary modal forcing G:
--
--   F_k^{+-}(u;G)
--     = sum [ G_p^+ x u_q^- - G_p^- x u_q^+ ].
--
-- If G is the quadratic Navier--Stokes nonlinearity N(u), then F^{+-} has
-- degree three and the forcing work Re<M,F^{+-}> has degree five.  If G is the
-- linear viscous forcing, F^{+-} has degree two and the corresponding work is
-- degree four.
--
-- BIDI CONSEQUENCE:
-- a bare quartic coherent Gram debt cannot be identified with the NONLINEAR
-- part of dQ/dt by homogeneity alone.  Any temporal route to R222 must either
--
--   * extract a quartic contribution from the linear/viscous tangent,
--   * use a phase functional with a scale/time weight changing homogeneity, or
--   * produce an integrated transfer/telescope identity whose endpoint object
--     is not simply a homogeneous quartic primitive.
--
-- This is a decision theorem, not a sign theorem.  It prevents R230/R233 from
-- being misread as an automatic flux representation of R179 Gram debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

mixedCellDegree : Nat
mixedCellDegree = 2

mixedOutputDegree : Nat
mixedOutputDegree = mixedCellDegree

gramDebtDegree : Nat
gramDebtDegree = mixedCellDegree + mixedCellDegree

companionMassDegree : Nat
companionMassDegree = mixedOutputDegree + mixedOutputDegree

viscousModalForcingDegree : Nat
viscousModalForcingDegree = 1

nonlinearModalForcingDegree : Nat
nonlinearModalForcingDegree = 2

mixedProductTangentDegree : Nat → Nat
mixedProductTangentDegree forcingDegree = forcingDegree + 1

mixedForcingWorkDegree : Nat → Nat
mixedForcingWorkDegree forcingDegree =
  mixedOutputDegree + mixedProductTangentDegree forcingDegree

gramDebtIsQuartic : gramDebtDegree ≡ 4
gramDebtIsQuartic = refl

companionMassIsQuartic : companionMassDegree ≡ 4
companionMassIsQuartic = refl

viscousMixedTangentIsQuadratic :
  mixedProductTangentDegree viscousModalForcingDegree ≡ 2
viscousMixedTangentIsQuadratic = refl

viscousMixedForcingWorkIsQuartic :
  mixedForcingWorkDegree viscousModalForcingDegree ≡ 4
viscousMixedForcingWorkIsQuartic = refl

nonlinearMixedTangentIsCubic :
  mixedProductTangentDegree nonlinearModalForcingDegree ≡ 3
nonlinearMixedTangentIsCubic = refl

nonlinearMixedForcingWorkIsQuintic :
  mixedForcingWorkDegree nonlinearModalForcingDegree ≡ 5
nonlinearMixedForcingWorkIsQuintic = refl

quarticGramDoesNotMatchNonlinearWorkDegree : Bool
quarticGramDoesNotMatchNonlinearWorkDegree = true

viscousWorkHasCompatibleQuarticDegree : Bool
viscousWorkHasCompatibleQuarticDegree = true

round289R230IsCorrectLiteralTangentOwner : Bool
round289R230IsCorrectLiteralTangentOwner = true

round289NaiveGramEqualsNonlinearFluxDerivativeRejected : Bool
round289NaiveGramEqualsNonlinearFluxDerivativeRejected = true

round289TemporalRouteStillPossibleWithWeightedOrViscousFlux : Bool
round289TemporalRouteStillPossibleWithWeightedOrViscousFlux = true

round289PointwiseSpatialRouteStillAvailable : Bool
round289PointwiseSpatialRouteStillAvailable = true

round289PackageAClosed : Bool
round289PackageAClosed = false

round289ClayPromotion : Bool
round289ClayPromotion = false

round289NaiveGramEqualsNonlinearFluxDerivativeRejectedIsTrue :
  round289NaiveGramEqualsNonlinearFluxDerivativeRejected ≡ true
round289NaiveGramEqualsNonlinearFluxDerivativeRejectedIsTrue = refl

round289PackageAClosedIsFalse : round289PackageAClosed ≡ false
round289PackageAClosedIsFalse = refl
