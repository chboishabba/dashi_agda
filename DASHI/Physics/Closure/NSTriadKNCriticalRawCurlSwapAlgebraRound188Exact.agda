module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlSwapAlgebraRound188Exact where

------------------------------------------------------------------------
-- ROUND188 / p/q SWAP ALGEBRA FOR THE COMPLETE RAW-CURL PRODUCTION
--
-- The physical trilinear amplitudes are alternating in the p/q slots.  Under
-- p/q swap the raw-curl slot triple therefore transforms schematically as
--
--   (C_k , C_p , C_q) -> (-C_k , -C_q , -C_p),
--
-- while (r_p,r_q) are exchanged.  This file proves the exact scalar algebra
-- resulting from that transformation.
--
-- The key conclusion is a NO-GO for a tempting static shortcut:
--
--   P_raw(k,q,p ; -C_k,-C_q,-C_p)
--     = P_raw(k,p,q ; C_k,C_p,C_q).
--
-- Thus the complete critical raw-curl production is SWAP-INVARIANT, not
-- antisymmetric.  Pairing the two ordered representatives doubles this full
-- production; it does not cancel it.  Any arbitrary-data gain must therefore
-- come from the internal double-commutator / trajectory structure rather than
-- from treating p/q swap as a sign cancellation of the full production.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlRadialGapRound169Exact as R169

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  neg : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  neg {F = F} x = C3.negate F x

rawCurlGapProductionSwapInvariant :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq ck cp cq : C3.Carrier F) →
  R169.rawCurlGapProduction rk rq rp (neg ck) (neg cq) (neg cp)
  ≡ R169.rawCurlGapProduction rk rp rq ck cp cq
rawCurlGapProductionSwapInvariant {F = F} rk rp rq ck cp cq =
  S.solve 6
    (λ rk rp rq ck cp cq →
      (((rq S.⊕ (S.⊝ rp)) S.⊗ (S.⊝ ck))
        S.⊕
        (((rp S.⊕ (S.⊝ rk)) S.⊗ (S.⊝ cq))
          S.⊕ ((rk S.⊕ (S.⊝ rq)) S.⊗ (S.⊝ cp))))
      S.⊜
      (((rp S.⊕ (S.⊝ rq)) S.⊗ ck)
        S.⊕
        (((rq S.⊕ (S.⊝ rk)) S.⊗ cp)
          S.⊕ ((rk S.⊕ (S.⊝ rp)) S.⊗ cq))))
    refl rk rp rq ck cp cq
  where module S = Field.Solver F

pairedRawCurlGapProductionDoubles :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq ck cp cq : C3.Carrier F) →
  C3.add F
    (R169.rawCurlGapProduction rk rp rq ck cp cq)
    (R169.rawCurlGapProduction rk rq rp (neg ck) (neg cq) (neg cp))
  ≡ C3.add F
      (R169.rawCurlGapProduction rk rp rq ck cp cq)
      (R169.rawCurlGapProduction rk rp rq ck cp cq)
pairedRawCurlGapProductionDoubles {F = F} rk rp rq ck cp cq
  rewrite rawCurlGapProductionSwapInvariant rk rp rq ck cp cq = refl

-- The two Round174 owners may still be useful internally, but the full swap
-- orbit itself supplies no cancellation token.
round188FullRawCurlProductionSwapAntisymmetric : Bool
round188FullRawCurlProductionSwapAntisymmetric = false

round188FullRawCurlProductionSwapInvariant : Bool
round188FullRawCurlProductionSwapInvariant = true

round188PairingFullProductionCancels : Bool
round188PairingFullProductionCancels = false

round188TrajectoryOrInternalCommutatorStillRequired : Bool
round188TrajectoryOrInternalCommutatorStillRequired = true

round188PackageAClosed : Bool
round188PackageAClosed = false

round188ClayPromotion : Bool
round188ClayPromotion = false
