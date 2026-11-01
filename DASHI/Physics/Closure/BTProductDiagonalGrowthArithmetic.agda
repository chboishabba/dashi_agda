module DASHI.Physics.Closure.BTProductDiagonalGrowthArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

open import DASHI.Physics.Closure.BTBallVolumeArithmetic
  using
    ( pow
    ; T3xT2xT7SphereCount
    ; T3xT2xT7BallCount
    )

------------------------------------------------------------------------
-- Exact diagonal product growth for T3 x T2 x T7.
--
-- The exact columns below are literal product sphere/ball counts at
-- diagonal radius (r , r , r).  The envelope column is the asymptotic
-- surrogate 8 * 42^r.  This module records Nat arithmetic only; it does
-- not assert an inequality between the exact counts and the surrogate.

diagonalProductSphereCount :
  Nat →
  Nat
diagonalProductSphereCount r =
  T3xT2xT7SphereCount r r r

diagonalProductBallCount :
  Nat →
  Nat
diagonalProductBallCount r =
  T3xT2xT7BallCount r r r

diagonalEnvelopeBase :
  Nat
diagonalEnvelopeBase =
  42

diagonalEnvelopePrefactor :
  Nat
diagonalEnvelopePrefactor =
  8

diagonalEnvelope :
  Nat →
  Nat
diagonalEnvelope r =
  diagonalEnvelopePrefactor * pow diagonalEnvelopeBase r

record DiagonalGrowthRow : Set where
  field
    radius :
      Nat

    exactSphere :
      Nat

    exactSphereIsComputed :
      exactSphere ≡ diagonalProductSphereCount radius

    exactBall :
      Nat

    exactBallIsComputed :
      exactBall ≡ diagonalProductBallCount radius

    envelope :
      Nat

    envelopeIsComputed :
      envelope ≡ diagonalEnvelope radius

open DiagonalGrowthRow public

diagonalGrowthRow0 :
  DiagonalGrowthRow
diagonalGrowthRow0 =
  record
    { radius =
        0
    ; exactSphere =
        1
    ; exactSphereIsComputed =
        refl
    ; exactBall =
        1
    ; exactBallIsComputed =
        refl
    ; envelope =
        8
    ; envelopeIsComputed =
        refl
    }

diagonalGrowthRow1 :
  DiagonalGrowthRow
diagonalGrowthRow1 =
  record
    { radius =
        1
    ; exactSphere =
        96
    ; exactSphereIsComputed =
        refl
    ; exactBall =
        180
    ; exactBallIsComputed =
        refl
    ; envelope =
        336
    ; envelopeIsComputed =
        refl
    }

diagonalGrowthRow2 :
  DiagonalGrowthRow
diagonalGrowthRow2 =
  record
    { radius =
        2
    ; exactSphere =
        4032
    ; exactSphereIsComputed =
        refl
    ; exactBall =
        11050
    ; exactBallIsComputed =
        refl
    ; envelope =
        14112
    ; envelopeIsComputed =
        refl
    }

diagonalGrowthRow3 :
  DiagonalGrowthRow
diagonalGrowthRow3 =
  record
    { radius =
        3
    ; exactSphere =
        169344
    ; exactSphereIsComputed =
        refl
    ; exactBall =
        532862
    ; exactBallIsComputed =
        refl
    ; envelope =
        592704
    ; envelopeIsComputed =
        refl
    }

diagonalProductSphereR0Is1 :
  diagonalProductSphereCount 0 ≡ 1
diagonalProductSphereR0Is1 =
  refl

diagonalProductBallR0Is1 :
  diagonalProductBallCount 0 ≡ 1
diagonalProductBallR0Is1 =
  refl

diagonalEnvelopeR0Is8 :
  diagonalEnvelope 0 ≡ 8
diagonalEnvelopeR0Is8 =
  refl

diagonalProductSphereR1Is96 :
  diagonalProductSphereCount 1 ≡ 96
diagonalProductSphereR1Is96 =
  refl

diagonalProductBallR1Is180 :
  diagonalProductBallCount 1 ≡ 180
diagonalProductBallR1Is180 =
  refl

diagonalEnvelopeR1Is336 :
  diagonalEnvelope 1 ≡ 336
diagonalEnvelopeR1Is336 =
  refl

diagonalProductSphereR2Is4032 :
  diagonalProductSphereCount 2 ≡ 4032
diagonalProductSphereR2Is4032 =
  refl

diagonalProductBallR2Is11050 :
  diagonalProductBallCount 2 ≡ 11050
diagonalProductBallR2Is11050 =
  refl

diagonalEnvelopeR2Is14112 :
  diagonalEnvelope 2 ≡ 14112
diagonalEnvelopeR2Is14112 =
  refl

diagonalProductSphereR3Is169344 :
  diagonalProductSphereCount 3 ≡ 169344
diagonalProductSphereR3Is169344 =
  refl

diagonalProductBallR3Is532862 :
  diagonalProductBallCount 3 ≡ 532862
diagonalProductBallR3Is532862 =
  refl

diagonalEnvelopeR3Is592704 :
  diagonalEnvelope 3 ≡ 592704
diagonalEnvelopeR3Is592704 =
  refl
