module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityFirstOrderExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Gate-I needs the nonidentity principal-log expansion in the SAME
-- trivialization and coordinate carrier consumed by equation (0.11)/(0.12).
-- This module deliberately does not manufacture a second derivative.  The
-- source derivative J_G and the source remainder r_G are carried vertically
-- through the coordinate map.  The only algebra below is the exact
-- same-object collapse from the literal principal-log increment to
--
--   coords(log(G exp xi))
--     = coords(log G) + coords(J_G xi) + coords(r_G xi).
--
-- The analytic leaf remains the local first-order expansion of principal log
-- at the selected nonidentity G.  Once supplied, no later coordinate/norm seam
-- remains: the exact same remainder is exposed to the Federbush producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record NonidentityPrincipalLogFirstOrderData
    (Lie GroupLog Coord : Set) : Set₁ where
  field
    addLog : GroupLog → GroupLog → GroupLog
    addCoord : Coord → Coord → Coord
    coords : GroupLog → Coord

    GLog : GroupLog
    principalLogAfterRightExp : Lie → GroupLog
    JG : Lie → GroupLog
    remainder : Lie → GroupLog

    principalLogFirstOrderExact : ∀ xi →
      principalLogAfterRightExp xi
      ≡ addLog (addLog GLog (JG xi)) (remainder xi)

    coordsAdd : ∀ x y →
      coords (addLog x y) ≡ addCoord (coords x) (coords y)

open NonidentityPrincipalLogFirstOrderData public

principalLogNonidentityCoordinateExpansionExact :
  ∀ {Lie GroupLog Coord}
    (data : NonidentityPrincipalLogFirstOrderData Lie GroupLog Coord)
    (xi : Lie) →
  coords data (principalLogAfterRightExp data xi)
  ≡ addCoord data
      (addCoord data (coords data (GLog data)) (coords data (JG data xi)))
      (coords data (remainder data xi))
principalLogNonidentityCoordinateExpansionExact data xi
  with principalLogFirstOrderExact data xi
     | coordsAdd data (addLog data (GLog data) (JG data xi)) (remainder data xi)
     | coordsAdd data (GLog data) (JG data xi)
... | refl | refl | refl = refl

record CoordinateLittleOAtZero
    (Lie Coord Magnitude : Set) : Set₁ where
  field
    inputMagnitude : Lie → Magnitude
    outputMagnitude : Coord → Magnitude
    LittleO : (Lie → Coord) → Set

open CoordinateLittleOAtZero public

record NonidentityPrincipalLogCoordinateProducer
    (Lie GroupLog Coord Magnitude : Set) : Set₂ where
  field
    firstOrder : NonidentityPrincipalLogFirstOrderData Lie GroupLog Coord
    asymptotics : CoordinateLittleOAtZero Lie Coord Magnitude
    coordinateRemainderLittleO :
      LittleO asymptotics (λ xi → coords firstOrder (remainder firstOrder xi))

open NonidentityPrincipalLogCoordinateProducer public

principalLogNonidentityCoordinateRemainderLittleO :
  ∀ {Lie GroupLog Coord Magnitude}
    (producer : NonidentityPrincipalLogCoordinateProducer
      Lie GroupLog Coord Magnitude) →
  LittleO (asymptotics producer)
    (λ xi → coords (firstOrder producer)
      (remainder (firstOrder producer) xi))
principalLogNonidentityCoordinateRemainderLittleO producer =
  coordinateRemainderLittleO producer

-- Left-trivialized printed conventions are represented by supplying the
-- corresponding literal map in principalLogAfterRightExp and the matching JG.
-- This avoids an unsafe theorem that silently identifies left and right
-- trivializations at nonidentity G.

cmp109PrincipalLogNonidentitySameCoordinateLevel : ProofLevel
cmp109PrincipalLogNonidentitySameCoordinateLevel = machineChecked

cmp109PrincipalLogNonidentityAnalyticProducerLevel : ProofLevel
cmp109PrincipalLogNonidentityAnalyticProducerLevel = conditional
