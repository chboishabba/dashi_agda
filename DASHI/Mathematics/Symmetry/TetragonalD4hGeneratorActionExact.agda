module DASHI.Mathematics.Symmetry.TetragonalD4hGeneratorActionExact where

-- Exact finite action of tetragonal generators on four equatorial
-- directions at two heights.  This is a faithful geometric
-- eight-site action of D4 x C2, but faithfulness and the
-- abstract group isomorphism are not yet kernel theorems here.
-- In particular, this is not an experimentally identified lattice.

open import Agda.Builtin.Equality using (_≡_; refl)

data Direction : Set where
  north east south west : Direction

data Height : Set where
  above below : Height

record Site : Set where
  constructor site
  field
    direction : Direction
    height : Height
open Site public

quarter : Direction → Direction
quarter north = east
quarter east = south
quarter south = west
quarter west = north

mirror : Direction → Direction
mirror north = north
mirror east = west
mirror south = south
mirror west = east

flip : Height → Height
flip above = below
flip below = above

quarter4 : (d : Direction) →
  quarter (quarter (quarter (quarter d))) ≡ d
quarter4 north = refl
quarter4 east = refl
quarter4 south = refl
quarter4 west = refl

mirror2 : (d : Direction) → mirror (mirror d) ≡ d
mirror2 north = refl
mirror2 east = refl
mirror2 south = refl
mirror2 west = refl

dihedralRelation : (d : Direction) →
  mirror (quarter (mirror d))
  ≡ quarter (quarter (quarter d))
dihedralRelation north = refl
dihedralRelation east = refl
dihedralRelation south = refl
dihedralRelation west = refl

flip2 : (h : Height) → flip (flip h) ≡ h
flip2 above = refl
flip2 below = refl

R : Site → Site
R (site d h) = site (quarter d) h

S : Site → Site
S (site d h) = site (mirror d) h

H : Site → Site
H (site d h) = site d (flip h)

R4 : (p : Site) → R (R (R (R p))) ≡ p
R4 (site north above) = refl
R4 (site east above) = refl
R4 (site south above) = refl
R4 (site west above) = refl
R4 (site north below) = refl
R4 (site east below) = refl
R4 (site south below) = refl
R4 (site west below) = refl

S2 : (p : Site) → S (S p) ≡ p
S2 (site north above) = refl
S2 (site east above) = refl
S2 (site south above) = refl
S2 (site west above) = refl
S2 (site north below) = refl
S2 (site east below) = refl
S2 (site south below) = refl
S2 (site west below) = refl

H2 : (p : Site) → H (H p) ≡ p
H2 (site north above) = refl
H2 (site east above) = refl
H2 (site south above) = refl
H2 (site west above) = refl
H2 (site north below) = refl
H2 (site east below) = refl
H2 (site south below) = refl
H2 (site west below) = refl

SRS : (p : Site) → S (R (S p)) ≡ R (R (R p))
SRS (site north above) = refl
SRS (site east above) = refl
SRS (site south above) = refl
SRS (site west above) = refl
SRS (site north below) = refl
SRS (site east below) = refl
SRS (site south below) = refl
SRS (site west below) = refl

HR : (p : Site) → H (R p) ≡ R (H p)
HR (site d h) = refl

HS : (p : Site) → H (S p) ≡ S (H p)
HS (site d h) = refl

-- The inversion acts on this carrier as a half-turn combined
-- with horizontal reflection.
inversion : Site → Site
inversion p = R (R (H p))

inversion2 : (p : Site) → inversion (inversion p) ≡ p
inversion2 (site north above) = refl
inversion2 (site east above) = refl
inversion2 (site south above) = refl
inversion2 (site west above) = refl
inversion2 (site north below) = refl
inversion2 (site east below) = refl
inversion2 (site south below) = refl
inversion2 (site west below) = refl

rotoinversion4 : Site → Site
rotoinversion4 p = inversion (R p)

rotoinversion4Order4 : (p : Site) →
  rotoinversion4 (rotoinversion4
    (rotoinversion4 (rotoinversion4 p))) ≡ p
rotoinversion4Order4 (site north above) = refl
rotoinversion4Order4 (site east above) = refl
rotoinversion4Order4 (site south above) = refl
rotoinversion4Order4 (site west above) = refl
rotoinversion4Order4 (site north below) = refl
rotoinversion4Order4 (site east below) = refl
rotoinversion4Order4 (site south below) = refl
rotoinversion4Order4 (site west below) = refl
