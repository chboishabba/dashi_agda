module DASHI.Mathematics.LinearAlgebra.RationalLDLQuadraticDominationBridgeExact where

------------------------------------------------------------------------
-- RATIONAL LDL^T CERTIFICATES -> GENERIC QUADRATIC DOMINATION
--
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Reuse the existing Yang--Mills `RationalLDLCertificate` consumer as a
-- constructor for the source-neutral quadratic domination relation.  No LDL
-- arithmetic is reimplemented here.
--
-- If an existing certificate proves
--
--   energy(x) = c * normSq(x) + sum_j d_j * ell_j(x)^2,
--   d_j >= 0,
--
-- then the already-proved `ldlCertificatePoincare` theorem immediately gives
--
--   c * normSq <=q energy.
--
-- This is the bridge needed for finite affine-spectral-independence defect
-- matrices: once a concrete defect quadratic form is supplied with an LDL^T
-- certificate, it becomes a generic domination theorem without any new
-- spectral machinery.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Mathematics.LinearAlgebra.FiniteRationalQuadraticDominationExact as Q
import DASHI.Physics.YangMills.BalabanRationalLDLCertificate as LDL

certificateLowerForm :
  ∀ {Coordinate : Set} →
  LDL.RationalLDLCertificate Coordinate → Q.QuadraticForm Coordinate
certificateLowerForm certificate coordinate =
  LDL.coercivityConstant certificate * LDL.normSq certificate coordinate

certificateUpperForm :
  ∀ {Coordinate : Set} →
  LDL.RationalLDLCertificate Coordinate → Q.QuadraticForm Coordinate
certificateUpperForm certificate = LDL.energy certificate

ldlCertificateGivesQuadraticDomination :
  ∀ {Coordinate : Set}
    (certificate : LDL.RationalLDLCertificate Coordinate) →
  certificateLowerForm certificate Q.≼q certificateUpperForm certificate
ldlCertificateGivesQuadraticDomination certificate coordinate =
  LDL.ldlCertificatePoincare certificate coordinate

ldlCertificateAsQuadraticDominationCertificate :
  ∀ {Coordinate : Set} →
  LDL.RationalLDLCertificate Coordinate →
  Q.QuadraticDominationCertificate Coordinate
ldlCertificateAsQuadraticDominationCertificate certificate =
  Q.quadraticDominationCertificate
    (certificateLowerForm certificate)
    (certificateUpperForm certificate)
    (ldlCertificateGivesQuadraticDomination certificate)
