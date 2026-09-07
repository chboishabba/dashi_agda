module DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact as Uniform

private
  boundary = Uniform.canonicalUniformCertifiedHighOffLineBoundary

oneOffCertificateNotClayProducer :
  Uniform.oneFixedFiniteCertificateIsClayLevelHighProducer boundary ≡ false
oneOffCertificateNotClayProducer = refl

uniformFamilyRequired :
  Uniform.perHighOffLineCertificateFamilyRequired boundary ≡ true
uniformFamilyRequired = refl

uniformCasesCompilePrizeHighProducer :
  Uniform.certifiedOffAndFreshGammaCasesCompilePrizeHighProducer boundary ≡ true
uniformCasesCompilePrizeHighProducer = refl

uniformProducerNotFabricated :
  Uniform.uniformProducerInhabitedHere boundary ≡ false
uniformProducerNotFabricated = refl

lowCertificateNotManufactured :
  Uniform.lowOrdinateCertificateManufacturedHere boundary ≡ false
lowCertificateNotManufactured = refl

rhStillOpen : Uniform.rhDerived boundary ≡ false
rhStillOpen = refl
