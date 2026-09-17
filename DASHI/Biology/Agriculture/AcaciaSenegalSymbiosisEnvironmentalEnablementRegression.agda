module DASHI.Biology.Agriculture.AcaciaSenegalSymbiosisEnvironmentalEnablementRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalSymbiosisEnvironmentalEnablementExact as Env

rasanen2004DOIPinned :
  Env.rasanen2004DOI ≡ "10.1023/B:PLSO.0000030181.03575.e1"
rasanen2004DOIPinned = refl

fall2011DOIPinned :
  Env.fall2011DOI ≡ "10.1007/s13199-011-0128-0"
fall2011DOIPinned = refl

rhizobialIdentityAloneNotAdequate :
  Env.rhizobialIdentityAloneAdequate Env.canonicalEnvironmentalEnablementBoundary ≡ false
rhizobialIdentityAloneNotAdequate = refl

hostIdentityAloneNotAdequate :
  Env.hostIdentityAloneAdequate Env.canonicalEnvironmentalEnablementBoundary ≡ false
hostIdentityAloneNotAdequate = refl

strainIdentityAloneNotAdequateUnderWaterDeficiency :
  Env.rhizobialStrainIdentityAloneAdequateUnderWaterDeficiency Env.canonicalEnvironmentalEnablementBoundary ≡ false
strainIdentityAloneNotAdequateUnderWaterDeficiency = refl

soilMoistureIsNotNoduleMicroenvironment :
  Env.bulkSoilMoistureEqualsNoduleMicroenvironment Env.canonicalEnvironmentalEnablementBoundary ≡ false
soilMoistureIsNotNoduleMicroenvironment = refl

greenhouseDoesNotCreateFieldDeployment :
  Env.greenhouseWaterDeficiencyCreatesFieldDeploymentAuthority Env.canonicalEnvironmentalEnablementBoundary ≡ false
greenhouseDoesNotCreateFieldDeployment = refl

environmentalEnablementDoesNotPayPlantAssimilation :
  Env.reactionEnablementPaysPlantAssimilation Env.canonicalEnvironmentalEnablementBoundary ≡ false
environmentalEnablementDoesNotPayPlantAssimilation = refl
