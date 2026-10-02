# Reproduce the CTblLib/AtlasRep quotient calculation for the Monster-local
# group 2^(2+11+22).(M24 x S3).
#
# Source recipe:
#   g := AtlasGroup("2^(2+11+22).(M24xS3)");
#   first block action kills an 8192 kernel;
#   second block action has order |M24|*6;
#   its two nontrivial block systems have block sizes 24 and 3;
#   the resulting quotient actions recover S3 and M24 respectively.
#
# This receipt verifies the sourced finite local quotient only.  It does not
# identify the Carnahan--Urano 2B Tate module with any module for this group.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

name := "2^(2+11+22).(M24xS3)";
expectedOrder := 50472333605150392320;
expectedDegree := 294912;
expectedM24Order := 244823040;
expectedS3Order := 6;
expectedProductOrder := expectedM24Order * expectedS3Order;

G := AtlasGroup(name);
if G=fail then Error("could not construct sourced Monster-local group"); fi;
if Size(G)<>expectedOrder then Error("unexpected local group order"); fi;
if NrMovedPoints(G)<>expectedDegree then Error("unexpected permutation degree"); fi;

bl1 := Blocks(G,MovedPoints(G));
if Length(bl1)<>147456 then Error("unexpected first block count"); fi;
hom1 := ActionHomomorphism(G,bl1,OnSets);
act1 := Image(hom1);
kernel1Order := Size(G)/Size(act1);
if kernel1Order<>8192 then Error("unexpected first block kernel order"); fi;

bl2 := Blocks(act1,MovedPoints(act1));
if Length(bl2)<>72 then Error("unexpected second block count"); fi;
hom2 := ActionHomomorphism(act1,bl2,OnSets);
act2 := Image(hom2);
if Size(act2)<>expectedProductOrder then
  Error("second quotient does not have order |M24|*6");
fi;

blockSeeds := AllBlocks(act2);
blockSeedSizes := List(blockSeeds,Length);
if Set(blockSeedSizes)<>Set([3,24]) then
  Error("quotient does not expose complementary size-3 and size-24 blocks");
fi;

seed3 := First(blockSeeds,b -> Length(b)=3);
seed24 := First(blockSeeds,b -> Length(b)=24);

orbitOf3Block := Orbit(act2,seed3,OnSets);
orbitOf24Block := Orbit(act2,seed24,OnSets);

homOn3Blocks := ActionHomomorphism(act2,orbitOf3Block,OnSets);
homOn24Blocks := ActionHomomorphism(act2,orbitOf24Block,OnSets);
imageOn3Blocks := Image(homOn3Blocks);
imageOn24Blocks := Image(homOn24Blocks);

# A block of size 3 has an orbit of 24 blocks and yields the M24 factor.
# A block of size 24 has an orbit of 3 blocks and yields the S3 factor.
if Length(orbitOf3Block)<>24 then
  Error("size-3 block system does not yield 24 blocks");
fi;
if Length(orbitOf24Block)<>3 then
  Error("size-24 block system does not yield 3 blocks");
fi;
if Size(imageOn3Blocks)<>expectedM24Order then
  Error("24-block action is not M24 order");
fi;
if Size(imageOn24Blocks)<>expectedS3Order then
  Error("3-block action is not S3 order");
fi;

kernelM24Projection := Kernel(homOn3Blocks);
kernelS3Projection := Kernel(homOn24Blocks);

if Size(kernelM24Projection)<>expectedS3Order then
  Error("kernel of the M24 projection is not the expected S3 factor");
fi;
if Size(kernelS3Projection)<>expectedM24Order then
  Error("kernel of the S3 projection is not the expected M24 factor");
fi;

kernelIntersection := Intersection(kernelM24Projection,kernelS3Projection);
if Size(kernelIntersection)<>1 then
  Error("M24 and S3 quotient actions do not jointly separate act2");
fi;

pureC3Candidates := Filtered(Elements(kernelM24Projection),x -> Order(x)=3);
if Length(pureC3Candidates)=0 then
  Error("S3 factor has no order-three element");
fi;
pureC3 := pureC3Candidates[1];
pureC3OnThreeBlocks := Image(homOn24Blocks,pureC3);
pureC3OnTwentyFourBlocks := Image(homOn3Blocks,pureC3);

if Order(pureC3OnThreeBlocks)<>3 then
  Error("pure C3 does not survive as order three on the S3 three-block action");
fi;
if pureC3OnTwentyFourBlocks<>One(imageOn3Blocks) then
  Error("pure C3 should act trivially on the M24 24-block quotient");
fi;

threeBlockPoints := MovedPoints(imageOn24Blocks);
if Length(threeBlockPoints)<>3 then
  Error("S3 factor does not act on exactly three points");
fi;
pureC3Orbit := Orbit(Group(pureC3OnThreeBlocks),threeBlockPoints[1]);
if Length(pureC3Orbit)<>3 then
  Error("pure C3 does not cycle all three S3 blocks");
fi;

m24Iso := IsomorphismGroups(imageOn3Blocks,MathieuGroup(24));
if m24Iso=fail then Error("24-point factor is not isomorphic to M24"); fi;

s3Iso := IsomorphismGroups(imageOn24Blocks,SymmetricGroup(3));
if s3Iso=fail then Error("3-point factor is not isomorphic to S3"); fi;

PrintNatList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

out := OutputTextFile("build/twob_pure_klein_m24_s3_local_group.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"atlas_group_name\": \"",name,"\",\n");
AppendTo(out,"  \"group_order\": ",String(Size(G)),",\n");
AppendTo(out,"  \"permutation_degree\": ",String(NrMovedPoints(G)),",\n");
AppendTo(out,"  \"first_block_count\": ",String(Length(bl1)),",\n");
AppendTo(out,"  \"first_kernel_order\": ",String(kernel1Order),",\n");
AppendTo(out,"  \"second_block_count\": ",String(Length(bl2)),",\n");
AppendTo(out,"  \"m24xs3_quotient_order\": ",String(Size(act2)),",\n");
AppendTo(out,"  \"block_seed_sizes\": ");
PrintNatList(out,blockSeedSizes);
AppendTo(out,",\n");
AppendTo(out,"  \"m24_block_orbit_degree\": ",String(Length(orbitOf3Block)),",\n");
AppendTo(out,"  \"m24_factor_order\": ",String(Size(imageOn3Blocks)),",\n");
AppendTo(out,"  \"s3_block_orbit_degree\": ",String(Length(orbitOf24Block)),",\n");
AppendTo(out,"  \"s3_factor_order\": ",String(Size(imageOn24Blocks)),",\n");
AppendTo(out,"  \"joint_kernel_order\": ",String(Size(kernelIntersection)),",\n");
AppendTo(out,"  \"s3_factor_kernel_order\": ",String(Size(kernelM24Projection)),",\n");
AppendTo(out,"  \"m24_factor_kernel_order\": ",String(Size(kernelS3Projection)),",\n");
AppendTo(out,"  \"pure_c3_order\": ",String(Order(pureC3)),",\n");
AppendTo(out,"  \"pure_c3_three_block_orbit_size\": ",String(Length(pureC3Orbit)),",\n");
AppendTo(out,"  \"pure_c3_trivial_on_m24_factor\": true,\n");
AppendTo(out,"  \"m24_factor_isomorphic\": true,\n");
AppendTo(out,"  \"s3_factor_isomorphic\": true,\n");
AppendTo(out,"  \"actual_2b_tate_action_identified\": false,\n");
AppendTo(out,"  \"completion10_subquotient_identified\": false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("2B-pure local M24xS3 quotient receipt written: ",
  "|G|=",Size(G),
  "; quotient=",Size(act2),
  "; M24=",Size(imageOn3Blocks),
  "; S3=",Size(imageOn24Blocks),"\n");
QUIT;
