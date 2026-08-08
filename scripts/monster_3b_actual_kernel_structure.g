# Certify the actual extraspecial 3-core in an AtlasRep construction of
# N_M(<3B>) = 3^(1+12).2.Suz.2 and align its centre with the unique
# size-two order-three MN3B class that fuses to Monster 3B.
#
# This script does not construct the 196883-dimensional Monster module.
# It closes the group-theoretic promotion seam that can be checked directly:
# the actual AtlasRep group has a normal extraspecial 3-core of order 3^13,
# exponent three, centre/derived subgroup of order three, elementary-abelian
# quotient of order 3^12, and its two nonidentity central elements form one
# conjugacy orbit. CTblLib then identifies the unique class with those
# invariants and its stored fusion to Monster 3B.
#
# Representation discovery deliberately uses the documented
# AllAtlasGeneratingSetInfos -> AtlasGroup(info) interface rather than assuming
# that one punctuation spelling is a constructible AtlasRep group name.
#
# SOURCES
# R. W. Barraclough and R. A. Wilson,
# "The Character Table of a Maximal Subgroup of the Monster",
# LMS J. Comput. Math. 10 (2007), 161--175.
# DOI: 10.1112/S1461157000001352.
#
# R. A. Wilson, P. Walsh, R. A. Parker and S. Linton,
# "A computer construction of the Monster",
# J. Group Theory 1 (1998), 307--337.
# DOI: 10.1515/jgth.1998.023.
#
# Thomas Breuer, "The GAP Character Table Library", CTblLib documentation.
# No DOI asserted.
#
# Thomas Breuer and Simon Nickerson, AtlasRep package documentation,
# especially AllAtlasGeneratingSetInfos and AtlasGroup. No DOI asserted.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;
if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

expectedGroupOrder := 2859230155080499200;
expectedKernelOrder := 1594323;       # 3^13
expectedQuotientOrder := 531441;      # 3^12
expectedHeisenbergDegree := 729;      # 3^6

groupNames := [
  "MN3B",
  "3^(1+12).2.Suz.2",
  "3^(1+12):2.Suz.2",
  "3^1+12.2.Suz.2"
];

G := fail;
selectedAtlasName := fail;
selectedRepName := fail;
selectedIdentifier := fail;

# Use AtlasRep's representation metadata first. AtlasGroup(info) is the
# documented way to construct exactly the representation described by a
# returned information record.
for groupName in groupNames do
  infos := AllAtlasGeneratingSetInfos(groupName);
  infos := Filtered(infos, info ->
    IsBound(info.size) and info.size = expectedGroupOrder);

  for info in infos do
    candidate := AtlasGroup(info);
    if candidate <> fail and Size(candidate) = expectedGroupOrder then
      G := candidate;
      selectedAtlasName := groupName;
      if IsBound(info.repname) then
        selectedRepName := info.repname;
      else
        selectedRepName := "unspecified";
      fi;
      if IsBound(info.identifier) then
        selectedIdentifier := info.identifier;
      fi;
      break;
    fi;
  od;

  if G <> fail then
    break;
  fi;
od;

# Some AtlasRep installations expose a constructible group directly but omit
# it from the locally cached information list. Retain a fail-closed fallback.
if G = fail then
  for groupName in groupNames do
    candidate := AtlasGroup(groupName);
    if candidate <> fail and Size(candidate) = expectedGroupOrder then
      G := candidate;
      selectedAtlasName := groupName;
      selectedRepName := "AtlasGroup-direct";
      break;
    fi;
  od;
fi;

if G = fail then
  Error("AtlasRep provides no constructible MN3B representation of the expected order");
fi;
if Size(G) <> expectedGroupOrder then
  Error("unexpected AtlasRep MN3B group order");
fi;

E := PCore(G, 3);
if E = fail then
  Error("could not compute the 3-core of the AtlasRep MN3B group");
fi;
if not IsNormal(G, E) then
  Error("the computed 3-core is not normal");
fi;
if Size(E) <> expectedKernelOrder then
  Error("the actual MN3B 3-core does not have order 3^13");
fi;
if Exponent(E) <> 3 then
  Error("the actual MN3B 3-core does not have exponent three");
fi;

Z := Centre(E);
D := DerivedSubgroup(E);
if Size(Z) <> 3 then
  Error("the actual 3-core centre does not have order three");
fi;
if D <> Z then
  Error("the actual 3-core derived subgroup is not its centre");
fi;

Q := FactorGroup(E, Z);
if Size(Q) <> expectedQuotientOrder then
  Error("the extraspecial quotient does not have order 3^12");
fi;
if not IsElementaryAbelian(Q) then
  Error("the extraspecial quotient is not elementary abelian");
fi;

nonidentityCentre := Filtered(Elements(Z), z -> z <> One(Z));
if Length(nonidentityCentre) <> 2 then
  Error("expected two nonidentity central elements");
fi;
z := nonidentityCentre[1];
centralOrbit := Orbit(G, z, OnConjugation);
if Length(centralOrbit) <> 2 then
  Error("the nonidentity centre is not one size-two MN3B conjugacy orbit");
fi;
if Set(centralOrbit) <> Set(nonidentityCentre) then
  Error("the size-two orbit is not exactly Z(E) minus the identity");
fi;

monster := CharacterTable("M");
mn3b := CharacterTable("MN3B");
if monster = fail or mn3b = fail then
  Error("required CTblLib tables M and MN3B are unavailable");
fi;
if Size(mn3b) <> Size(G) then
  Error("AtlasRep group order and MN3B table order disagree");
fi;

fusion := GetFusionMap(mn3b, monster);
if fusion = fail then
  Error("stored MN3B to Monster class fusion is unavailable");
fi;
monsterClassNames := ClassNames(monster, "ATLAS");
monster3BPosition := Position(monsterClassNames, "3B");
if monster3BPosition = fail then
  Error("Monster table does not expose ATLAS class 3B");
fi;

orders := OrdersClassRepresentatives(mn3b);
sizes := SizesConjugacyClasses(mn3b);
centralCandidates := Filtered([1..Length(orders)], i ->
  orders[i] = 3 and sizes[i] = 2);
if Length(centralCandidates) <> 1 then
  Error("MN3B does not have a unique size-two class of order three");
fi;
centralClass := centralCandidates[1];
if fusion[centralClass] <> monster3BPosition then
  Error("the unique size-two order-three MN3B class does not fuse to 3B");
fi;

# Character-theoretic arithmetic forced by the extraspecial structure.
linearCharacterCount := expectedQuotientOrder;
nonlinearCharacterCount := 2;
degreeSquareSum := linearCharacterCount
  + nonlinearCharacterCount * expectedHeisenbergDegree^2;
if degreeSquareSum <> expectedKernelOrder then
  Error("extraspecial character-degree square sum failed");
fi;

output := OutputTextFile("build/monster_3b_actual_kernel_structure.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"atlas_group_name\": \"", selectedAtlasName, "\",\n",
  "  \"atlas_representation_name\": \"", selectedRepName, "\",\n",
  "  \"mn3b_table\": \"", Identifier(mn3b), "\",\n",
  "  \"monster_table\": \"", Identifier(monster), "\",\n",
  "  \"actual_group_order\": ", Size(G), ",\n",
  "  \"kernel_prime\": 3,\n",
  "  \"actual_kernel_order\": ", Size(E), ",\n",
  "  \"actual_kernel_exponent\": ", Exponent(E), ",\n",
  "  \"actual_kernel_normal\": true,\n",
  "  \"actual_kernel_centre_order\": ", Size(Z), ",\n",
  "  \"actual_kernel_derived_order\": ", Size(D), ",\n",
  "  \"derived_equals_centre\": true,\n",
  "  \"actual_kernel_quotient_order\": ", Size(Q), ",\n",
  "  \"quotient_elementary_abelian\": true,\n",
  "  \"nonidentity_centre_orbit_size\": ", Length(centralOrbit), ",\n",
  "  \"centre_orbit_is_all_nonidentity_centre\": true,\n",
  "  \"mn3b_central_class_position\": ", centralClass, ",\n",
  "  \"mn3b_central_class_order\": ", orders[centralClass], ",\n",
  "  \"mn3b_central_class_size\": ", sizes[centralClass], ",\n",
  "  \"monster_3b_class_position\": ", monster3BPosition, ",\n",
  "  \"centre_class_fuses_to_monster_3b\": true,\n",
  "  \"linear_character_count\": ", linearCharacterCount, ",\n",
  "  \"nonlinear_character_count\": ", nonlinearCharacterCount, ",\n",
  "  \"nonlinear_character_degree\": ", expectedHeisenbergDegree, ",\n",
  "  \"character_degree_square_sum\": ", degreeSquareSum, "\n",
  "}\n"
);
CloseStream(output);

Print("Actual MN3B extraspecial kernel certificate written.\n");
Print("AtlasRep name: ", selectedAtlasName,
  "; representation: ", selectedRepName, "\n");
Print("|E| = ", Size(E), ", |Z(E)| = ", Size(Z),
  ", |E/Z(E)| = ", Size(Q), "\n");
Print("central class position = ", centralClass,
  ", Monster fusion = 3B\n");
QUIT;
