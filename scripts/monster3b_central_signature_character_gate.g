# Exact source-row screen: does marked central C3 and C2 parity at the
# measured dimensions already force the ordinary multiplicity representation?
# Uses CTblLib original ordinary tables; does not presume the answer.
# Also compute predicted sparse literal traces from the existing source fusions.
if LoadPackage("ctbllib")<>true then Error("CTblLib required"); fi;
six:=CharacterTable("6.Suz");;
outer:=CharacterTable("6.Suz.2");;
two:=CharacterTable("2.Suz.2");;
suz:=CharacterTable("Suz.2");;
main:=CharacterTable("3^1+12:6.Suz.2");;
if main=fail then main:=CharacterTable("3^(1+12):6.Suz.2"); fi;
n:=CharacterTable("MN3B");;
m:=CharacterTable("M");;
if ForAny([six,outer,two,suz,main,n,m],x->x=fail) then Error("original table absent"); fi;
if Size(six)<>2690072985600 or NrConjugacyClasses(six)<>210 then Error("source table identity"); fi;
f:=function(a,b)
 local x;
 x:=GetFusionMap(a,b);
 if x=fail or Length(x)<>NrConjugacyClasses(a) then Error("exact stored fusion missing"); fi;
 return x;
end;;
irr:=Irr(six);;
center:=ClassPositionsOfCentre(six);;
c2:=Filtered(center,i->OrdersClassRepresentatives(six)[i]=2);;
c3:=Filtered(center,i->OrdersClassRepresentatives(six)[i]=3);;
if Length(c2)<>1 or Length(c3)<>2 then Error("marked centre inventory"); fi;
t2:=c2[1];; t3:=c3[1];;
p2:=PowerMap(six,2);;
if p2=fail or Length(p2)<>210 then Error("source power map absent"); fi;
matches:=[];; unique:=true;;
for s in [1,2] do
 for spec in [[12,-1],[78,1]] do
  candidates:=Filtered([1..Length(irr)],i->irr[i][1]<=spec[1]
    and irr[i][t2]=spec[2]*irr[i][1]
    and irr[i][t3]=E(3)^s*irr[i][1]);;
  Add(matches,[s,spec[1],spec[2],List(candidates,i->[i,irr[i][1]])]);;
  if Length(candidates)<>1 or irr[candidates[1]][1]<>spec[1] then
   unique:=false;
  fi;
 od;
od;
Print("MARKED_CENTRAL_CLASSES ",[t2,t3],"\n");
Print("CENTRAL_SIGNATURE_CANDIDATES ",matches,"\n");
Print("CENTRAL_SIGNATURE_DIMENSIONS_FORCE_IRREDUCIBLES ",unique,"\n");
if unique then
 for k in [1,3] do
  i:=matches[k][4][1][1];; j:=matches[k+1][4][1][1];;
  values:=List([1..210],u->GaloisCyc((irr[i][u]^2+irr[i][p2[u]])/2,-1));;
  if values<>List(irr[j],x->x) then Error("same-phase full dual Sym2 residual"); fi;
 od;
 Print("CENTRAL_SIGNATURE_DUAL_SYM2_FULL_ROWS_MATCH true\n");
fi;
# Original outer standard C source class, distinct from the inner D4 rotation.
ts:=f(two,suz);; ot:=f(outer,two);; om:=f(outer,main);;
mn:=f(main,n);; nm:=f(n,m);; mo:=f(main,outer);;
sc:=Position(AtlasClassNames(suz),"2C");;
zz:=Filtered(ClassPositionsOfCentre(two),i->OrdersClassRepresentatives(two)[i]=2);;
if sc=fail or Length(zz)<>1 then Error("outer source class absent"); fi;
tc:=Filtered([1..NrConjugacyClasses(two)],i->OrdersClassRepresentatives(two)[i]=4
  and PowerMap(two,2)[i]=zz[1] and ts[i]=sc);;
oc:=Filtered([1..NrConjugacyClasses(outer)],i->OrdersClassRepresentatives(outer)[i]=4 and ot[i] in tc);;
mc:=Set(List(oc,i->om[i]));;
if Length(mc)<>1 then Error("outer lift main class not unique"); fi;
mc:=mc[1];; mj:=PowerMap(main,2)[mc];;
mz:=Filtered([1..NrConjugacyClasses(main)],i->OrdersClassRepresentatives(main)[i]=3
 and SizesConjugacyClasses(main)[i]=2 and mo[i]=1);;
if Length(mz)<>1 then Error("actual extraspecial centre class not unique"); fi;
mz:=mz[1];;
mzj:=Filtered([1..NrConjugacyClasses(main)],i->OrdersClassRepresentatives(main)[i]=6
 and PowerMap(main,2)[i]=mz and PowerMap(main,3)[i]=mj);;
if Length(mzj)<>1 then Error("central twist main class not unique"); fi;
mzj:=mzj[1];;
classes:=List([mc,mj,mzj,mz],i->nm[mn[i]]);;
mi:=Filtered(Irr(m),x->x[1]=196883);;
if Length(mi)<>1 then Error("original Monster character absent"); fi;
chi:=mi[1];;
Print("SOURCE_MAIN_CLASSES_C_J_ZJ_Z ",[mc,mj,mzj,mz],"\n");
Print("SOURCE_MONSTER_CLASSES_C_J_ZJ_Z ",classes,"\n");
Print("SOURCE_MONSTER_LABELS_C_J_ZJ_Z ",AtlasClassNames(m){classes},"\n");
Print("SOURCE_FULL_TRACES_C_J_ZJ_Z ",List(classes,i->chi[i]+1),"\n");
# Independently retain every constituent in the full restriction, including
# the zero sector, not just the two previously selected nontrivial rows.
rest:=ClassFunction(n,List(nm,i->chi[i]));;
coeff:=List(Irr(n),x->ScalarProduct(n,rest,x));;
if ForAny(coeff,x->not IsInt(x) or x<0) then Error("restriction multiplicity residual"); fi;
support:=Filtered([1..Length(coeff)],i->coeff[i]>0);;
if Sum(List(support,i->coeff[i]*Irr(n)[i]))<>rest then Error("full restriction reconstruction residual"); fi;
Print("FULL_IRR196883_RESTRICTION_ROWS ",List(support,i->[i,Irr(n)[i][1],coeff[i],Irr(n)[i][mn[mz]]]),"\n");
Print("SOURCE_GATE_COMPLETE; actual native trace and cover attachment separate\n");
QUIT;
