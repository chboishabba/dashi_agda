# Literal outer C, not inner rotation r: ATLAS Suz:2 standard c is 2C.
# Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
# Reuse stored Barraclough-Wilson/CTblLib fusions. For order4 lifts
# over an order4 quotient, Schur-Zassenhaus in the E-extension
# identifies all lifts up to E-conjugacy; no assertion that the outer
# lift is unique as an element. An order4 lift is assumed source-proved.
if LoadPackage("ctbllib")<>true then Error("CTblLib required"); fi;
s:=CharacterTable("Suz.2");;
t:=CharacterTable("2.Suz.2");;
h:=CharacterTable("6.Suz.2");;
main:=CharacterTable("3^1+12:6.Suz.2");;
if main=fail then main:=CharacterTable("3^(1+12):6.Suz.2"); fi;
n:=CharacterTable("MN3B");;
m:=CharacterTable("M");;
if ForAny([s,t,h,main,n,m],x->x=fail) then Error("missing original table"); fi;
f:=function(a,b)
 local x;
 x:=GetFusionMap(a,b);
 if x=fail or Length(x)<>NrConjugacyClasses(a) then Error("missing exact source fusion"); fi;
 return x;
end;;
c2:=Position(AtlasClassNames(s),"2C");;
if c2=fail or OrdersClassRepresentatives(s)[c2]<>2 then Error("ATLAS outer 2C class absent"); fi;
zz:=Filtered(ClassPositionsOfCentre(t),i->OrdersClassRepresentatives(t)[i]=2);;
if Length(zz)<>1 then Error("central -I class not unique"); fi;
ts:=f(t,s);; ht:=f(h,t);; hm:=f(h,main);; mn:=f(main,n);; nm:=f(n,m);;
tc:=Filtered([1..NrConjugacyClasses(t)],i->OrdersClassRepresentatives(t)[i]=4
 and PowerMap(t,2)[i]=zz[1] and ts[i]=c2);;
hc:=Filtered([1..NrConjugacyClasses(h)],i->OrdersClassRepresentatives(h)[i]=4 and ht[i] in tc);;
if Length(hc)=0 then Error("no outer C source lift"); fi;
rows:=List(hc,i->[ht[i],i,hm[i],mn[hm[i]],nm[mn[hm[i]]]]);;
classes:=Set(List(rows,x->x[5]));;
if ForAny(classes,i->OrdersClassRepresentatives(m)[i]<>4) then Error("bad source fusion order"); fi;
Print("OUTER_C_SOURCE_FUSION_ROWS ",rows,"\n");
Print("OUTER_C_SOURCE_MONSTER_POSITIONS ",classes,"\n");
Print("OUTER_C_SOURCE_MONSTER_CLASSES ",List(classes,i->ClassNames(m)[i]),"\n");
Print("OUTER_C_SOURCE_UNIQUE ",Length(classes)=1,"\n");
QUIT;
