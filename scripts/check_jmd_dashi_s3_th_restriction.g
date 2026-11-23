# Source-owned acceptance test; run locally with GAP and CTblLib.
# Not executed in the current environment.
if LoadPackage("ctbllib") <> true then Error("CTblLib required"); fi;
h:=CharacterTable("S3xTh");;
m:=CharacterTable("M");;
f:=GetFusionMap(h,m);;
if f=fail or Length(f)<>144 then Error("missing complete fusion"); fi;
ir:=Irr(h);;
mi:=Filtered(Irr(m),x->x[1]=196883);;
if Length(mi)<>1 then Error("unique Monster character required"); fi;
v:=ClassFunction(h,List(f,i->mi[1][i]+1));;
mult:=List(ir,x->ScalarProduct(h,v,x));;
if not ForAll(mult,x->IsInt(x) and x>=0) then Error("bad multiplicities"); fi;
if List(Sum([1..Length(ir)],i->mult[i]*ir[i]))<>List(v) then Error("classwise reconstruction"); fi;
orders:=OrdersClassRepresentatives(h);; sizes:=SizesConjugacyClasses(h);;
r:=Filtered([1..Length(f)],i->orders[i]=3 and sizes[i]=2);;
t:=Filtered([1..Length(f)],i->orders[i]=2 and sizes[i]=3);;
if Length(r)<>1 or Length(t)<>1 then Error("S3 class identification"); fi;
r:=r[1];; t:=t[1];;
if v[r]<>0 or v[t]<>4372 then Error("reflection/rotation source disagreement"); fi;
Print("Fusion: ",f,"\n");
Print("Nonzero constituents [index, degree, multiplicity, reflection, rotation]:\n");
for i in [1..Length(ir)] do
 if mult[i]<>0 then Print([i,ir[i][1],mult[i],ir[i][t],ir[i][r]],"\n"); fi;
od;
Print("PASS: 144-class reconstruction\n");
QUIT;
