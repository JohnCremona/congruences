load "IntFrobFunctions.m";
load "mod13pairs.m";

p:=13;
Fp:=GF(p);

function QuickGoodRedTest(E1,E2,Bound,p)
	pps:=[ q : q in PrimesUpTo(Bound) | Conductor(E1)*Conductor(E2)*p mod q ne 0];
	Gp:=GL(2,p);
	types:=[];
	for q in pps do
		Fq:=GF(q);
		E1res:=ChangeRing(MinimalModel(E1),Fq);
		frobq:=Gp!IntegralFrobenius(ChangeRing(MinimalModel(E1),Fq));
		if Order(frobq) mod p eq 0 then 
			E2res:=ChangeRing(MinimalModel(E2),Fq);
		 	if IsIsomorphic(E1res,E2res) then Append(~types,1); end if;
		end if;
	end for;
	if #types ne 0 then 
		assert #Set(types) eq 1 and Rep(Set(types)) eq 1;
		return 1;
	else 	
		print "good reduction test was inconclusive";
		return 0;
	end if;
end function;

function symFrobMatrix(E,q,p)

assert Valuation(Conductor(E),q) eq 0;

Gp:=GL(2,p);
Fp:=GF(p);
Zp:=Integers(p);
Fq:=GF(q);
P<x>:=PolynomialRing(Rationals());

frobq:=Gp!IntegralFrobenius(ChangeRing(MinimalModel(E),Fq));
assert Order(frobq) mod p eq 0;


// fixes a non-square mod p
_:=exists(ns){ x : x in [1..p] | not IsSquare(Zp!x) };
assert LegendreSymbol(ns,p) eq -1;



/* Finding the p-torsion field of the residual curve E over Fq. */

print "Finding the p-torsion field of the residual curve at q=", q;

EoFq:=ChangeRing(E,Fq);
polE:=DivisionPolynomial(EoFq,p);
K:=SplittingField(polE);
PK<y>:=PolynomialRing(K);
roots:=Roots(polE,K);
r1:=roots[1,1];

EoK:=ChangeRing(EoFq,K);
pE:=PK!Evaluate(DefiningPolynomial(EoK),[r1,y,1]);

if #Factorisation(pE) eq 1 then
Kp:=ext<K | pE>;
else
Kp:=K;
end if;
print "..done.";

/* Finding symplectic basis of the p-torsion of the residual curve. */

EoKp:=ChangeRing(EoK,Kp);

// fixing a primitive root of unity to use in with the Weil pairing
zeta:=Roots(x^p - 1,K)[2,1]; 
assert zeta ne 1;

P1:=EoKp!Points(EoKp,r1)[1];

for i in [1..#roots] do 
    pt:=Points(EoKp,roots[i,1])[1];
    if IsLinearlyIndependent([P1,pt],p) then
        pairing:=WeilPairing(P1,pt,p);
        k:=Index([zeta^k eq pairing : k in [1..p]],true);
        if IsSquare(Zp!k) then
            P2:=pt;
        else
            P2:=ns*pt;
        end if;
        break i;
    end if;
end for;
assert IsSquare(Zp!Index([zeta^k eq WeilPairing(P1,P2,p) : k in [1..p]],true));

print "found a symplectic basis of the p-torsion";

/* computing the action of Frob_q in the computed basis */

// finding the Frobenius element

Gal,_,toAut:=AutomorphismGroup(Kp,Fq);
Frobq:=toAut(Gal.1);
assert Frobq(Kp.1) eq Kp.1^q;

FrP1:=EoKp![Frobq(P1[1]),Frobq(P1[2])];
FrP2:=EoKp![Frobq(P2[1]),Frobq(P2[2])];

for a, b in [1..p] do 
    if (a*P1 + b*P2) eq FrP1 then
        vec1:=[a,b]; bol1:=true;
    else
        bol1:=false;
    end if;
    if (a*P1 + b*P2) eq FrP2 then
        vec2:=[a,b]; bol2:=true;
    else 
        bol2:=false;
    end if;
    if bol1 and bol2 then break a; end if;
end for;

FrobMat:=Transpose(Gp!Matrix([vec1,vec2]));

// determines the matrix converting the matrix representation 
// in the symplectic basis P1, P2 into the matrix representation given 
// by Tommaso's paper

assert IsConjugate(Gp,FrobMat,frobq);

return FrobMat;
end function;


function FullGoodRedTest(E1, E2, Bound, p)

pps:=[ q : q in PrimesUpTo(Bound) | Conductor(E1)*Conductor(E2)*p mod q ne 0];
	Gp:=GL(2,p);
	types:=[];
	for q in pps do
		Fq:=GF(q);
		E1res:=ChangeRing(MinimalModel(E1),Fq);
		frobq:=Gp!IntegralFrobenius(E1res);
		if Order(frobq) mod p eq 0 then 
			M1:=symFrobMatrix(E1,q,p);
			M2:=symFrobMatrix(E2,q,p);
	                assert IsConjugate(Gp,M1,M2);
                        _,cj:=IsConjugate(Gp,M1,M2);
            		Append(~types,IsSquare(Determinant(cj)));
print "q =",q,"worked";
break;
		end if;
	end for;
	if #types eq 0 then
		print "no useful good reduction primes smaller than prescribed bound";
		return 0;
	else
		assert #Set(types) eq 1;
		if Rep(Set(types)) eq true then return 1; else return -1; end if;	
	end if;
end function;



function has3torsionPoint(E,ell)
	assert ell ne 3; 
	C:=MinimalModel(E);
	c4C,c6C:=Explode(cInvariants(C)); 
	v4:=Valuation(c4C,ell); 
	c4Ctil:=Integers()!(c4C/ell^v4);
	v6:=Valuation(c6C,ell); 
	c6Ctil:=Integers()!(c6C/ell^v6);
	Delta:=Integers()!Discriminant(E);


        
	if ell ge 5 then
		assert Denominator(Valuation(Delta,ell)/12) eq 3;
		Ql:=pAdicField(ell,40);
		bolE:=IsSquare(Ql!(-6*c6Ctil));
		return bolE;
	end if;

	assert ell eq 2;
	assert Valuation(Conductor(E),ell) eq 2;
	bolE:=false;

	vD:=Valuation(Delta,ell);
	vals:=[v4,v6,vD];
	if vals eq [4,5,4] and [c4Ctil mod 8,c6Ctil mod 8] in [[7,1],[3,5]] then 
		bolE:=true;		
	end if;
	if (v4 ge 6 and [v6,vD] eq [5,4]) or (v4 ge 7 and [v6,vD] eq [7,8]) then 
		if c6Ctil mod 8 eq 5 then 
		      bolE:=true;		
		end if;
	end if;
  	if vals eq [4,6,8] then 
		if [c4Ctil mod 32, c6Ctil mod 16] in [[29,15],[5,3],[13,7],[21,11]] then 
			bolE:=true;		
		end if;
	end if;

	return bolE;
end function;



function findC3twist(E,q);
	C:=MinimalModel(E);
	Delta:=Integers()!Discriminant(C);
	if q ge 5 then
		e:=Denominator(Valuation(Delta,q)/12);
		if e eq 3 then
		   return 1;
		end if;
		if e eq 6 then
		   Ct:=MinimalModel(QuadraticTwist(C,q));	
		   assert Denominator(Valuation(Integers()!Discriminant(Ct),q)/12) eq 3;
		   return q;
		end if;
		print "there is no twist with C3 inertia at ", q;
		return 0;
	end if;

	if q eq 2 then 
		for t in [1,-1,2,-2] do 
			vt:=Valuation(Conductor(QuadraticTwist(C,t)),q);
			if vt eq 2 then 
				return t;
			end if;
		end for;
		print "there is no twist with C3 inertia at ", q;
		return 0;
	end if;
end function;


function C3testAtq(E1,E2,q,p)

	assert q mod 3 eq 2;	
	assert Valuation(jInvariant(E1),q) ge 0;
	assert Valuation(jInvariant(E2),q) ge 0;

	tw:=findC3twist(E1,q);
	if tw eq 0 then 
		return 0;
	else
		C1:=MinimalModel(QuadraticTwist(E1,tw));
		C2:=MinimalModel(QuadraticTwist(E2,tw));
	end if;
	
        if {has3torsionPoint(C1,q), has3torsionPoint(C2,q)} eq {true, false} then 
		t:=1; 
	else
		t:=0;
	end if;
	
	v1:=Valuation(Discriminant(C1),q);
	v2:=Valuation(Discriminant(C2),q);

	if (v1-v2) mod 3 eq 0 then 
		r:=0;
	else
		r:=1;
	end if;

	type:=LegendreSymbol(q,p)^r*LegendreSymbol(3,p)^t;
	return type;
end function;

function C3test(E1,E2,p)	
	potGoodE1:={q : q in PrimeDivisors(Conductor(E1)) | Valuation(jInvariant(E1),q) ge 0 and q ne p and q mod 3 eq 2};
	potGoodE2:={q : q in PrimeDivisors(Conductor(E2)) | Valuation(jInvariant(E2),q) ge 0 and q ne p and q mod 3 eq 2};
	potGood:=SetToSequence(potGoodE1 meet potGoodE2);

	symbols:=[];
	if #potGood ge 1 then
		for q in potGood do 
			type:=C3testAtq(E1,E2,q,p);
			if type ne 0 then 
				Append(~symbols,type);
			end if;
		end for;
	else 
		print "Curves have no useful C3 primes away from ",p;
	end if;

	if #Set(symbols) gt 0 then
		assert #Set(symbols) eq 1;
		return Rep(symbols);
	else
		print "Curves have no useful C3 primes away from ",p;
		return 0;
	end if;
end function;

function C3testWild(E1,E2,p)	
	
	if Valuation(Conductor(E1),3) ne 4 then 
		print "not wild C3 inertia";
		return 0;
	end if;

	assert Valuation(jInvariant(E2),3) ge 0;

	C1:=MinimalModel(E1);
	C2:=MinimalModel(E2);

	Delta1:=Discriminant(C1); 	
	c41,c61:=Explode(cInvariants(C1));
	vc41:=Valuation(c41,3);
	vc61:=Valuation(c61,3);
	c61p:=Integers()!(c61/3^vc61);

	Delta2:=Discriminant(C2); 	
	c42,c62:=Explode(cInvariants(C2));
	vc42:=Valuation(c42,3);
	vc62:=Valuation(c62,3);
	c62p:=Integers()!(c62/3^vc62);

	v1:=Valuation(Delta1,3);	
	v2:=Valuation(Delta2,3);
	delta1:=Integers()!(Delta1/3^v1);
	delta2:=Integers()!(Delta2/3^v2);

	if [vc41,vc61,v1] in [[2,3,4],[5,8,12]] and delta1 mod 3 eq 2 then 
		assert [vc42,vc62,v2] in [[2,3,4],[5,8,12]] and delta2 mod 3 eq 2;
		if (c61p - c62p) mod 3 eq 0 then r:=0; else r:=1; end if;
		return LegendreSymbol(3,p)^r;
	end if;
		


	C1:=MinimalModel(QuadraticTwist(C1,3));
	C2:=MinimalModel(QuadraticTwist(C2,3));

	Delta1:=Discriminant(C1); 	
	c41,c61:=Explode(cInvariants(C1));
	vc41:=Valuation(c41,3);
	vc61:=Valuation(c61,3);
	c61p:=Integers()!(c61/3^vc61);

	Delta2:=Discriminant(C2); 	
	c42,c62:=Explode(cInvariants(C2));
	vc42:=Valuation(c42,3);
	vc62:=Valuation(c62,3);
	c62p:=Integers()!(c62/3^vc62);

	v1:=Valuation(Delta1,3);
	v2:=Valuation(Delta2,3);
	delta1:=Integers()!(Delta1/3^v1);
	delta2:=Integers()!(Delta2/3^v2);


	if [vc41,vc61,v1] in [[2,3,4],[5,8,12]] and delta1 mod 3 eq 2 then 
		assert [vc42,vc62,v2] in [[2,3,4],[5,8,12]] and delta2 mod 3 eq 2;
		if (c61p - c62p) mod 3 eq 0 then r:=0; else r:=1; end if;
		return LegendreSymbol(3,p)^r;
	else
		print "wild C3 inertia but abelian image";
		return 0;
	end if;
end function;

function C4testAtq(E1,E2,q,p)

	assert q mod 4 eq 3;	
	assert Valuation(jInvariant(E1),q) ge 0;
	assert Valuation(jInvariant(E2),q) ge 0;

	C1:=MinimalModel(E1);
	C2:=MinimalModel(E2);

	Delta1:=Discriminant(C1); 	
	Delta2:=Discriminant(C2); 

	v1:=Valuation(Delta1,q);
	v2:=Valuation(Delta2,q);
	delta1:=Integers()!(Delta1/q^v1);
	delta2:=Integers()!(Delta2/q^v2);


        if {IsSquare(Integers(q)!delta1), IsSquare(Integers(q)!delta2)} eq {true, false} then 
		t:=1; 
	else
		t:=0;
	end if;
	
	if (v1-v2) mod 4 eq 0 then 
		r:=0;
	else
		r:=1;
	end if;

	type:=LegendreSymbol(q,p)^r*LegendreSymbol(2,p)^t;
	return type;
end function;


function C4test(E1, E2, p)

	C1:=MinimalModel(E1);
	C2:=MinimalModel(E2);

	Delta1:=Discriminant(C1); 	
	Delta2:=Discriminant(C2); 

	N1:=Conductor(C1);
	N2:=Conductor(C2);

	ppsC1:={q : q in PrimeDivisors(N1) | Valuation(jInvariant(C1),q) ge 0 and q ne p and q mod 4 eq 3};
	ppsC2:={q : q in PrimeDivisors(N2) | Valuation(jInvariant(C2),q) ge 0 and q ne p and q mod 4 eq 3};
	
	C4primes1:=[];
	C4primes2:=[];
	if 3 in ppsC1 and Valuation(N1,3) eq 2 and LocalInformation(QuadraticTwist(C1,3),3)[3] ne 0 then 
		Append(~C4primes1,3);	
		assert Valuation(N2,3) eq 2;
		Append(~C4primes2,3);	
	end if;

	for q in ppsC1 do
		if q ne 3 and Denominator(Valuation(Delta1,q)/12) eq 4 then 
				Append(~C4primes1,q);	
		end if;
	end for;
	
	
		
	for q in ppsC2 do
		if q ne 3 and Denominator(Valuation(Delta2,q)/12) eq 4 then 
				Append(~C4primes2,q);	
		end if;
	end for;
	
	assert Set(C4primes1) eq Set(C4primes2);
	potGood:=SetToSequence(Set(C4primes1) meet Set(C4primes2));

	symbols:=[];
	if #potGood ge 1 then
		for q in potGood do 
			type:=C4testAtq(C1,C2,q,p);
			if type ne 0 then 
				Append(~symbols,type);
			end if;
		end for;
	else 
		print "Curves have no useful C4 primes away from ",p;
	end if;

	if #Set(symbols) gt 0 then
		assert #Set(symbols) eq 1;
		return Rep(symbols);
	else
		print "Curves have no useful C4 primes away from ",p;
		return 0;
	end if;
end function;

function C4testWild(E1,E2,p)
	
	if Valuation(Conductor(E1),2) ne 8 then 
		print "not wild C4 inertia";
		return 0;
	end if;

	assert Valuation(jInvariant(E2),2) ge 0;

	C1:=MinimalModel(E1);
	C2:=MinimalModel(E2);

	Delta1:=Discriminant(C1); 	
	c41,c61:=Explode(cInvariants(C1));
	vc41:=Valuation(c41,2);
	c41p:=Integers()!(c41/2^vc41);	
	vc61:=Valuation(c61,2);
	c61p:=Integers()!(c61/2^vc61);

	Delta2:=Discriminant(C2); 	
	c42,c62:=Explode(cInvariants(C2));
	vc42:=Valuation(c42,2);
	c42p:=Integers()!(c42/2^vc42);	
	vc62:=Valuation(c62,2);
	c62p:=Integers()!(c62/2^vc62);

	v1:=Valuation(Delta1,2);	
	v2:=Valuation(Delta2,2);
	delta1:=Integers()!(Delta1/2^v1);
	delta2:=Integers()!(Delta2/2^v2);

	if [vc41,vc61,v1] in [[5,8,9],[7,11,15]] and (c41p-5*delta1) mod 8 eq 0 then 
		assert [vc42,vc62,v2] in [[5,8,9],[7,11,15]] and (c42p-5*delta2) mod 8 eq 0;
		if (c61p - c62p) mod 4 eq 0 then r:=0; else r:=1; end if;
		return LegendreSymbol(2,p)^r;
	else
		print "either abelian wild C4 or not C4 inertia";
		return 0;
	end if;
end function;

function H8test(E1,E2,p)
	C1:=E1; C2:=E2;

	if Valuation(Integers()!Conductor(C1),2) eq 6 then 
		C1:=QuadraticTwist(C1,2);
		C2:=QuadraticTwist(C2,2);
	end if;

        val2:=Valuation(Integers()!Conductor(C1),2);
	assert val2 eq Valuation(Integers()!Conductor(C2),2);

        valDisc1:=Valuation(Discriminant(C1),2);	
	c41,c61:=Explode(cInvariants(C1)); 
        valc41:=Valuation(c41,2); c41p:=Integers()!(c41/2^valc41);
        valc61:=Valuation(c61,2); 

	valDisc2:=Valuation(Discriminant(C2),2);
        c42,c62:=Explode(cInvariants(C2)); 
        valc42:=Valuation(c42,2); c42p:=Integers()!(c42/2^valc42);
        valc62:=Valuation(c62,2);

	if val2 eq 5 then
			if LegendreSymbol(2,p) eq 1 then
			 	return 1;
			else 
			   bolC1:=(([valc41,valDisc1] eq [4,6] and valc61 ge 7 and (c41p + 1) mod 4 eq 0) or [valc41,valc61,valDisc1] eq [7,9,12]);
			   bolC2:=(([valc42,valDisc2] eq [4,6] and valc62 ge 7 and (c42p + 1) mod 4 eq 0) or [valc42,valc62,valDisc2] eq [7,9,12]);	
			   assert LegendreSymbol(2,p) eq -1;	
			   if bolC1 eq bolC2 then return 1; else return -1; end if;	
			end if;
	end if;

	if val2 eq 8 then 
		if ([valc41,valDisc1] eq [5,9] and valc61 ge 9) or ([valc41,valDisc1] eq [7,15] and valc61 ge 12) then
			assert ([valc42,valDisc2] eq [5,9] and valc62 ge 9) or ([valc42,valDisc2] eq [7,15] and valc62 ge 12);
			if LegendreSymbol(2,p) eq 1 then 
				return 1;
			else
				assert LegendreSymbol(2,p) eq -1;
				if (c41p - c42p) mod 4 eq 0 then 
					return 1;
				else
					return -1;
				end if;
			end if;
		else 
			print "Conductor 2^8 but not H8 inertia";
			return 0;
		end if;
	end if;
	
	print "Not H8 inertia";
	return 0;
end function;


function SL2test(E1,E2,p);
	twistVals:=[Valuation(Conductor(QuadraticTwist(E1,d)),2) : d in [1,-1,2,-2]];	

	if {3,7} meet Set(twistVals) ne {} then 
		if LegendreSymbol(2,p) eq 1 then
		 	return 1;
		else 
		   assert LegendreSymbol(2,p) eq -1;	
		   valDisc1:=Valuation(Discriminant(MinimalModel(E1)),2);	
		   valDisc2:=Valuation(Discriminant(MinimalModel(E2)),2);	
		   if (valDisc1 - valDisc2) mod 3 eq 0 then 
			return 1;
		   else 
			return -1;
		   end if;
	 	end if;
	end if;

	print "Non SL2 inertia";
	return 0;
end function;

function Dic12test(C1,C2,p);
	E1:=MinimalModel(C1);
	E2:=MinimalModel(C2);
	val3:=Valuation(Integers()!Conductor(E1),3);

	if val3 in [3,5] and LegendreSymbol(3,p) eq 1 then 
		return 1;
	end if;

	valDisc1:=Valuation(Discriminant(E1),3); 
	Delta1p:=Integers()!(Discriminant(E1)/3^valDisc1);	
	c41,c61:=Explode(cInvariants(E1)); 
        valc41:=Valuation(c41,3); 
        valc61:=Valuation(c61,3); 

	valDisc2:=Valuation(Discriminant(E2),3); 
	Delta2p:=Integers()!(Discriminant(E2)/3^valDisc2);
        c42,c62:=Explode(cInvariants(E2)); 
        valc42:=Valuation(c42,3); 
        valc62:=Valuation(c62,3);

	if val3 eq 3 then 
		assert LegendreSymbol(3,p) eq -1;
		assert Valuation(Integers()!Conductor(E2),3) eq 3;	
		bolC1:=(valc41 ge 2 and [valc61,valDisc1] eq [3,3] and Delta1p mod 9 notin [2,4]) or [valc41,valc61,valDisc1] in [[2,4,3],[4,6,11]];
		bolC2:=(valc42 ge 2 and [valc62,valDisc2] eq [3,3] and Delta2p mod 9 notin [2,4]) or [valc42,valc62,valDisc2] in [[2,4,3],[4,6,11]];
		if bolC1 eq bolC2 then return 1; else return -1; end if;
	end if;

	if val3 eq 5 then 
		assert LegendreSymbol(3,p) eq -1;
		assert Valuation(Integers()!Conductor(E2),3) eq 5;	
		bolC1:=(valc41 ge 3 and [valc61,valDisc1] eq [4,5]) or (valc41 ge 6 and [valc61,valDisc1] eq [8,13]);
		bolC2:=(valc42 ge 3 and [valc62,valDisc2] eq [4,5]) or (valc42 ge 6 and [valc62,valDisc2] eq [8,13]);
		if bolC1 eq bolC2 then return 1; else return -1; end if;
	end if;		

	print "Non Dic12 inertia";
	return 0;
end function;

function findMultiplicativeTwist(E,q);
	assert Valuation(jInvariant(E),q) lt 0;
	C:=E;
	if Valuation(Conductor(C),q) eq 1 then 
		return MinimalModel(C), q;
	end if;
	if q mod 2 eq 1 then 
	   Cd:=QuadraticTwist(C,q);
	   assert Valuation(Conductor(Cd),q) eq 1; 	
	   return MinimalModel(Cd), q;
	end if;

	if q eq 2 then
	    for d in [-1,2,-2] do 	
	   	Cd:=QuadraticTwist(C,d);
	   	if Valuation(Conductor(Cd),q) eq 1 then 
			return MinimalModel(Cd), d;
		end if;
            end for;
	end if;
end function;

function multiplicativeTest(E1,E2,p);

multPPsE1:={q : q in PrimeDivisors(Conductor(E1)) | Valuation(jInvariant(E1),q) lt 0};
multPPsE2:={q : q in PrimeDivisors(Conductor(E2)) | Valuation(jInvariant(E2),q) lt 0};
mpps:=SetToSequence(multPPsE1 meet multPPsE2);

k:=Index(mpps,p);
if k ne 0 then 
mpps:=Remove(mpps,k);
end if;

if mpps ne [] then 
	symbols:=[];
	for q in mpps do 
	   E1t, t1:=findMultiplicativeTwist(E1,q);	
	   E2t, t2:=findMultiplicativeTwist(E2,q);		
           assert t1 eq t2;
       	   dq1:=Fp!Valuation(Discriminant(E1t),q);	
           dq2:=Fp!Valuation(Discriminant(E2t),q);	
	   if Fp!0 notin [dq1, dq2] then  
		Append(~symbols,LegendreSymbol(Integers()!(dq1/dq2),p));
	   end if;
	end for;
	if #Set(symbols) gt 0 then
		assert #Set(symbols) eq 1;
		return Rep(symbols);
	else
		print "Curves have no useful multiplicative primes away from ",p;
		return 0;
	end if;
end if;

if mpps eq [] then 
	print "Curves have no common multiplicative primes away from ", p;
	return 0;
end if;
end function;


function test_pairs(pairs);

missed:=[];
symplectics:=[];
antisymplectics:=[];

for i in [1..#pairs] do 
tps:=[];
pr:=pairs[i];
print "i = ", i, ", pair = ", pr;
E1:=MinimalModel(EllipticCurve(pr[1]));
E2:=MinimalModel(EllipticCurve(pr[2]));

s1:=multiplicativeTest(E1,E2,p);
if s1 ne 0 then 
	Append(~tps,s1);
	print "success with multiplicative test";
end if;

s2:=H8test(E1,E2,p);
if s2 ne 0 then 
	Append(~tps,s2);
	print "success with H8 test";
end if;

s3:=SL2test(E1,E2,p);
if s3 ne 0 then 
	Append(~tps,s3);
	print "success with SL2 test";
end if;

s4:=Dic12test(E1,E2,p);
if s4 ne 0 then 
	Append(~tps,s4);
	print "success with Dic12 test";
end if;


s5:=C3test(E1,E2,p);
if s5 ne 0 then 
	Append(~tps,s5);
	print "success with C3 test";
end if;

s6:=C4test(E1,E2,p);
if s6 ne 0 then 
	Append(~tps,s6);
	print "success with C4 test";
end if;

s7:=C3testWild(E1,E2,p);	
if s7 ne 0 then 
	Append(~tps,s7);
	print "success with wild C3 test";
end if;

s8:=C4testWild(E1,E2,p);	
if s8 ne 0 then 
	Append(~tps,s8);
	print "success with wild C4 test";
end if;


if #tps ne 0 then
        // check that all test which applied agree:
        assert #Set(tps) eq 1;
        sgn := Rep(Set(tps));
	if sgn eq 1 then Append(~symplectics,i);
        elif sgn eq -1 then Append(~antisymplectics,i);
        end if;
	print i, sgn;
	print "+++++++++++++++++++++";
else
	print i, "no test applied";
	Append(~missed,i);
	print "+++++++++++++++++++++";
end if;
end for;


// applies test of good reduction only to those who missed all the tests

missed2:=[];
Bound:=1000;

print "After testing ", #pairs, " pairs, ";
print #symplectics, " pairs were proved to be symplectic, ";
print #antisymplectics, " pairs were proved to be antisymplectic, and";
print #missed, " failed (no test applied)";
print "Now applying the test of good reduction to these";

for i in [1..#missed] do 
tps:=[];
pr:=pairs[i];
print "i = ", i, ", pair = ", pr;
E1:=MinimalModel(EllipticCurve(pr[1]));
E2:=MinimalModel(EllipticCurve(pr[2]));

s9:=QuickGoodRedTest(E1,E2,Bound,p);
if s9 ne 0 then 
	Append(~tps,s9);
	print "success with quick good reduction test";
end if;

s10:=FullGoodRedTest(E1,E2,Bound,p);
if s10 ne 0 then 
	Append(~tps,s10);
	print "success with full good reduction test";
end if;

if #tps ne 0 then
	assert #Set(tps) eq 1; 
        sgn := Rep(Set(tps));
	if sgn eq 1 then Append(~symplectics,i);
        elif sgn eq -1 then Append(~antisymplectics,i);
        end if;
	print i, Rep(tps);
	print "+++++++++++++++++++++";
else
	print i, "no test applied";
	Append(~missed2,i);
	print "+++++++++++++++++++++";
end if;

end for;

print "After additional tests of ", #missed, " pairs";
print #symplectics, " pairs were proved to be symplectic, ";
print #antisymplectics, " pairs were proved to be antisymplectic, and";
print #missed2, " still failed (no test applied)";

// return statement to avoid error message, useless otherwise
return 0;

end function;

//test_pairs(mod7_red_anti_pairs);
//test_pairs(mod7_red_symp_pairs);


