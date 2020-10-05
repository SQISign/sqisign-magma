// ----------------------------------------------
// Optimisation of KLPT algorithm
// ----------------------------------------------


//TODO

DEBUG:=0;

CST:=1000;

CST_DEGREE:=1000;
CST_RANDOMIZATION_GAMMA:=15;
BOUND:=2;

Z:=Integers();
//apply LLL to a lattice given by its gram matrix
LLLFromGram:=function(M)
  L:=LatticeWithGram(M);
  _,T,_:=LLL(L:Proof:=false,Delta:=0.9999);
  return T;
end function;
//reduce the basis of an ideal using LLL, seems like it yields the same kind of result than for ReducedBasis
LLLReducedBasis:=function(I)
  M:=GramMatrix(I);
  B:=Basis(I);
  U:=LLLFromGram(M);
  return [ &+[B[j] * U[i,j] : j in [1..4] | U[i,j] ne 0] : i in [1..4] ];
end function;
//select a random element from an order
RandomElement:=function(A,S)
  return A![ Random(S) : i in [1..4] ];
end function;
//Sample a random ideal from A of norm l^bound
RandomIdeal:=function(A,l,bound)
  count:=1;
  D := Discriminant(A);
  I := LeftIdeal(A,[A!1]);
  MZ := RSpace(Integers(),2);
  FF := FiniteField(l);
  PF<X> := PolynomialRing(FF);
  EmptyList := [ MZ | ];
  repeat
    x1 := RandomElement(A,[-l div 2..l div 2]);
    D1 := Trace(x1)^2 - 4*Norm(x1);
  until KroneckerSymbol(D1,l) eq -1;
  repeat
    x2 := RandomElement(A,[-l div 2..l div 2]);
    D2 := Trace(x2)^2 - 4*Norm(x2);
  until KroneckerSymbol(D2,l) eq 1;
  a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
  x2 := x2 - a2;
  T := 2*Trace(x1*Conjugate(x2)) - Trace(x1)*Trace(x2);
  D := (D1*D2 - T^2) div 4;
  r1 := 1;
  Frontier := [ [ MZ!P : P in P1Classes(l) ] ];
  P:=Frontier[1][1];
  // #Frontier;
  // #Frontier[1];
  while count lt bound do
    count:=count+1;
    Append(~Frontier,EmptyList);
    r2:=Random(1,#Frontier[r1]);
    P:=Frontier[r1][r2];
    Q:=P;
    if (P[2] mod l) ne 0 then // P[2] eq 1 by assumption.
      for t in [0..(l-1)] do
        Q[1] := P[1] + t*l^r1;
        Append(~Frontier[r1+1],Q);
      end for;
    else // P = Q equals <1,0 mod l>.
      for t in [0..(l-1)] do
        Q[2] := P[2] + t*l^r1;
        Append(~Frontier[r1+1],Q);
      end for;
    end if;
    r1+:=1;
  end while;
  Ires := LeftIdeal(A,[x2^r1*(A!P[1] + P[2]*x1), A!l^r1]);
  return Ires;
end function;
// given a quaternion algebra ramified at a prime p and infty
// return a maximal order such that it lies in a nearly uniformly chosen class
// this is achieved by performing a random walk of degree p^2 from a fixed order
RandomOrderClass:=function(B)
	// compute arbitrary maximal order
	order:=MaximalOrder(B);

	// fix L
	L:=2;

	// compute path length to achieve random distribution
	p:=Max(Norm(B.1),Norm(B.2));
	length:=Ceiling(2*Log(L,p));

	// random walk
	for ind in [1..length] do
		ideal:=Random(MaximalLeftIdeals(order,L));
		order:=RightOrder(ideal);
	end for;

	return order;
end function;

// given a quaternion algebra ramified at a prime p and infty
// return a maximal order such that it lies in a nearly uniformly chosen class, and in addition the representative is "randomly chosen"
// this is achieved by conjugating an order obtained with the previous function
RandomOrder:=function(B)
	// "random" quaternion
	p:=Max(Norm(B.1),Norm(B.2));
	bound:=Ceiling(p^BOUND);
	quat:=&+[(Random(2*bound)-bound)*elt: elt in [1,B.1,B.2,B.3]];

	// random order class
	order:=RandomOrderClass(B);

	//randomizing representative
	order:=QuaternionOrder([quat*elt*Conjugate(quat)/Norm(quat): elt in Basis(order)]);

	return order;
end function;

// Given two maximal orders, return an ideal connecting them
// This should be polytime. The approach below is kind of ad hoc.
// Should we follow lemma 8 in ANTS 2014 paper instead?
// See also ALGORITHMIC ENUMERATION OF IDEAL CLASSES FOR QUATERNION ORDERS by MARKUS KIRSCHMER AND JOHN VOIGHT
ConnectingIdeal:=function(order1,order2)
	intersection:=order1 meet order2;
	index:= Integers()! (Discriminant(intersection)/Discriminant(order1));
	ideal:=LeftIdeal(order1,[index*elt: elt in Basis(order2)]);
	if DEBUG ge 2 then Basis(RightOrder(ideal)); Basis(order2); end if;

	// addendum to previous method: scale down ideal if possible
	factors:= Factorization(Integers()!Norm(ideal));
	factors:= [fac[1]: fac in factors];
	for fac in factors do
		reduced:=true;
		while reduced do
			if &and[elt/fac in ideal : elt in Basis(ideal)] then
				ideal:=LeftIdeal(order1,[elt/fac: elt in Basis(ideal)]);
			else
				reduced:=false;
			end if;
		end while;
	end for;

	return ideal;
end function;

// given a maximal order
// return a maximal order in same class with LLL reduced elements
ReducedMaximalOrder:=function(order)
	// QA
	B:=Parent(Basis(order)[1]);

	// compute special order
	special:=MaximalOrder(B);

	// order intersecting both
	intersection:=order meet special;
	index:= Integers()! (Discriminant(intersection)/Discriminant(order));

	// ideal connecting both
	ideal:=LeftIdeal(special,[index*elt: elt in Basis(order)]);   // should we follow lemma 8 in ANTS 2014 paper instead?
	if DEBUG ge 2 then Basis(RightOrder(ideal)); Basis(order); end if;

	// reduce this ideal with LLL
	// basis:=ReducedBasis(ideal);
	basis:=LLLReducedBasis(ideal);

	// use Lemma 5 in ANTS paper to reduce ideal
	ideal:=LeftIdeal(special,[elt*Conjugate(basis[1])/Norm(ideal): elt in Basis(ideal)]);

	// compute resulting order
	order2:=RightOrder(ideal);
	if DEBUG ge 2 then "is result isomorphic?",IsIsomorphic(order,order2); "previous order is",Basis(order); "new order is", Basis(order2); end if;

	return order2;
end function;


// Finds some powersmooth number larger than n
// Not very clever, but does the job
NextPowerSmooth:=function(N : reduced := true);
	n := 1;
	factors := [<3,1>];
	B := 1;
	while n le N do
		incremented := false;
		for i in [1..#factors] do
			if factors[i][1]^(factors[i][2]+1) le B then
				factors[i][2] +:= 1;
				incremented := true;
			end if;
		end for;
		if not(incremented) then
			factors := Append(factors, <NextPrime(factors[#factors][1]),1>);
		end if;
		n := &*[f[1]^f[2] : f in factors];
		B := Maximum([f[1]^f[2] : f in factors]);
	end while;

	// reduce if we overshot
	for i in Reverse([1..#factors]) do
		while ((factors[i][2] gt 0) and (n/factors[i][1] gt N)) do
			factors[i][2] -:= 1;
			n /:= factors[i][1];
		end while;
	end for;
	return Integers()!n, factors;
end function;

// Finds n1>N1 and n2>N2 such that n1*n2 is powersmooth
// Again, not very clever, but does the job
PowerSmoothPair:=function(N1,N2);
	n, factors := NextPowerSmooth(N1*N2 : reduced := false);

	n1 := 1;
	n2 := 1;
	factors1 := [<f[1], 0> : f in factors];
	factors2 := [<f[1], 0> : f in factors];

	// randomply split the factors between both numbers
	for i in [1..#factors] do
		r := Random(0,factors[i][2]);
		factors1[i][2] := r;
		factors2[i][2] := factors[i][2]-r;
	end for;
	n1 := &*[f[1]^f[2] : f in factors1];
	n2 := &*[f[1]^f[2] : f in factors2];
	// balance
	for i in Reverse([1..#factors]) do
		while ((factors1[i][2] ge 1) and (n1/factors1[i][1] gt N1)) do
			factors1[i][2] -:= 1;
			n1 /:= factors1[i][1];
			factors2[i][2] +:= 1;
			n2 *:= factors2[i][1];
		end while;
		while ((factors2[i][2] ge 1) and (n2/factors2[i][1] gt N2)) do
			factors2[i][2] -:= 1;
			n2 /:= factors2[i][1];
			factors1[i][2] +:= 1;
			n1 *:= factors1[i][1];
		end while;
	end for;
	// might need to add new primes...
	while n1 le N1 do
		factors1 := Append(factors1, <NextPrime(factors1[#factors1][1]),1>);
		factors2 := Append(factors2, <factors1[#factors1][1],0>);
		n1 *:= factors1[#factors1][1];
	end while;
	while n2 le N2 do
		factors2 := Append(factors2, <NextPrime(factors2[#factors2][1]),1>);
		factors1 := Append(factors1, <factors2[#factors2][1],0>);
		n2 *:= factors2[#factors2][1];
	end while;
	// reduce if we overshot
	for i in Reverse([1..#factors]) do
		while ((factors1[i][2] ge 1) and (n1/factors1[i][1] gt N1)) do
			factors1[i][2] -:= 1;
			n1 /:= factors1[i][1];
		end while;
		while ((factors2[i][2] ge 1) and (n2/factors2[i][1] gt N2)) do
			factors2[i][2] -:= 1;
			n2 /:= factors2[i][1];
		end while;
	end for;

	return Integers()!n1,Integers()!n2,factors1,factors2;
end function;
// Assumes N is powersmooth, and finds a prime such that p*N is still as powersmooth as possible
NextBestPrimeForPowersmooth:=function(N : notIn := [])
	n := 1;
	p := 1;
	factors := [];

	while n ne N do
		p := NextPrime(p);
		factors := Append(factors,<p,Valuation(N,p)>);
		n *:= p^factors[#factors][2];
	end while;

	B := Maximum([f[1]^f[2] : f in factors]);

	for f in factors do
		if (f[1]^(f[2]+1) le B) and not(f[1] in notIn) then
			return f[1];
		end if;
	end for;

	p := factors[#factors][1];
	while true do
		p := NextPrime(p);
		if not(p in notIn) then
			return p;
		end if;
	end while;
end function;

// Finds some powersmooth number larger than n
// We want the result to divide T
NextPowerSmoothConstraint:=function(N,T,factorT : reduced := true);
	n := 1;
	factors := [<factorT[1][1],1>];
	tight:=false;
	while n le N do
		incremented := false;
		for i in [1..#factors] do
			if factors[i][2] le factorT[i][2]-1 then
				factors[i][2] +:= 1;
				n*:=factorT[i][1];
				incremented := true;
			end if;
		end for;
		if not(incremented)  then
			if #factors le #factorT -1 then
				factors := Append(factors, <factorT[#factors+1][1],1>);
				n*:=factorT[#factors][1];
			else
				"Not possible with current constraint";
				return 0,[];
			end if;
		end if;
	end while;

	// reduce if we overshot
	for i in Reverse([1..#factors]) do
		while ((factors[i][2] gt 0) and (n/factors[i][1] gt N)) do
			factors[i][2] -:= 1;
			n /:= factors[i][1];
		end while;
	end for;
	return Integers()!n, factors;
end function;

// Finds n1>N1 and n2>N2 such that n1*n2 is powersmooth
// We want the result to divide T
PowerSmoothPairConstraint:=function(N1,N2,T,factorT);
	n, factors := NextPowerSmoothConstraint(N1*N2,T,factorT : reduced := false);
	n1 := 1;
	n2 := 1;
	factors1 := [<f[1], 0> : f in factors];
	factors2 := [<f[1], 0> : f in factors];
	//"Available", Log(T)/Log(2);
	//"Required", Log(N1*N2)/Log(2);

	// randomply split the factors between both numbers
	for i in [1..#factors] do
		r := Random(0,factors[i][2]);
		factors1[i][2] := r;
		factors2[i][2] := factors[i][2]-r;
	end for;
	n1 := &*[f[1]^f[2] : f in factors1];
	n2 := &*[f[1]^f[2] : f in factors2];
	// balance
	for i in Reverse([1..#factors]) do
		while ((factors1[i][2] ge 1) and (n1/factors1[i][1] gt N1)) do
			factors1[i][2] -:= 1;
			n1 /:= factors1[i][1];
			factors2[i][2] +:= 1;
			n2 *:= factors2[i][1];
		end while;
		while ((factors2[i][2] ge 1) and (n2/factors2[i][1] gt N2)) do
			factors2[i][2] -:= 1;
			n2 /:= factors2[i][1];
			factors1[i][2] +:= 1;
			n1 *:= factors1[i][1];
		end while;
	end for;
	// might need to add new primes...
	// while n1 le N1 do
	// 	factors1 := Append(factors1, <NextPrime(factors1[#factors1][1]),1>);
	// 	factors2 := Append(factors2, <factors1[#factors1][1],0>);
	// 	n1 *:= factors1[#factors1][1];
	// end while;
	// while n2 le N2 do
	// 	factors2 := Append(factors2, <NextPrime(factors2[#factors2][1]),1>);
	// 	factors1 := Append(factors1, <factors2[#factors2][1],0>);
	// 	n2 *:= factors2[#factors2][1];
	// end while;
	// reduce if we overshot
	for i in Reverse([1..#factors]) do
		while ((factors1[i][2] ge 1) and (n1/factors1[i][1] gt N1)) do
			factors1[i][2] -:= 1;
			n1 /:= factors1[i][1];
		end while;
		while ((factors2[i][2] ge 1) and (n2/factors2[i][1] gt N2)) do
			factors2[i][2] -:= 1;
			n2 /:= factors2[i][1];
		end while;
	end for;
	//Remove the useless factors
	f1:=factors1;
	f2:=factors2;
	for i in [1..#factors1] do
		if factors1[i][2] eq 0 then
			f1:=Exclude(f1,factors1[i]);
		end if;
	end for;
	for i in [1..#factors2] do
		if factors2[i][2] eq 0 then
			f2:=Exclude(f2,factors2[i]);
		end if;
	end for;
	return Integers()!n1,Integers()!n2,f1,f2;
end function;

//remove the used constraint in n1 from T
RemainingConstraint:=function(n1,f1,T,fT)
	newT:=Z!T/n1;
	pointeur:=1;
	newfT:=fT;
	excl:=[];
	for i in [1..#f1] do
		if pointeur ge ((#fT)+1) then
			fT;
			f1;
		end if;
		while f1[i][1] ne fT[pointeur][1] do
			pointeur+:=1;
			if pointeur ge ((#fT)+1) then
				fT;
				f1;
			end if;
		end while;
		if f1[i][2] eq fT[pointeur][2] then
			Append(~excl,fT[pointeur]);
		else
			newfT[pointeur][2]:=newfT[pointeur][2]-f1[i][2];
		end if;
	end for;
	for i in [1..#excl] do
		Exclude(~newfT,excl[i]);
	end for;
	return newT,newfT;
end function;

// Magma's trial division is weirdly slow for numbers with one huge prime factor, even if all the other factors are very small...
TrialDivision_:=function(n,B);
	if n eq 0 then
		return 0;
	end if;
	a := 1;
	b := Integers()!n;
	p := 2;
	while p le B do
		while ((b mod p) eq 0) do
			a *:= p;
			b := Integers()!(b/p);
		end while;
		p := NextPrime(p);
	end while;
	return a, b;
end function;


// given a positive integer, decide whether Cornacchia's algorithm will run efficiently on it
// current check is passed by pseudoprime times smooth factor
CornacciaNice:=function(n : bound := 500);
	// remove small factors
	small, large := TrialDivision_(n, bound);

	// check whether remaining factor is prime
	return IsProbablyPrime(large), large;
	// return IsProbablyPrime(n),n;
end function;

// Solve the norm equation over the special extremal order
// Ensures that for each pair <order, integer> in divisibility, output/integer is not in order
NormEquation_SpecialOrder:=function(w1,w2,M : divisibility := [])
	// recover parameters D,E,q
	E:=Integers()!(Norm(w2)); // in this special case, E is p
	a := 0; b := 0; c:= 0; d:= 0;
	// d:=0; if DEBUG ge 0 then "d:=-1 would be better here, but it is problematic when the algorithm is used in function QuaternionIsogenyPath below"; end if;

	L := StandardLattice(2);

	foundsol:=false;
	no_solution:=false;

	upper_bound:=Floor(M/E);
  short_vec:=ShortVectors(L,1, Maximum(upper_bound,1));
  Reverse(~short_vec);
  for v in short_vec do
    // v:=short_vec[#short_vec-i+1];
    n := M - E*v[2];

	if n lt 0 then
		return false,0;
	end if;
    foundsol:=CornacciaNice(n);
    if foundsol then
      foundsol,a,b:=NormEquation(1,n);   // computation repeated due to Magma syntax, can this be avoided?
      if foundsol then
        c := v[1][1];
        d := v[1][2];
        quat:=a+b*w1+c*w2+d*w1*w2;
        if &and[not(quat/d[2] in d[1]) : d in divisibility] then
        	return true, quat;
        end if;
      end if;
    end if;
  end for;

	return false,0;
end function;


// Same as above but for the special maximal order, and the norm is of the form M*L^e for e as small as possible
NormEquation_SpecialOrder_adaptive:=function(w1,w2,M,L)
	E:=Integers()!(Norm(w2)); // in this special case, E is p
	e := Maximum(0, Ceiling(Log(E/M)/Log(L)) + 1);
	cofactor := L^e;
	done := false;

	while (not done) do
		done, quat := NormEquation_SpecialOrder(w1,w2,Z!M*cofactor);
		e +:= 1;
		cofactor *:= L;
	end while;

	return true, quat, e;
end function;

//same as above but samples a random solution among all possibilities, the value of e is fixed
NormEquation_Special_Order_random_solution:=function(w1,w2,M,L,e)
  E:=Integers()!(Norm(w2));
  q:=Integers()!Norm(w1);
  bound:=Floor(Sqrt(M*L^e/(q*E))/2);
  found:=false;
  count:=1;
  while not found and count le bound^2 do
    count+:=1;
    c:=Random(-bound,bound); d:=Random(-bound,bound);
    n:= M*L^e - E*(c^2+q*d^2);
    foundsol:=CornacciaNice(n);
    if foundsol then
      foundsol,a,b:=NormEquation(1,n);   // computation repeated due to Magma syntax, can this be avoided?
      if foundsol then
        quat:=a+b*w1+c*w2+d*w1*w2;
        return true,quat;
      end if;
    end if;
  end while;
  return false,0;
end function;

//same as above but with some constraint
NormEquation_SpecialOrder_adaptiveConstraint:=function(w1,w2,M,T,fT : divisibility := [])
	E:=Integers()!(Norm(w2)); // in this special case, E is p
	cofactor := 1;
	done := false;
	rT:=T;
	frT:=fT;

	while (not done) and rT ge 2 do
		done, quat := NormEquation_SpecialOrder(w1,w2,M*cofactor : divisibility := divisibility);
		if done then
			return true, quat, cofactor,rT,frT;
		end if;
		cofactor *:=frT[1][1];
		rT,frT:=RemainingConstraint(frT[1][1],[<frT[1][1],1>],rT,frT);
	end while;

	return false, 0, 0,T,fT;
end function;


//compute the smallest equivalent ideal of prime norm, where the norm verifies a series of condition
EquivalentPrimeIdeal :=function(ideal, D, E, L : previous := 0,previousN:=1)
	order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));
	//BOUNDcoeff:=Ceiling(100*(Log(p))^(1/2));
	//if DEBUG ge 1 then "bound on coefficients for random linear combination is", BOUNDcoeff; end if;
	N:=Norm(ideal);
	foundsol:=false;
	alpha:=B!0;
	index := 0;
	BOUNDcoeff:=Ceiling(1*(Log(p))^(1/2));

	cnt:=100;
	repeat
		cnt +:= 1;
		vectors := Enumerate(ideal, Round(2^cnt));
	until #vectors gt Maximum(10,previous + 1);
	while not foundsol do
		vectors := Enumerate(ideal, Round(2^cnt));
		// cnt, #vectors;
		if DEBUG ge 1 then "number of candidates:", #vectors; end if;
    triedN := 1;
		for k in [previous+1..#vectors] do
      a := vectors[k];
      Na:=Integers()!(Norm(a)/N);
      if Na ne triedN then
 			    triedN:=Na;
 			    foundsol := (Na gt previousN+1) and IsProbablyPrime(Na) and (GCD(Na,D) eq 1) and (IsSquare(IntegerRing(D)!(Na*E))) and ((L eq -1) or not(IsSquare(IntegerRing(Na)!L)));
 			    if foundsol then
            alpha := a;
 				    index := k;
 				    break;
 			  end if;
     end if;

		end for;
		previous := #vectors;
		cnt +:= 1;
	end while;
	if DEBUG ge 1 then "cnt=",cnt; end if;
	ideal2:=LeftIdeal(order,[elt*Conjugate(alpha)/Norm(ideal): elt in Basis(ideal)]);
	if DEBUG ge 1 then "ideal 2 and ideal are isomorphic?",IsIsomorphic(ideal,ideal2); "new ideal of prime norm?",IsPrime(Integers()!Norm(ideal2));end if;
	ideal:=ideal2;
	N:=Integers()!Norm(ideal);
	if DEBUG ge 1 then "Norm(ideal)=",Norm(ideal); "Factorization is ", Factorization(Integers()!Norm(ideal)); end if;
	if DEBUG ge 1 then "Computed a prime norm ideal in the same class\n"; end if;
	return ideal, index,a;
end function;
//same as above but adds the constaint and the possibility to have a little of it in N
EquivalentPrimeIdealConstraint :=function(ideal, D, E, L,T : previous := 0,count_size:=0)
	order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));
	//BOUNDcoeff:=Ceiling(100*(Log(p))^(1/2));
	//if DEBUG ge 1 then "bound on coefficients for random linear combination is", BOUNDcoeff; end if;
	N:=Norm(ideal);
	foundsol:=false;
	alpha:=B!0;
	index := 0;
  cnt_fin:=0;
  cnt:=Maximum(1,count_size-1);
	repeat
		cnt +:= 1;
		vectors := Enumerate(ideal, Round(2^cnt));
	until #vectors gt Maximum(10,previous + 1);
	while not foundsol do
		// cnt, #vectors;
    triedN:=1;
		if DEBUG ge 1 then "number of candidates:", #vectors; end if;

		for k in [previous+1..#vectors] do
			a := vectors[k];
			Norma:=Integers()!(Norm(a)/N);
      if Norma ne triedN then
        triedN:=Norma;
  			// check condition
  			Na:=Norma;
  			// g:=1;
  			g:=GCD(T,Norma);
  			// g;
  			Na:=Z!(Norma/g);
  			foundsol :=  IsProbablyPrime(Na) and (IsSquare(IntegerRing(D)!(Na*E))) and ((L eq -1) or not(IsSquare(IntegerRing(Na)!L)));
  			if foundsol then
  				alpha := a;
  				index := k;
          cnt_fin:=cnt;
  				break;
  			end if;
      end if;
		end for;
		previous := #vectors;
		cnt +:= 1;
    vectors := Enumerate(ideal, Round(2^cnt));
	end while;
	if DEBUG ge 1 then "cnt=",cnt; end if;
	ideal2:=LeftIdeal(order,[elt*Conjugate(alpha)/Norm(ideal): elt in Basis(ideal)]);
	if DEBUG ge 1 then "ideal 2 and ideal are isomorphic?",IsIsomorphic(ideal,ideal2); "new ideal of prime norm?",IsPrime(Integers()!Norm(ideal2));end if;
	ideal:=ideal2;
	N:=Integers()!Norm(ideal);
	if DEBUG ge 1 then "Norm(ideal)=",Norm(ideal); "Factorization is ", Factorization(Integers()!Norm(ideal)); end if;
	if DEBUG ge 1 then "Computed a prime norm ideal in the same class\n"; end if;
	return ideal,index,a,g,cnt_fin;
end function;
//same as above but looks for the best constraint among a large panel of possible solutions
// not intended to be iterated on the contrary of previous one
EquivalentPrimeIdealConstraint2 :=function(ideal, D, E, L,T,iter,debug : previous := 0,count_size:=0)
  if debug then Factorization(Integers()!Norm(ideal)); end if;
  order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));
	//BOUNDcoeff:=Ceiling(100*(Log(p))^(1/2));
	//if DEBUG ge 1 then "bound on coefficients for random linear combination is", BOUNDcoeff; end if;
	N:=Integers()!Norm(ideal);
	foundsol:=false;
	alpha:=B!0;
	index := 0;
  cnt_fin:=0;
  cnt:=Maximum(1,count_size-1);
	repeat
		cnt +:= 1;
		vectors := Enumerate(ideal,Round(2^cnt));
	until #vectors gt Maximum(10,previous + 1);
  sol:=1;
  gsol:=1;
  foundone:=false;
  ind:=2;
  add:=0;

  // CORRECTION: NEED TO FOLLOWING TO AVOID ENUMERATING FOREVER VECTORS WITH BAD NORM

  norms := [Integers()!Norm(b) : b in Basis(ideal)];
  traces := [Integers()!Trace(b) : b in Basis(ideal)];
  content := [GCD(norms[i],traces[i]) : i in [1..4]];

  good_basis_elements := [Basis(ideal)[i] : i in [1..4] | GCD(content[i], N) eq 1];

  good_basis_element := 0;

  if IsEmpty(good_basis_elements) then
  	ctr := 1;
  	while ctr gt 0 do
  		elt := &+[Random(-ctr,ctr) * b : b in Basis(ideal)];
  		if (GCD(GCD(Integers()!Norm(elt),Integers()!Trace(elt)), N) eq 1) then
  			good_basis_elements := elt;
  			ctr := -1;
  		end if;
  		ctr +:= 1;
  	end while;
  else
  	good_basis_element := [b : b in good_basis_elements | Integers()!Norm(b) eq Minimum([Integers()!Norm(x) : x in good_basis_elements])][1];
  end if;
  if debug then "good elt norm :",Floor(Log(Norm(good_basis_element)/Norm(ideal))/Log(2)); end if;
  repeat
    vectors:=Enumerate(ideal,Round(2^(cnt+iter+add)));
    add+:=1;
    triedN:=1;
    for k in [ind..#vectors] do
      a := vectors[k];
      Norma:=Integers()!(Norm(a)/N);
      if debug then
        Na:=Norma;
        g:=GCD(T,Norma);
        Na:=Z!(Norma/g);
        "before:",Floor(Log(Na)/Log(2));
      end if;
      // if GCD(Norma, N) ne 1 then
      //   "adding good basis element !!!!!!!!!!!!!!!";
      // 	a +:= good_basis_element;
      // 	Norma:=Integers()!(Norm(a)/N);
      // end if;

      if Norma ne triedN then
        triedN:=Norma;
        // check condition

        Na:=Norma;
        g:=GCD(T,Norma);
        Na:=Z!(Norma/g);
        if debug then
          "after:",Floor(Log(Na)/Log(2));
        end if;
        foundsol :=  IsProbablyPrime(Na) and (Norma/N ne Floor(Norma/N)) and (IsSquare(IntegerRing(D)!(Na*E))) and ((L eq -1) or not(IsSquare(IntegerRing(Na)!L)));
        if foundsol then
          foundone:=true;
          if sol eq 1 then
            sol:=Na;
            gsol:=g;
            alpha:=a;
          elif Na le sol-1 then
            sol:=Na;
            gsol:=g;
            alpha:=a;
          end if;
        end if;
      end if;
    end for;
    ind:=#vectors;
  until foundone;
  return alpha,index,a,gsol,cnt_fin;
end function;

//same as above but with more conditions
EquivalentPrimeIdealExtended :=function(ideal, D, E, L : previous := 0)
	order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));
	//BOUNDcoeff:=Ceiling(100*(Log(p))^(1/2));
	//if DEBUG ge 1 then "bound on coefficients for random linear combination is", BOUNDcoeff; end if;
	N:=Norm(ideal);
	foundsol:=false;
	alpha:=B!0;
	index := 0;
	BOUNDcoeff:=Ceiling(1*(Log(p))^(1/2));

	cnt:= 2+Ceiling(Log(N)/Log(2));
	repeat
		cnt +:= 1;
		vectors := Enumerate(ideal, Round(2^cnt));
	until #vectors gt Maximum(10,previous + 1);
	while not foundsol do
		vectors := Enumerate(ideal, Round(2^cnt));
		// cnt, #vectors;
		if DEBUG ge 1 then "number of candidates:", #vectors; end if;

		for k in [previous+1..#vectors] do
			a := vectors[k];
			Na:=Integers()!(Norm(a)/N);
			// check condition
			foundsol :=  IsProbablyPrime(Na) and (LegendreSymbol(-E,Na) eq 1) and (LegendreSymbol(-D,Na) eq 1) and (GCD(Na,D) eq 1) and (IsSquare(IntegerRing(D)!(Na*E))) and ((L eq -1) or not(IsSquare(IntegerRing(Na)!L)));

			if foundsol then
				alpha := a;
				index := k;
				break;
			end if;
		end for;
		previous := #vectors;
		cnt +:= 1;
	end while;
	if DEBUG ge 1 then "cnt=",cnt; end if;
	ideal2:=LeftIdeal(order,[elt*Conjugate(alpha)/Norm(ideal): elt in Basis(ideal)]);
	if DEBUG ge 1 then "ideal 2 and ideal are isomorphic?",IsIsomorphic(ideal,ideal2); "new ideal of prime norm?",IsPrime(Integers()!Norm(ideal2));end if;
	ideal:=ideal2;
	N:=Integers()!Norm(ideal);
	if DEBUG ge 1 then "Norm(ideal)=",Norm(ideal); "Factorization is ", Factorization(Integers()!Norm(ideal)); end if;
	if DEBUG ge 1 then "Computed a prime norm ideal in the same class\n"; end if;
	return ideal,index,a;
end function;

//compute the ideal on O0 on the other side of the sidh diagram
ComputeSIDHDiagramIdealIngoing:=function(O0,O1,Ipsi,degphi,degpsi)
  alpha:=&+[Random(-CST,CST)*bas: bas in Basis(Ipsi)];
  while GCD([Floor(Norm(alpha)),degpsi^2]) ne degpsi do
    alpha:=&+[Random(-CST,CST)*bas: bas in Basis(Ipsi)];
  end while;
  J:=lideal<O0|[degpsi,alpha*degphi]>;
  return J;
end function;
//compute the ideal on the other side of the sidh diagram, starting from O0
ComputeSIDHDiagramIdealOutgoing:=function(O0,O1,Ipsi,degphi,degpsi)
  K:=Ipsi meet lideal<O1| degphi>;
  alpha:=&+[Random(-CST,CST)*bas: bas in Basis(K)];
  while GCD([Floor(Norm(alpha)),degpsi^2]) ne degpsi do
    alpha:=&+[Random(-CST,CST)*bas: bas in Basis(K)];
  end while;
  J:=lideal<O1|[degpsi,alpha/degphi]>;
  return J;
end function;
//finds the generator a the ideal
FindGenerator:=function(I,O,basis,N)
  arand:=&+[Random(-CST,CST)*basis[i]:i in [1..4]];
  while GCD([Floor(Norm(arand)),N^2]) ne N do
    arand:=&+[Random(-CST,CST)*basis[i]:i in [1..4]];
  end while;
  return arand;
end function;
FindGeneratorNoDenom:=function(I,O,basis,N)
  arand:=&+[Random(-10*CST,10*CST)*basis[i]:i in [1..4]];
  while GCD([Floor(Norm(arand)),N^2]) ne N or [Denominator(co): co in Coordinates(arand)] ne [1,1,1,1] do
    if GCD([Floor(Norm(arand)),N^2]) eq N then
      [Denominator(co): co in Coordinates(arand)];
    end if;

    arand:=&+[Random(-10*CST,10*CST)*basis[i]:i in [1..4]];
  end while;
  return arand;
end function;
//bijection from the quaternion order O0 to M_2(Z/NZ)
IsoMat := function(N,x,ZN,p,q)
  c:=Coordinates(x);
  cmod:= [Numerator(c[l])*InverseMod(Denominator(c[l]),N) mod N :l in [1..4]];
  sq:=0;
  Mat:=Matrix(Z,2,2,[0,0,0,0]);
    sqp:=Modsqrt(-p,N);
    sqq:=Modsqrt(-q,N);
    M1:=Matrix(ZN,2,2,[1,0,0,1]);
    M3:=Matrix(ZN,2,2,[sqp,0,0,-sqp]);
    M2:=Matrix(ZN,2,2,[0,sqq,sqq,0]);
    M4:=M2*M3;
    Mat:=cmod[1]*M1+cmod[2]*M2+cmod[3]*M3+cmod[4]*M4;
  return Mat;
end function;
//bijection from M_2(Z/NZ) to O0
IsoQuat:=function(A,M,N,p,q)
  Mnu1:=ChangeRing(M,Z);
  nu1:=A![(Mnu1[1,1]+Mnu1[2,2])*InverseMod(2,N) mod N,(Mnu1[2,1]+Mnu1[1,2])*InverseMod(2*Modsqrt(-1,N),N) mod N,
  (Mnu1[1,1]-Mnu1[2,2])*InverseMod(2*Modsqrt(-p,N),N) mod N,
  (Mnu1[2,1]-Mnu1[1,2])*InverseMod(2*Modsqrt(-1,N)*Modsqrt(-p,N),N) mod N];
  return nu1;
end function;
//bijection from the quaternion order O0 to M_2(Z/NZ) when N is a power of 2 (works only when p = 7 mod 8)
SplitIsoMat:=function(O,l,x,Zl,p)
  if p mod 8 ne 7 then
    "wrong congruence mod 8";
  end if;
  b1:=Basis(O);
  alpha:=[];
  co1:=Coordinates(2*b1[1]);
  co2:=Coordinates(2*b1[2]);
  co3:=Coordinates(2*b1[3]);
  co4:=Coordinates(2*b1[4]);
  M:=Matrix(Z,4,4,[Floor(co1[1]),Floor(co1[2]),Floor(co1[3]),Floor(co1[4]),Floor(co2[1]),Floor(co2[2]),Floor(co2[3]),Floor(co2[4]),Floor(co3[1]),Floor(co3[2]),Floor(co3[3]),Floor(co3[4]),Floor(co4[1]),Floor(co4[2]),Floor(co4[3]),Floor(co4[4])]);
  coeff:=Coordinates(2*x);
  v:=[Floor(coeff[i]): i in [1..4]];
  v:=Vector(Z,v);
  w:=Solution(M,v);

  c:=Coordinates(x);
  cmod:= [Numerator(c[n])*InverseMod(Denominator(c[n]),l) mod l :n in [1..4]];
  sq:=Modsqrt(-p,l);
  M1:=Matrix(Zl,2,2,[1,0,0,1]);
  M3:=Matrix(Zl,2,2,[sq,0,0,-sq]);
  M2:=Matrix(Zl,2,2,[0,1,-1,0]);
  M4:=M2*M3;
  Mat:=cmod[1]*M1+cmod[2]*M2+cmod[3]*M3+cmod[4]*M4;
  test:=sq mod l;
  t1:=Z!((1+test mod l)/2) ;
  t2:=Z!((1-test mod l)/2) ;
  M3bis:=Matrix(Zl,2,2,[t1,0,0,t2]);
  M4bis:=Matrix(Zl,2,2,[0,t2,-t1,0]);

  return Mat;
end function;



// Improved KLPT algorithm from O0
//L=-1 : smooth, otherwise search for an ideal of prime power L
QuaternionIsogenyPath_special:=function(order,w1,w2, input_ideal, L)
	// main parameters
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index_prime_ideal:=0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	while repeatforcp do
		// "round ", counter;
		counter +:= 1;
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;

		// t:=Cputime();
		ideal,index_prime_ideal,_ := EquivalentPrimeIdeal(input_ideal, D, E, L : previous := index_prime_ideal);
		N := Integers()!Norm(ideal);
		// t:=Cputime();
		boo, gamma, e1:= NormEquation_SpecialOrder_adaptive(w1,w2,N,3);
		L1 := 3^e1;

		if not(boo) then
			"WARNING: NormEquation_SpecialOrder could not solve equation";
			continue;
		end if;


		MARGIN:=1.01;// maybe 1.01 is safer?
		L2 := Ceiling((N^3*p)^MARGIN);
		if L eq -1 then
			L1,L2 := PowerSmoothPair(L1,L2);
		else
			L1 := L^(Ceiling(Log(L1)/Log(L)));
			L2 := L^(Ceiling(Log(L2)/Log(L)));
		end if;
		L1 := 3^e1;


		//
		// "length N: ", Ceiling(Log(N)/Log(2));
		// "length 1: ", Ceiling(Log(L1)/Log(2));
		// "length 2: ", Ceiling(Log(L2)/Log(2));
		// "Total : ", Ceiling(Log(L1*L2)/Log(2));



		if DEBUG ge 1 then
			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
		end if;
		//"MaximalOrder(B) is", Basis(MaximalOrder(B));



		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
		Z:=Integers();
		vecsys:=[Z!0: ind in [1..4]];
		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
		matsys:=[Z!(elt*lcm): elt in matsys];
		vecsys:=Matrix(Z,1,4, vecsys);
		matsys:=Matrix(Z,8,4, matsys);

		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
		if DEBUG ge 2 then "ker is", ker; end if;

		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
		// normally the third one is the one we are after
		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
		//if DEBUG ge 2 then "solution to system is",sol; end if;
		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;

		beta:=C0*w2  + D0*w1*w2;
		if GCD(N,Integers()!Norm(gamma*beta)) ne N then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;

		if (GCD(N,Integers()!Norm(beta)) ne 1) then
			if DEBUG ge 1 then "beta is in N*order"; end if;
			continue;
		end if;
		t:=Cputime();
		factor:=Z!(C0^2*p + D0^2*p) ;
		// adjust e2 as needed to have a solution for lambda

		// the second condition makes sure we can still solve for cp
		if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor)) then
			accumulator := [];
			while true do
				small_prime := NextBestPrimeForPowersmooth(L1*L2 : notIn := accumulator);
				accumulator := Append(accumulator,small_prime);
				if IsSquare(IntegerRing(N)!L2*small_prime*factor) then
					L2 *:= small_prime;
					break;
				end if;
			end while;

		else
			if not(IsSquare(IntegerRing(N)!L2*factor)) then
				L2*:=L;
			end if;

			if (not IsSquare(IntegerRing(N)!L2*factor)) then
				if DEBUG ge 0 then "no solution for lambda"; end if;
				// N,D,E,C0,D0,D1;
				continue;
			end if;
		end if;

		lambda:=Z!Sqrt(IntegerRing(N)!L2/factor);


		if DEBUG ge 1 then
			"computed beta";//"beta=",beta;
		end if;
		if DEBUG ge 1 then
			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
		end if;
		// loop on cp
		foundsol:=false;

		ap:=0; bp:=0;


		coeff_c := 2*p*lambda*C0;
		coeff_d := 2*p*lambda*D0;
		constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);

		coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);

		cp0 := 0;
		dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);



		//"TEST", BB1,CC0;
		lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
		//"TEST", lattice_basis, Rank(lattice_basis);

		lattice := LatticeWithBasis(lattice_basis);
		target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);

		closest := ClosestVectors(lattice,-target);


		distance := Norm(closest[1] + target);

		cp := Integers()!((closest[1][1])/N)+cp0;
		dp := Integers()!((closest[1][2])/N)+dp0;

		//Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2);


		// check RHT norm
		if DEBUG ge 3 then
			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
		end if;

		//if DEBUG ge 0 then "RHT=",RHT; end if;


		//while not(foundsol) and (cnt le 100) do

		// find a bunch of candidates
		close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;



		for v in close do
			cp := Integers()!((v[1][1])/N)+cp0;
			dp := Integers()!((v[1][2])/N)+dp0;

			if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

			RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

			if RHT lt 0 then break; end if; // gotta try again with a new N...
			if CornacciaNice(RHT) then
				foundsol,ap,bp:=NormEquation(q,RHT);
				if foundsol then
					repeatforcp:=false;
					break;
				end if;
			end if;
		end for;

		//end while;

		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
		// Cputime(t);
		if foundsol then
			if DEBUG ge 1 then "found a solution for betap"; end if;

			// build betap
			a:=N*ap;
			b:=N*bp;
			c:=N*cp + lambda*C0;
			d:=N*dp + lambda*D0;
			betap:=a+b*w1+c*w2+d*w1*w2;
			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

			// build ideal
			alphabar:=Conjugate(gamma*betap);
			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
			newideal:=LeftIdeal(order,[elt1*alphabar/N: elt1 in Basis(ideal)]);
			// IsMaximal(order);

			// check solution
			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
		end if;
	end while;

	return newideal;
end function;
//same as above but with some constraint on the output's norm
//thus only work for powersmoo
//The constraint is T and the factors are rT (here T is the square of the available torsion on small extensions)
//SEEMS like this version is slightly less efficient than the v2.0 below
QuaternionIsogenyPath_specialConstraint:=function(order,w1,w2, input_ideal,L, T,fT)
	// main parameters
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index_prime_ideal:=0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	total:=0;
  total2:=0;
  cnt:=240;
	while repeatforcp do
		// "round ", counter;
		counter +:= 1;
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;


		ideal,index_prime_ideal,_,g,cnt := EquivalentPrimeIdealConstraint(input_ideal, D, E, L,T : previous := index_prime_ideal,count_size:=cnt);
		rT,frT:=RemainingConstraint(g,Factorization(g),T,fT);
    t:=Cputime();
		ideal_g:=lideal<RightOrder(ideal)|1>;
    total+:=Cputime(t);
		ideal_red:=ideal;
    //if necessary compute the complementray of norm g, it will be used at the end, when a solution is found
		if g ge 2 then
			gen:=FindGenerator(ideal,LeftOrder(ideal),Basis(ideal),Z!Norm(ideal));
			ideal_g:=lideal<RightOrder(ideal)|[gen,g]>;
			ideal_red:=ideal*ideal_g;
			ideal_red:=LeftIdeal(order,[elt1/g: elt1 in Basis(ideal_red)]);
			ideal:=ideal_red;
		end if;
		N := Integers()!Norm(ideal);
    // Ceiling(Log(N)/Log(2));
    //compute the constraint
		MARGIN:=1.01;
		L1,L2,f1,f2:=PowerSmoothPairConstraint(Ceiling(100*p/N),Ceiling((p*N^3)^MARGIN),rT,frT);
		rT,frT:=RemainingConstraint(L1,f1,rT,frT);
		rT,frT:=RemainingConstraint(L2,f2,rT,frT);
    //compute the representative gamma of norm N*L1
		boo, gamma, cof,rT,frT:= NormEquation_SpecialOrder_adaptiveConstraint(w1,w2,N*L1,rT,frT);

		L1 := L1*cof;
		if not(boo) then
			// "WARNING: NormEquation_SpecialOrder could not solve equation with the constraint";
			continue;
		end if;

		if DEBUG ge 1 then
			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
		end if;
		//"MaximalOrder(B) is", Basis(MaximalOrder(B));

		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
		vecsys:=[Z!0: ind in [1..4]];
		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
		matsys:=[Z!(elt*lcm): elt in matsys];
		vecsys:=Matrix(Z,1,4, vecsys);
		matsys:=Matrix(Z,8,4, matsys);

		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
		if DEBUG ge 2 then "ker is", ker; end if;

		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
		// normally the third one is the one we are after
		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
		//if DEBUG ge 2 then "solution to system is",sol; end if;
		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;

		beta:=C0*w2  + D0*w1*w2;
		if GCD(N,Integers()!Norm(gamma*beta)) ne N then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;

		if (GCD(N,Integers()!Norm(beta)) ne 1) then
			if DEBUG ge 0 then "beta is in N*order"; end if;
			continue;
		end if;
		t:=Cputime();
		factor:=Z!(C0^2*p + D0^2*p) ;
		// adjust e2 as needed to have a solution for lambda

		// the second condition makes sure we can still solve for cp
		foundsol:=false;
		liberty:=true;
		if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor)) then
			for i in [1..#frT] do
				if IsSquare(IntegerRing(N)!L2*factor*frT[i][1]) then
					L2:=L2*frT[i][1];
					rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
					break;
				end if;
			end for;
			liberty:=false;
			// print("No Solution for making a square mod N");
		else
			if not(IsSquare(IntegerRing(N)!L2*factor)) then
				L2*:=L;
			end if;
			if (not IsSquare(IntegerRing(N)!L2*factor)) then
				if DEBUG ge 0 then "no solution for lambda"; end if;
				// N,D,E,C0,D0,D1;
				continue;
			end if;
		end if;
		if DEBUG ge 1 then
			"computed beta";//"beta=",beta;
		end if;
		if DEBUG ge 1 then
			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
		end if;
		// loop on L2

		while not foundsol and liberty do
			if L1*L2 ne 0 then
				// T/(L1*L2);
			end if;
			if frT eq [] then liberty:=false; end if;
			lambda:=Z!Sqrt(IntegerRing(N)!L2/factor);
			ap:=0; bp:=0;
			coeff_c := 2*p*lambda*C0;
			coeff_d := 2*p*lambda*D0;
			constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);
			coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);
			cp0 := 0;
			dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);
		//"TEST", BB1,CC0;
			lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
		//"TEST", lattice_basis, Rank(lattice_basis);
			lattice := LatticeWithBasis(lattice_basis);
			target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);
			closest := ClosestVectors(lattice,-target);
			distance := Norm(closest[1] + target);
			cp := Integers()!((closest[1][1])/N)+cp0;
			dp := Integers()!((closest[1][2])/N)+dp0;
			if DEBUG ge 3 then
			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
			end if;
		// find a bunch of candidates
			close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;
			for v in close do
				cp := Integers()!((v[1][1])/N)+cp0;
				dp := Integers()!((v[1][2])/N)+dp0;

				if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

				RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

				if RHT lt 0 then break; end if; // gotta try again with a new N...
				if CornacciaNice(RHT) then
					foundsol,ap,bp:=NormEquation(q,RHT);
					if foundsol then
						repeatforcp:=false;
						break;
					end if;
				end if;
			end for;
			if not foundsol then
				incremented:=false;
				for i in [1..#frT] do
					if frT[i][2] ge 2 then
						L2*:=frT[i][1]^2;
						rT,frT:=RemainingConstraint(frT[i][1]^2,[<frT[i][1],2>],rT,frT);
						incremented:=true;
					elif IsSquare(IntegerRing(N)!L2*factor*frT[i][1]) then
						L2*:=frT[i][1];
						rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
						incremented:=true;
					end if;
					if incremented then
						break;
					end if;
				end for;
				if not incremented and #frT ge 2 then
					if IsSquare(IntegerRing(N)!L2*factor*frT[1][1]*frT[2][1]) then
						L2*:=frT[1][1]*frT[2][1];
						rT,frT:=RemainingConstraint(frT[1][1]*frT[2][1],[<frT[1][1],1>,<frT[2][1],1>],rT,frT);
					end if;
				elif not incremented and #frT ge 1 then
					liberty:=false;
				end if;
			end if;
		end while;
		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
		// Cputime(t);
		//finish the computation once a solution is found
		if foundsol then
			if DEBUG ge 1 then "found a solution for betap"; end if;
			// build betap
			a:=N*ap;
			b:=N*bp;
			c:=N*cp + lambda*C0;
			d:=N*dp + lambda*D0;
			betap:=a+b*w1+c*w2+d*w1*w2;
			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

			// build ideal
			alphabar:=Conjugate(gamma*betap);
			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
			newideal:=LeftIdeal(order,[elt1*alphabar/N: elt1 in Basis(ideal)]);
			ideal_g:=Conjugate(ideal_g);
			// ideal_g:=ideal_g*lideal<RightOrder(ideal_g)|alphabar/N>;
			// ideal_g:=rideal<LeftOrder(ideal_g)|Conjugate(alphabar)*N/Norm(alphabar)>* ideal_g;
			ideal_g:=LeftIdeal(RightOrder(newideal),[Conjugate(alphabar)*elt1*alphabar/Norm(alphabar): elt1 in Basis(ideal_g)]);
			newideal:=newideal*ideal_g;
			// check solution
			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
		end if;
	end while;
	return newideal;
end function;

//same as above, a slighlty different rerandomization dynamic, we hope it will allow to compute a smallest ideal
//Seems more efficent than v1.0 above
QuaternionIsogenyPath_specialConstraint2:=function(order,w1,w2, input_ideal,L, T,fT:good_input:=false)
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index_prime_ideal:=0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	total:=0;
  total2:=0;
  cnt:=2+Ceiling(Log(Integers()!Norm(input_ideal))/Log(2));
  iter:=1;
	while repeatforcp do
		// "round ", counter;
		counter +:= 1;
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;
    alpha:=1;
    ideal:=input_ideal;
    tT:=T;
    ftT:=fT;
    norm_input_ideal:=1;
    if not good_input then
      alpha,index_prime_ideal,_,g,_ := EquivalentPrimeIdealConstraint2(input_ideal, D, E, L,T,iter,false : previous := index_prime_ideal,count_size:=cnt);
      tT,ftT:=RemainingConstraint(g,Factorization(g),T,fT);
		  ideal:=lideal<order|[Conjugate(alpha),Norm(alpha)/(g*Norm(input_ideal))]>;
      norm_input_ideal:=Norm(input_ideal);
    end if;
    N := Integers()!Norm(ideal);
    // Floor(Log(N)/Log(2));
    if Floor(Log(N)/Log(2)) ge Floor(Log(p)/Log(2)) then

      "size of N:",Floor(Log(N)/Log(2));
      "size of input_ideal", Floor(Log(Norm(input_ideal))/Log(2));
      index:=Floor(Log(p)/Log(2));
      vector:=Enumerate(input_ideal,2^index);
      repeat
        index+:=1;
        vector:=Enumerate(input_ideal,2^index);
      until #vector gt 1;
      "size of smalles equivalent ideal:",Floor(Log(Norm(vector[2])/Norm(input_ideal))/Log(2));
      "trying again....";
      alpha,index_prime_ideal,_,g,_ := EquivalentPrimeIdealConstraint2(input_ideal, D, E, L,T,iter,true : previous := index_prime_ideal,count_size:=cnt);
      tT,ftT:=RemainingConstraint(g,Factorization(g),T,fT);
  		ideal:=lideal<order|[Conjugate(alpha),Norm(alpha)/(g*Norm(input_ideal))]>;
  		N := Integers()!Norm(ideal);
      "size of N:",Floor(Log(N)/Log(2));
    end if;
    //compute the constraint
		MARGIN:=1.01;
    foundsol:=false;
    while not foundsol do
  		L1,L2,f1,f2:=PowerSmoothPairConstraint(Ceiling(100*p/N),Ceiling((p*N^3)^MARGIN),tT,ftT);
  		rT,frT:=RemainingConstraint(L1,f1,tT,ftT);
  		rT,frT:=RemainingConstraint(L2,f2,rT,frT);
      //compute the representative gamma of norm N*L1
  		boo, gamma, cof,rT,frT:= NormEquation_SpecialOrder_adaptiveConstraint(w1,w2,N*L1,rT,frT);
      L1 := L1*cof;
  		if not(boo) then
  			// "WARNING: NormEquation_SpecialOrder could not solve equation with the constraint";
  			continue;
  		end if;
  		if DEBUG ge 1 then
  			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
  			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
  		end if;
  		//"MaximalOrder(B) is", Basis(MaximalOrder(B));
  		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
  		vecsys:=[Z!0: ind in [1..4]];
  		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
  		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
  		matsys:=[Z!(elt*lcm): elt in matsys];
  		vecsys:=Matrix(Z,1,4, vecsys);
  		matsys:=Matrix(Z,8,4, matsys);

  		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
  		if DEBUG ge 2 then "ker is", ker; end if;
  		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
  		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
  		// normally the third one is the one we are after
  		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
  		//if DEBUG ge 2 then "solution to system is",sol; end if;
  		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;
      beta:=C0*w2  + D0*w1*w2;
  		if GCD(N,Integers()!Norm(gamma*beta)) ne N then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;

  		if (GCD(N,Integers()!Norm(beta)) ne 1) then
  			if DEBUG ge 0 then "beta is in N*order"; Factorization(N); C0^2 + D0^2 mod N; end if;
  			continue;
  		end if;
  		t:=Cputime();
  		factor:=Z!(C0^2*p + D0^2*p) ;
  		// adjust e2 as needed to have a solution for lambda

  		// the second condition makes sure we can still solve for cp
  		liberty:=true;
  		if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor)) then
  			for i in [1..#frT] do
  				if IsSquare(IntegerRing(N)!L2*factor*frT[i][1]) then
  					L2:=L2*frT[i][1];
  					rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
  					break;
  				end if;
  			end for;
  			liberty:=false;
  			// print("No Solution for making a square mod N");
  		else
  			if not(IsSquare(IntegerRing(N)!L2*factor)) then
  				L2*:=L;
  			end if;
  			if (not IsSquare(IntegerRing(N)!L2*factor)) then
  				if DEBUG ge 0 then "no solution for lambda"; end if;
  				// N,D,E,C0,D0,D1;
  				continue;
  			end if;
  		end if;
  		if DEBUG ge 1 then
  			"computed beta";//"beta=",beta;
  		end if;
  		if DEBUG ge 1 then
  			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
  		end if;
  		// loop on L2

  		while not foundsol and liberty do
  			if L1*L2 ne 0 then
  				// T/(L1*L2);
  			end if;
  			if frT eq [] then liberty:=false; end if;
  			lambda:=Z!Sqrt(IntegerRing(N)!L2/factor);
  			ap:=0; bp:=0;
  			coeff_c := 2*p*lambda*C0;
  			coeff_d := 2*p*lambda*D0;
  			constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);
  			coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);
  			cp0 := 0;
  			dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);
  			lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
  			lattice := LatticeWithBasis(lattice_basis);
  			target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);
  			closest := ClosestVectors(lattice,-target);
  			distance := Norm(closest[1] + target);
  			cp := Integers()!((closest[1][1])/N)+cp0;
  			dp := Integers()!((closest[1][2])/N)+dp0;
  			if DEBUG ge 3 then
  			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
  			end if;
  		// find a bunch of candidates
  			close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
  		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;
  			for v in close do
  				cp := Integers()!((v[1][1])/N)+cp0;
  				dp := Integers()!((v[1][2])/N)+dp0;

  				if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

  				RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

  				if RHT lt 0 then break; end if; // gotta try again with a new N...
  				if CornacciaNice(RHT) then
  					foundsol,ap,bp:=NormEquation(q,RHT);
  					if foundsol then
  						repeatforcp:=false;
  						break;
  					end if;
  				end if;
  			end for;
  			if not foundsol then
  				incremented:=false;
  				for i in [1..#frT] do
  					if frT[i][2] ge 2 then
  						L2*:=frT[i][1]^2;
  						rT,frT:=RemainingConstraint(frT[i][1]^2,[<frT[i][1],2>],rT,frT);
  						incremented:=true;
  					elif IsSquare(IntegerRing(N)!L2*factor*frT[i][1]) then
  						L2*:=frT[i][1];
  						rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
  						incremented:=true;
  					end if;
  					if incremented then
  						break;
  					end if;
  				end for;
  				if not incremented and #frT ge 2 then
  					if IsSquare(IntegerRing(N)!L2*factor*frT[1][1]*frT[2][1]) then
  						L2*:=frT[1][1]*frT[2][1];
  						rT,frT:=RemainingConstraint(frT[1][1]*frT[2][1],[<frT[1][1],1>,<frT[2][1],1>],rT,frT);
  					end if;
  				elif not incremented and #frT ge 1 then
  					liberty:=false;
  				end if;
  			end if;
  		end while;
  		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
  		// Cputime(t);
  		//finish the computation once a solution is found
  		if foundsol then
  			if DEBUG ge 1 then "found a solution for betap"; end if;
  			// build betap
  			a:=N*ap;
  			b:=N*bp;
  			c:=N*cp + lambda*C0;
  			d:=N*dp + lambda*D0;
  			betap:=a+b*w1+c*w2+d*w1*w2;
  			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

  			// build ideal
  			alphabar:=Conjugate(gamma*betap);
        alphabar2:=Conjugate(gamma*Conjugate(betap));
  			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
        newideal:=LeftIdeal(order,[elt1*Conjugate(alpha)*alphabar/(N*norm_input_ideal): elt1 in Basis(input_ideal)]);
  			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
  		end if;
    end while;
	end while;

	return newideal;
end function;

//same as above but when the norm of the ideal in input is a small power of 2. In this case, we cannot find a prime equivalent ideal of small norm a  and so we use the input ideal instead.
//The norm being not prime is a bit problematic for some steps but it should be manageable.



QuaternionIsogenyPath_specialConstraint_small2power_input:=function(order,w1,w2, input_ideal,L, T,fT)
	B<i,j,k>:=Parent(Basis(order)[1]);

	if (input_ideal + order*2) ne (order*(i+1) + order*2) then
		// we make sure the ideal is a fixed point for the action of (R/2R)^*
		input_ideal_corrected := lideal<order | [b*(i+1) : b in Basis(input_ideal)]>;
		//"no trouble?",IsIsomorphic(input_ideal, input_ideal_corrected);
		input_ideal := input_ideal_corrected;
	end if;

	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index_prime_ideal:=0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	total:=0;
  total2:=0;
  cnt:=2+Ceiling(Log(Integers()!Norm(input_ideal))/Log(2));
  iter:=1;
	while repeatforcp do
		counter +:= 1;
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;

    // alpha,index_prime_ideal,_,g,_ := EquivalentPrimeIdealConstraint2(input_ideal, D, E, L,T,iter : previous := index_prime_ideal,count_size:=cnt);
    // tT,ftT:=RemainingConstraint(g,Factorization(g),T,fT);
		// ideal:=lideal<order|[Conjugate(alpha),Norm(alpha)/(g*Norm(input_ideal))]>;
		// N := Integers()!Norm(ideal);
    alpha:=1;
    ideal:=input_ideal;
    N:=Integers()!Norm(ideal);
    tT:=T;
    ftT:=fT;
    //compute the constraint
		MARGIN:=1.01;
    foundsol:=false;
    while not foundsol do
  		L1,L2,f1,f2:=PowerSmoothPairConstraint(Ceiling(100*p/N),Ceiling((p*N^3)^MARGIN),tT,ftT);


  		rT,frT:=RemainingConstraint(L1,f1,tT,ftT);
  		rT,frT:=RemainingConstraint(L2,f2,rT,frT);
      //compute the representative gamma of norm N*L1
  		boo, gamma, cof,rT,frT:= NormEquation_SpecialOrder_adaptiveConstraint(w1,w2,Z!(N*L1),rT,frT: divisibility := [<order,2>]);
      L1 := L1*cof;
  		if not(boo) then
  			// "WARNING: NormEquation_SpecialOrder could not solve equation with the constraint";
  			continue;
  		end if;// //"MaximalOrder(B) is", Basis(MaximalOrder(B));
  		// // compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
  		vecsys:=[Z!0: ind in [1..4]];
  		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
  		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
  		matsys:=[Z!(elt*lcm): elt in matsys];
  		vecsys:=Matrix(Z,1,4, vecsys);
  		matsys:=Matrix(Z,8,4, matsys);
      zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
      A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
  		if DEBUG ge 2 then "ker is", ker; end if;
      while C0 mod 2 eq 0 and D0 mod 2 eq 0 do
        C0:=Z!(C0/2);
        D0:=Z!(D0/2);
        if not gamma*(C0*w2  + D0*w1*w2) in ideal then
          C0:=2*C0;
          D0:=2*D0;
          break;
        end if;
      end while;
      if C0 mod 2 eq 0 and D0 mod 2 eq 0 then
        continue;
      end if;
      if D0 mod 2 eq 0 then
        continue;
      end if;
  		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;
      beta:=C0*w2  + D0*w1*w2;
      if not gamma*beta in ideal then
        continue;
      end if;
  		if GCD(N,Integers()!Norm(gamma*beta)) ne N then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;
      // gamma*beta in ideal;
  		// if (GCD(N,Integers()!Norm(beta)) ne 1) then
  		// 	if DEBUG ge 0 then "beta is in N*order"; end if;
  		// 	continue;
  		// end if;
  		t:=Cputime();
  		factor:=Z!(C0^2*p + D0^2*p) ;

      // "a";
      // Valuation(factor,2);
      correct := 2^Valuation(factor,2);

      factor:=Z!(factor/correct);
  		// adjust e2 as needed to have a solution for lambda

  		// the second condition makes sure we can still solve for cp
  		liberty:=true;
  		if (L eq -1) and not(L2*Z!(factor) mod 8 eq 1) then
  			for i in [1..#frT] do
  				if L2*factor*frT[i][1] mod 8 eq 1 then
  					L2:=L2*frT[i][1];
  					rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
  					break;
  				end if;
  			end for;
  			liberty:=false;
  			// print("No Solution for making a square mod N");
  		else
  			if not (L2*factor mod 8 eq 1 ) then
  				L2*:=L;
  			end if;
  			if (not L2*factor mod 8 eq 1) then

  				if DEBUG ge 0 then "no solution for lambda"; end if;
  				// N,D,E,C0,D0,D1;
  				continue;
  			end if;
  		end if;
  		if DEBUG ge 1 then
  			"computed beta";//"beta=",beta;
  		end if;
  		if DEBUG ge 1 then
  			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
  		end if;
  		// loop on L2
      cnter:=1;
  		while not foundsol and liberty and cnter le 10 do
        cnter+:=1;
  			if L1*L2 ne 0 then
  				// T/(L1*L2);
  			end if;
  			if frT eq [] then liberty:=false; end if;
  			lambda:=Z!Sqrt(IntegerRing(Integers()!(N/correct))!(L2)/factor);
  			ap:=0; bp:=0;
  			coeff_c_half := p*lambda*C0;
  			coeff_d_half := p*lambda*D0;
  			constant_term := Z!((L2*correct - p*lambda^2*(D0^2 + C0^2))/(N));

  			if IsEven(constant_term) then

	  			coeff_d_half_inv := Z!(IntegerRing(N)!1/coeff_d_half);
	  			cp0 := 0;
	  			dp0 := Z!(IntegerRing(N)!(constant_term/2)*coeff_d_half_inv);

	  			lattice_basis := N*Matrix([[1, -coeff_c_half*coeff_d_half_inv mod N],[0,N]]);
	  			lattice := LatticeWithBasis(lattice_basis);
	  			target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);
	  			closest := ClosestVectors(lattice,-target);
	  			distance := Norm(closest[1] + target);
	  			cp := Integers()!((closest[1][1])/N)+cp0;
	  			dp := Integers()!((closest[1][2])/N)+dp0;
	  			if DEBUG ge 3 then
	  			"mod N^2 is", Z!(L2*correct-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
	  			end if;
	  		// find a bunch of candidates
	  			close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
	  		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;
	  			for v in close do
	  				cp := Integers()!((v[1][1])/N)+cp0;
	  				dp := Integers()!((v[1][2])/N)+dp0;

	  				if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

	  				RHT:=Z!((correct*L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

	  				if RHT lt 0 then break; end if; // gotta try again with a new N...
	  				if CornacciaNice(RHT) then
	  					foundsol,ap,bp:=NormEquation(q,RHT);
	  					if foundsol then
	  						repeatforcp:=false;
	  						break;
	  					end if;
	  				end if;
	  			end for;
  			end if;
  			if not foundsol then
  				incremented:=false;
  				for i in [1..#frT] do
  					if frT[i][2] ge 2 then
  						L2*:=frT[i][1]^2;
  						rT,frT:=RemainingConstraint(frT[i][1]^2,[<frT[i][1],2>],rT,frT);
  						incremented:=true;
  					elif L2*factor*frT[i][1] mod 8 eq 1 then
              L2*:=frT[i][1];
  						rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
  						incremented:=true;
  					end if;
  					if incremented then
  						break;
  					end if;
  				end for;
  				if not incremented and #frT ge 2 then
  					if L2*factor*frT[1][1]*frT[2][1] mod 8 eq 1 then
  						L2*:=frT[1][1]*frT[2][1];
  						rT,frT:=RemainingConstraint(frT[1][1]*frT[2][1],[<frT[1][1],1>,<frT[2][1],1>],rT,frT);
  					end if;
  				elif not incremented and #frT ge 1 then
  					liberty:=false;
  				end if;
  			end if;
  		end while;
  		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
  		// Cputime(t);
  		//finish the computation once a solution is found
  		if foundsol then

  			if DEBUG ge 1 then "found a solution for betap"; end if;
  			// build betap
  			a:=N*ap;
  			b:=N*bp;
  			c:=N*cp + lambda*C0;
  			d:=N*dp + lambda*D0;
  			betap:=a+b*w1+c*w2+d*w1*w2;
  			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;
  			// build ideal
  			alphabar:=Conjugate(gamma*betap);
        alphabar2:=Conjugate(gamma*Conjugate(betap));
  			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
        newideal:=LeftIdeal(order,[elt1*alphabar/(Norm(input_ideal)): elt1 in Basis(input_ideal)]);
  			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
  		end if;
    end while;
	end while;

	return newideal;
end function;


// When input_ideal + O0*2 is equal to the ideal generated by i+1, the output
// has norm dividing 2*T^2.
// Otherwise, it has norm dividing T^2.
// The issue comes from that particular ideal being a fixed point of the action
// of R/2*R on the O0-ideals of O0/2*O0 (where R is the ring of integers of QQ(i))
QuaternionIsogenyPath_specialConstraint2_small_power_of_2:=function(order,w1,w2, input_ideal,L, T,fT)
	B<i,j,k>:=Parent(Basis(order)[1]);

	if (input_ideal + order*2) ne (order*(i+1) + order*2) then
		// we make sure the ideal is a fixed point for the action of (R/2R)^*
		input_ideal_corrected := lideal<order | [b*(i+1) : b in Basis(input_ideal)]>;
		//"no trouble?",IsIsomorphic(input_ideal, input_ideal_corrected);
		input_ideal := input_ideal_corrected;
	end if;
	"IS FIXED POINT", (input_ideal + order*2) eq (order*(i+1) + order*2);

	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index_prime_ideal:=0;
	index_solution:= 0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	total:=0;
  	total2:=0;
  	cnt:=2+Ceiling(Log(Integers()!Norm(input_ideal))/Log(2));
  	iter:=1;
	ideal := input_ideal;
	N := Integers()!Norm(ideal);
	while repeatforcp do
		// "round ", counter;
		counter +:= 1;
		tT := T;
		ftT := fT;
    //compute the constraint
		MARGIN:=1.01;
   		foundsol:=false;
	    while not foundsol do
	  		L1,L2,f1,f2:=PowerSmoothPairConstraint(Ceiling(100*p/N),Ceiling((p*N^4)^MARGIN),tT,ftT);
	  		rT,frT:=RemainingConstraint(L1,f1,tT,ftT);
	  		rT,frT:=RemainingConstraint(L2,f2,rT,frT);
	      //compute the representative gamma of norm N*L1
	  		boo, gamma, cof,rT,frT:= NormEquation_SpecialOrder_adaptiveConstraint(w1,w2,N*L1,rT,frT: divisibility := [<order,2>]);
	      	L1 := L1*cof;
	  		if not(boo) then
	  			// "WARNING: NormEquation_SpecialOrder could not solve equation with the constraint";
	  			continue;
	  		end if;
	  		if DEBUG ge 1 then
	  			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
	  			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
	  		end if;
	  		//"MaximalOrder(B) is", Basis(MaximalOrder(B));
	  		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(gamma*beta),N)=N
	  		vecsys:=[Z!0: ind in [1..4]];
	  		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
	  		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
	  		matsys:=[Z!(elt*lcm): elt in matsys];
	  		vecsys:=Matrix(Z,1,4, vecsys);
	  		matsys:=Matrix(Z,8,4, matsys);

	  		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
	  		if DEBUG ge 2 then "ker is", ker; end if;
	  		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
	  		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
	  		// normally the third one is the one we are after
	  		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
	  		//if DEBUG ge 2 then "solution to system is",sol; end if;
	  		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;
	  		beta:=C0*w2  + D0*w1*w2;
	  		if GCD(N,Integers()!Norm(gamma*beta)) ne N then
	  			"WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", TrialDivision(GCD(N,Integers()!Norm(beta)),1000);
	  			//counter;
	  			//break;
	  		end if;
	  		 if not IsOdd(D0) then  // annoying situation, go to next attempt
				// TODO: maybe it is more efficient to actually deal with this case
				if DEBUG ge 1 then
					print "D0 is even, try again";
				end if;
				continue;
			end if;

	  		t:=Cputime();
			factor:=Integers()!(C0^2*p + D0^2*p);
			val_factor := Valuation(factor,2);
			factor := Integers()!(factor/2^val_factor);
	  		// adjust e2 as needed to have a solution for lambda


	  		// the second condition makes sure we can still solve for cp
	  		liberty:=true;
	  		if (L eq -1) and not(IsSquare(IntegerRing(Integers()!(N/2^val_factor))!L2*factor)) then
	  			for i in [1..#frT] do
	  				if IsSquare(IntegerRing(Integers()!(N/2^val_factor))!L2*factor*frT[i][1]) then
	  					L2:=L2*frT[i][1];
	  					rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
	  					break;
	  				end if;
	  			end for;
	  			liberty:=false;
	  			// print("No Solution for making a square mod N");
	  		elif ((L ne -1) and not(IsSquare(IntegerRing(Integers()!(N/2^val_factor))!L2*factor))) then
	  			L2*:=L;
	  			if (not IsSquare(IntegerRing(Integers()!(N/2^val_factor))!L2*factor)) then
	  				if DEBUG ge 1 then "no solution for lambda"; end if;
	  				// N,D,E,C0,D0,D1;
	  				continue;
	  			end if;
	  		end if;
	  		if DEBUG ge 1 then
	  			"computed beta";//"beta=",beta;
	  		end if;
	  		if DEBUG ge 1 then
	  			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
	  		end if;
	  		// loop on L2

	  		while not foundsol and liberty do
	  			if L1*L2 ne 0 then
	  				// T/(L1*L2);
	  			end if;
	  			if frT eq [] then liberty:=false; end if;
	  			lambda:=Z!Sqrt(Integers(Integers()!(N/2^val_factor))!L2/factor);
	  			ap:=0; bp:=0;
	  			coeff_c_half := p*lambda*C0;
	  			coeff_d_half := p*lambda*D0;
	  			constant_term := Z!((L2*2^val_factor - p*lambda^2*(D0^2 + C0^2))/N);

	  			if IsEven(constant_term) then


		  			// we made sure D0 is odd
					coeff_d_half_inv := Integers()!(IntegerRing(N)!(1/coeff_d_half));
					cp0 := 0;
					dp0 := Integers()!(IntegerRing(N)!(Integers()!(constant_term/2)*coeff_d_half_inv));



		  			lattice_basis := N*Matrix([[1, -coeff_c_half*coeff_d_half_inv mod N],[0,N]]);
		  			lattice := LatticeWithBasis(lattice_basis);
		  			target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);
		  			closest := ClosestVectors(lattice,-target);
		  			distance := Norm(closest[1] + target);
		  			cp := Integers()!((closest[1][1])/N)+cp0;
		  			dp := Integers()!((closest[1][2])/N)+dp0;
		  			if DEBUG ge 3 then
		  			"mod N^2 is", Z!(L2*2^val_factor-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
		  			end if;
		  		// find a bunch of candidates
		  			close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		  		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;
		  			for v in close do
		  				cp := Integers()!((v[1][1])/N)+cp0;
		  				dp := Integers()!((v[1][2])/N)+dp0;

		  				if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

		  				RHT:=Z!((L2*2^val_factor-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

		  				if RHT lt 0 then break; end if; // gotta try again with a new N...
		  				if CornacciaNice(RHT) then
		  					foundsol,ap,bp:=NormEquation(q,RHT);
		  					if foundsol then
		  						repeatforcp:=false;
		  						break;
		  					end if;
		  				end if;
		  			end for;
	  			end if;


	  			if not foundsol then
	  				incremented:=false;
	  				for i in [1..#frT] do
	  					if frT[i][2] ge 2 then
	  						L2*:=frT[i][1]^2;
	  						rT,frT:=RemainingConstraint(frT[i][1]^2,[<frT[i][1],2>],rT,frT);
	  						incremented:=true;
	  					elif IsSquare(IntegerRing(N)!L2*factor*frT[i][1]) then
	  						L2*:=frT[i][1];
	  						rT,frT:=RemainingConstraint(frT[i][1],[<frT[i][1],1>],rT,frT);
	  						incremented:=true;
	  					end if;
	  					if incremented then
	  						break;
	  					end if;
	  				end for;
	  				if not incremented and #frT ge 2 then
	  					if IsSquare(IntegerRing(N)!L2*factor*frT[1][1]*frT[2][1]) then
	  						L2*:=frT[1][1]*frT[2][1];
	  						rT,frT:=RemainingConstraint(frT[1][1]*frT[2][1],[<frT[1][1],1>,<frT[2][1],1>],rT,frT);
	  					end if;
	  				elif not incremented and #frT ge 1 then
	  					liberty:=false;
	  				end if;
	  			end if;

	  		end while;
	  		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
	  		// Cputime(t);
	  		//finish the computation once a solution is found
	  		if foundsol then
	  			if DEBUG ge 1 then "found a solution for betap"; end if;
	  			// build betap
	  			a:=N*ap;
	  			b:=N*bp;
	  			c:=N*cp + lambda*C0;
	  			d:=N*dp + lambda*D0;
	  			betap:=a+b*w1+c*w2+d*w1*w2;
	  			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

	  			// build ideal
	  			alphabar:=Conjugate(gamma*betap);
	        	alphabar2:=Conjugate(gamma*Conjugate(betap));
	  			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
	  			alpha := 1;
	        			//newideal:=LeftIdeal(order,[elt1*Conjugate(alpha)*alphabar/(N*Norm(input_ideal)): elt1 in Basis(input_ideal)]);
	  					newideal:=LeftIdeal(order,[elt1*alphabar/N: elt1 in Basis(ideal)]);

	  			// // a small correction required in some cases
	  			// if IsEven(Integers()!Norm(newideal)) then
	  			//newideal := lideal<order | [b/(i+1) : b in Basis(newideal)]>;
	  			// end if;

	  			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
	  		end if;
	    end while;
	end while;

	return newideal;
end function;


// same as above but modified to be called from the extension to the generic case below
//does not handle well the powersmooth case
QuaternionIsogenyPath_special_for_Extended:=function(order,w1,w2, input_ideal,L: index_prime_ideal := 0,good_input:=false)
	// main parameters
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	index:=index_prime_ideal;
  No:=1;
	while repeatforcp do
		// "round ", counter;
		counter +:= 1;
		// replace ideal by another one in same class with prime norm + extra residuosity conditions on norm
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;
		// the index_prime_ideal allows to find new prime ideals each round, starting with the smallest one and increasing
    ideal:=input_ideal;
    delta:=1;
    if not good_input then
      ideal,index,delta := EquivalentPrimeIdeal(input_ideal, D, E, L : previous := index,previousN:=No);
    end if;
    N := Z!Norm(ideal);
    No:=N;
    // "id", index_prime_ideal;


		// find gamma with norm N\ell^{2e1} in nice suborder
		boo, gamma, e1:= NormEquation_SpecialOrder_adaptive(w1,w2,N,2);
		// Cputime(t);
		L1 := L^e1;
		if not(boo) then
			"WARNING: NormEquation_SpecialOrder could not solve equation";
			continue;
		end if;
		MARGIN:=1.01;// maybe 1.01 is safer?
		L2 := Ceiling((N^3*p)^MARGIN);
    L2 := L^(Ceiling(Log(L2)/Log(L)));
		// if L eq -1 then
		// 	L1,L2 := PowerSmoothPair(L1,L2);
		// else
		// 	L1 := L^(Ceiling(Log(L1)/Log(L)));
		//
		// end if;
		// L1 := 3^e1;

		if DEBUG ge 1 then
			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
		end if;
		//"MaximalOrder(B) is", Basis(MaximalOrder(B));



		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
		vecsys:=[Z!0: ind in [1..4]];
		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
		matsys:=[Z!(elt*lcm): elt in matsys];
		vecsys:=Matrix(Z,1,4, vecsys);
		matsys:=Matrix(Z,8,4, matsys);

		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
		if DEBUG ge 2 then "ker is", ker; end if;

		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
		// normally the third one is the one we are after
		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
		//if DEBUG ge 2 then "solution to system is",sol; end if;
		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;

		beta:=C0*w2  + D0*w1*w2;
		if GCD(N,Integers()!Norm(gamma*beta)) ne N then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;

		if (GCD(N,Integers()!Norm(beta)) ne 1) then
			if DEBUG ge 0 then "beta is in N*order"; end if;
			continue;
		end if;
		factor:=Z!(C0^2*p + D0^2*p) ;
		// adjust e2 as needed to have a solution for lambda

		// the second condition makes sure we can still solve for cp
		if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor)) then
			accumulator := [];
			while true do
				small_prime := NextBestPrimeForPowersmooth(L1*L2 : notIn := accumulator);
				accumulator := Append(accumulator,small_prime);
				if IsSquare(IntegerRing(N)!L2*small_prime*factor) then
					L2 *:= small_prime;
					break;
				end if;
			end while;

		else
			if not(IsSquare(IntegerRing(N)!L2*factor)) then
				L2*:=L;
			end if;

			if (not IsSquare(IntegerRing(N)!L2*factor)) then
				if DEBUG ge 0 then "no solution for lambda"; end if;
				// N,D,E,C0,D0,D1;
				continue;
			end if;
		end if;

		lambda:=Z!Sqrt(IntegerRing(N)!L2/factor);


		if DEBUG ge 1 then
			"computed beta";//"beta=",beta;
		end if;
		if DEBUG ge 1 then
			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
		end if;
		// loop on cp
		foundsol:=false;

		ap:=0; bp:=0;


		coeff_c := 2*p*lambda*C0;
		coeff_d := 2*p*lambda*D0;
		constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);

		coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);

		cp0 := 0;
		dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);



		//"TEST", BB1,CC0;
		lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
		//"TEST", lattice_basis, Rank(lattice_basis);

		lattice := LatticeWithBasis(lattice_basis);
		target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);

		closest := ClosestVectors(lattice,-target);


		distance := Norm(closest[1] + target);

		cp := Integers()!((closest[1][1])/N)+cp0;
		dp := Integers()!((closest[1][2])/N)+dp0;

		//Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2);


		// check RHT norm
		if DEBUG ge 3 then
			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
		end if;

		//if DEBUG ge 0 then "RHT=",RHT; end if;


		//while not(foundsol) and (cnt le 100) do

		// find a bunch of candidates
		close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;

		for v in close do
			cp := Integers()!((v[1][1])/N)+cp0;
			dp := Integers()!((v[1][2])/N)+dp0;

			if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

			RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

			if RHT lt 0 then break; end if; // gotta try again with a new N...
			if CornacciaNice(RHT) then
				foundsol,ap,bp:=NormEquation(q,RHT);
				if foundsol then
					repeatforcp:=false;
					break;
				end if;
			end if;
		end for;

		//end while;

		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
		if foundsol then
			if DEBUG ge 1 then "found a solution for betap"; end if;

			// build betap
			a:=N*ap;
			b:=N*bp;
			c:=N*cp + lambda*C0;
			d:=N*dp + lambda*D0;
			betap:=a+b*w1+c*w2+d*w1*w2;
			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

			// build ideal
			alphabar:=Conjugate(gamma*betap);
			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
			newideal:=LeftIdeal(order,[elt1*alphabar/N: elt1 in Basis(ideal)]);

			// IsMaximal(order);

			// check solution
			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
		end if;
	end while;

	return newideal,ideal,gamma*betap,delta,L1*L2,index;
end function;

//solves the two constraints at once to optimize the size of the output
QuaternionIsogenyPath_special_for_Extended2:=function(order,w1,w2, input_ideal,NormConnectingIdeal,connecting_ideal,L: index_prime_ideal := 0,additional_factor:=1)
	// main parameters
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	index:=index_prime_ideal;
  No:=1;
  ideal,index,delta := EquivalentPrimeIdeal(input_ideal, D, E, L : previous := index,previousN:=No);
  N := Z!Norm(ideal);
  No:=N;
	while repeatforcp do
    N:=No;
		counter +:= 1;
		// replace ideal by another one in same class with prime norm + extra residuosity conditions on norm
		if DEBUG ge 1 then "Computing a prime norm ideal in same class (+additional congruence conditions)"; end if;
		// the index_prime_ideal allows to find new prime ideals each round, starting with the smallest one and increasing

		// "id", index_prime_ideal;
		// find gamma with norm N\ell^{e1} in nice suborder
    e1:=Floor(Log(p/N)/Log(L))+CST_RANDOMIZATION_GAMMA;
    boo,gamma:=NormEquation_Special_Order_random_solution(w1,w2,N,L,e1);

		// boo, gamma, e1:= NormEquation_SpecialOrder_adaptive(w1,w2,Z!N*additional_factor,2);
		// Cputime(t);
		L1 := L^e1;

		if not(boo) then
			"WARNING: NormEquation_SpecialOrder could not solve equation";
			continue;
		end if;
		MARGIN:=1.01;// maybe 1.01 is safer?
		L2 := Ceiling(((N*NormConnectingIdeal)^3*p)^MARGIN);

		if L eq -1 then
			L1,L2 := PowerSmoothPair(L1,L2);
		else
			L1 := L^(Ceiling(Log(L1)/Log(L)));
			L2 := L^(Ceiling(Log(L2)/Log(L)));
		end if;
		if DEBUG ge 1 then
			"computed gamma"; //"gamma=",gamma; "Norm(gamma)=",Norm(gamma);
			"gamma in nice suborder?", gamma in QuaternionOrder([1,w1,w2,w1*w2]);
		end if;
		//"MaximalOrder(B) is", Basis(MaximalOrder(B));

		// compute beta in <N,Nw1,w2,w1w2> such that gamma*beta in ideal with GCD(n(beta),N)=N
		vecsys:=[Z!0: ind in [1..4]];
		matsys:=&cat([Eltseq(quat): quat in [gamma*N,gamma*N*w1,gamma*w2,gamma*w1*w2] cat Basis(ideal)]);
		lcm:=LeastCommonMultiple([Denominator(elt) : elt in matsys]);
		matsys:=[Z!(elt*lcm): elt in matsys];
		vecsys:=Matrix(Z,1,4, vecsys);
		matsys:=Matrix(Z,8,4, matsys);

		zero, ker:= Solution(matsys,vecsys); 		// should implement the case where no solution: find another gamma
    if DEBUG ge 2 then "ker is", ker; end if;

		// normally solution space is 4-dimensional, returned as a Gauss-reduced basis
		// we are not interested in the first basis vectors having nonzero coefficients in front of N*gamma and/or N*gamma*w1
		// normally the third one is the one we are after
		A0,B0,C0,D0,a,b,c,d:=Explode(Eltseq(Basis(ker)[3]));
		//if DEBUG ge 2 then "solution to system is",sol; end if; we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	   // counter := 1;
		if (A0 ne 0) or (B0 ne 0) or (C0 eq 0) or (D0 eq 0) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected"; end if;

    Np:=Z!NormConnectingIdeal;
    ZNp:=quo<Z|Np>;
    //second part of the modulus computations
    eichler_order:=lideal<LeftOrder(connecting_ideal)|1> meet lideal<RightOrder(connecting_ideal)|1>;

    vecsys_test:=[Z!0: ind in [1..4]];
    matsys_test:=&cat([Eltseq(quat): quat in [gamma*Np,gamma*Np*w1,gamma*w2,gamma*w1*w2] cat [bas*Conjugate(delta): bas in Basis(eichler_order)] ]);
    lcm_test:=LeastCommonMultiple([Denominator(elt) : elt in matsys_test]);
		matsys_test:=[Z!(elt*lcm_test): elt in matsys_test];
		vecsys_test:=Matrix(Z,1,4, vecsys_test);
		matsys_test:=Matrix(Z,8,4, matsys_test);
		zero, ker_test:= Solution(matsys_test,vecsys_test);
    _,_,Ctest,Dtest,_,_,_,_:=Explode(Eltseq(Basis(ker_test)[3]));
    // Ctest;
    // Dtest;
    // nu_test:=Ctest*w2+ Dtest*w1*w2;
    // gamma*nu_test*delta in eichler_order;


	  // M:=IsoMat(Np,gamma,ZNp,E,D);
    // Md:=IsoMat(Np,delta,ZNp,E,D);
    // Md:=Md*1/(ZNp!N);
    // Mdm1:=Matrix(ZNp,2,2,[Md[2,2],-Md[1,2],-Md[2,1],Md[1,1]]);
    // Mdm1:=Mdm1*(1/Determinant(Md));
    // gen:=FindGenerator(connecting_ideal,order,Basis(connecting_ideal),Np);
	  // Mgen:=IsoMat(Np,gen,ZNp,E,D);
    // y:=Random(Np);
    // x:=Mgen[1,1]*y/Mgen[1,2];
	  // lambda1:=Random(ZNp);
	  // MMM:=Matrix(ZNp,4,4,[M[1,1],M[1,2],-(x*Mdm1[1,1]+Mdm1[2,1]*y),0,-M[1,2],-M[1,1],-(x*Mdm1[1,2]+y*Mdm1[2,2]),0,M[2,1],M[2,2],0,
    // -(x*Mdm1[1,1]+Mdm1[2,1]*y),-M[2,2],-M[2,1],0,-(x*Mdm1[1,2]+y*Mdm1[2,2])]);
	  // MMM:=Transpose(MMM);
	  // vec:=Vector(ZNp,[-lambda1*Mdm1[1,1],-lambda1*Mdm1[1,2],-lambda1*Mdm1[2,1],-lambda1*Mdm1[2,2]]);
	  // w:=Solution(MMM,vec);
	  // lambda1:=Z!lambda1;
    //
    // w:=ChangeRing(w,Integers());
    //
	  // nu:=IsoQuat(B,Matrix(ZNp,2,2,[w[1],-w[2],w[2],-w[1]]),Np,E,D);
    // coeff:=Coordinates(nu);
    // gamma*nu*delta in eichler_order;
    //
		// //CAREFUL This step is wrong if we are not working for p = 3 mod 4
    //
    C0N:=C0;
    D0N:=D0;
    //
    // C0p:=Z!coeff[3];
		// D0p:=Z!coeff[4];
    // ((C0p mod Np)*InverseMod(D0p,Np)) mod Np eq ((Ctest mod Np)*InverseMod(Dtest,Np)) mod Np;
    C0p:=Ctest mod Np;
    D0p:=Dtest mod Np;

    C0:=CRT([C0N,C0p],[N,Np]);
    D0:=CRT([D0N,D0p],[N,Np]);
    factor:=Z!(C0^2*p + D0^2*p);

    // b1,_:=IsSquare(IntegerRing(N)!factor);
    // b2,_:=IsSquare(IntegerRing(Np)!factor);
    // while b1 ne b2 do
    //   x:=Random(1,N-1);
    //   y:=Random(1,N-1);NewKLPT
    //   C0Nt := (C0N*x + D0N*y);
    //   D0Nt := -(C0N*y - D0N*x);
    //
    //   (C0Nt*w2+D0Nt*w1*w2);
    //   (C0N*w2+D0N*w1*w2)*(x+i*y);
    //   gamma*(C0N*w2+D0N*w1*w2) in ideal;
    //   gamma*(C0N*w2+D0N*w1*w2)*(x+i*y) in ideal;
    //   C0:=CRT([C0Nt,C0p],[N,Np]);
    //   D0:=CRT([D0Nt,D0p],[N,Np]);
    //   factor:=Z!(C0^2*p + D0^2*p);
    //
    //   b1,_:=IsSquare(IntegerRing(N)!factor);
    //   b2,_:=IsSquare(IntegerRing(Np)!factor);
    //   "try again";
    //
    // end while;

		beta:=C0*w2  + D0*w1*w2;
    // gamma*beta*delta in eichler_order;
    // gamma*beta in ideal;
    // gamma*beta*delta/N in LeftOrder(ideal);
    // gamma*beta*delta/N+lambda1 in connecting_ideal;
    N:=N*Np;
    // Factorization(N);
    // Factorization(Z!Norm(gamma*beta));
    // GCD(N,Integers()!Norm(gamma*beta));
		if GCD(N,Integers()!Norm(gamma*beta)) ne Z!(N/Np) then "WARNING in QuaternionIsogenyPath: solution for beta is not as expected. GCD is", Factorization(GCD(N,Integers()!Norm(beta))); end if;

		if (GCD(N,Integers()!Norm(beta)) ne 1) then
			if DEBUG ge 0 then "beta is in N*order"; end if;
			continue;
		end if;

    factorisationN:=[<Np,1>,<Z!(N/Np ),1>];
    // "test for compatibility :";
    // IsSquare(IntegerRing(Np)!factor);
    // IsSquare(IntegerRing(Z!(N/Np))!factor);

		// adjust e2 as needed to have a solution for lambda

		// the second condition makes sure we can still solve for cp
		// if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor:Factorization:=factorisationN)) then
		// 	accumulator := [];
		// 	while true do
		// 		small_prime := NextBestPrimeForPowersmooth(L1*L2 : notIn := accumulator);
		// 		accumulator := Append(accumulator,small_prime);
		// 		if IsSquare(IntegerRing(N)!L2*small_prime*factor:Factorization:=factorisationN) then
		// 			L2 *:= small_prime;
		// 			break;
		// 		end if;
		// 	end while;
    //
		// else
		// 	if not(IsSquare(IntegerRing(N)!L2*factor:Factorization:=factorisationN)) then
		// 		L2*:=L;
		// 	end if;
    //
		// 	if (not IsSquare(IntegerRing(N)!L2*factor:Factorization:=factorisationN)) then
		// 		if DEBUG ge 0 then
    //       // "no solution for lambda";
    //     end if;
		// 		// N,D,E,C0,D0,D1;
		// 		continue;
		// 	end if;
		// end if;
    e2:=CST_DEGREE-e1;
    L2:=L^e2;
    // factorisationN;
    if not IsSquare( IntegerRing(N)!(L2)/IntegerRing(N)!factor:Factorization:=factorisationN) then
      continue;
    end if;
    // "number of attempts before reaching this point :",counter;
		lambda:=Z!Sqrt(IntegerRing(N)!L2/factor:Factorization:=factorisationN);


		if DEBUG ge 1 then
			"computed beta";//"beta=",beta;
		end if;
		if DEBUG ge 1 then
			"I=ON+O*gamma*beta?", ideal eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
		end if;
		// loop on cp
		foundsol:=false;

		ap:=0; bp:=0;


		coeff_c := 2*p*lambda*C0;
		coeff_d := 2*p*lambda*D0;
		constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);

		coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);

		cp0 := 0;
		dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);


		//"TEST", BB1,CC0;
		lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
		//"TEST", lattice_basis, Rank(lattice_basis);

		lattice := LatticeWithBasis(lattice_basis);
		target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);

		closest := ClosestVectors(lattice,-target);


		distance := Norm(closest[1] + target);

		cp := Integers()!((closest[1][1])/N)+cp0;
		dp := Integers()!((closest[1][2])/N)+dp0;

		//Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2);


		// check RHT norm
		if DEBUG ge 3 then
			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
		end if;

		//if DEBUG ge 0 then "RHT=",RHT; end if;


		//while not(foundsol) and (cnt le 100) do

		// find a bunch of candidates
		close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;


		for v in close do
			cp := Integers()!((v[1][1])/N)+cp0;
			dp := Integers()!((v[1][2])/N)+dp0;

			if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;

			RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));

			if RHT lt 0 then break; end if; // gotta try again with a new N...
			if CornacciaNice(RHT) then
				foundsol,ap,bp:=NormEquation(q,RHT);
				if foundsol then
					repeatforcp:=false;
					break;
				end if;
			end if;
		end for;

		//end while;

		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
		if foundsol then
			if DEBUG ge 1 then "found a solution for betap"; end if;

			// build betap
			a:=N*ap;
			b:=N*bp;
			c:=N*cp + lambda*C0;
			d:=N*dp + lambda*D0;
			betap:=a+b*w1+c*w2+d*w1*w2;
			if DEBUG ge 1 then "gamma*betap in ideal?",gamma*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

			// build ideal
			alphabar:=Conjugate(gamma*betap);
			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
			newideal:=LeftIdeal(order,[elt1*alphabar/N: elt1 in Basis(ideal)]);

			// IsMaximal(order);

			// check solution
			if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
		end if;
	end while;

	return newideal,ideal,gamma*betap,delta,L1*L2,index;
end function;
//Improved KLPT algorithm for a generic order
//does not handle well the powersmooth case
QuaternionIsogenyPath_special_Extended:=function(order,w1,w2,input_ideal,connecting_ideal,L)
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index:=0;
	repeatforcp:=true;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	N:=Z!Norm(connecting_ideal);
	ZN:=quo<Z|N>;
	input_ideal_order:=ComputeSIDHDiagramIdealIngoing(order,LeftOrder(input_ideal),input_ideal,N,Z!Norm(input_ideal));

	MARGIN:=1.01;// maybe 1.01 is safer?
	L2 := Ceiling((N^3*p)^MARGIN);
	e2:=Ceiling(Log(L2)/Log(L));
	L2 := L^e2;
	counter:=1;
	// alpha in input_ideal_order*lideal<RightOrder(input_ideal_order)|Conjugate(delta)/Norm(input_ideal_order)>;
	while repeatforcp do
		// "round", counter;
		counter:=counter+1;
		new_ideal_order,prime_input_ideal_order,alpha,delta,L1,index:=QuaternionIsogenyPath_special_for_Extended(order,w1,w2,input_ideal_order,N,connecting_ideal,L:index_prime_ideal:=index);
		alpha:=alpha*delta*Norm(input_ideal_order)/Norm(delta);
	  M:=IsoMat(N,alpha,ZN,E,D);
	  gen:=FindGenerator(connecting_ideal,order,Basis(connecting_ideal),N);
	  Mgen:=IsoMat(N,gen,ZN,E,D);
	  x:=Mgen[1,1]/Mgen[1,2];
	  y:=1;
	  v:=Random(ZN);
	  MMM:=Matrix(ZN,3,3,[M[1,1]+M[2,2],-M[1,2]-M[2,1],-x,-M[2,1],M[1,1],0,M[1,2],-M[2,2],-y]);
	  MMM:=Transpose(MMM);
	  vec:=Vector(ZN,[-v*y,v*x,0]);
	  w:=Solution(MMM,vec);
	  Mlamb:=Matrix(ZN,2,2,[w[1],-w[2],w[2],-w[1]])*M - Matrix(ZN,2,2,[w[3]*x,w[3]*y,v*x,v*y]);
	  Mlamb:=ChangeRing(Mlamb,Integers());
	  lambda1:=Mlamb[1,1];
	  w:=ChangeRing(w,Integers());
	  nu:=IsoQuat(B,Matrix(ZN,2,2,[w[1],-w[2],w[2],-w[1]]),N,E,D);
		coeff:=Coordinates(nu);

		//CAREFUL This step is wrong if we are not working for p = 3 mod 4
		C0:=Z!coeff[3];
		D0:=Z!coeff[4];

		beta:=C0*w1  + D0*w2*w1;
		factor:=Z!(C0^2*p + D0^2*p) ;
		// adjust e2 as needed to have a solution for lambda

		// the second condition makes sure we can still solve for cp
		if (L eq -1) and not(IsSquare(IntegerRing(N)!L2*factor)) then
			accumulator := [];
			while true do
				small_prime := NextBestPrimeForPowersmooth(L1*L2 : notIn := accumulator);
				accumulator := Append(accumulator,small_prime);
				if IsSquare(IntegerRing(N)!L2*small_prime*factor) then
					L2 *:= small_prime;
					break;
				end if;
			end while;
		else
			if not(IsSquare(IntegerRing(N)!L2*factor)) then
        cnt:=1;
        L2*:=L;
			end if;

			if (not IsSquare(IntegerRing(N)!L2*factor)) then
				if DEBUG ge 0 then "no solution for lambda"; end if;
				continue;
			end if;
		end if;
		lambda:=Z!Sqrt(IntegerRing(N)!L2/factor);

		if DEBUG ge 1 then
			"computed beta";//"beta=",beta;
		end if;
		// if DEBUG ge 1 then
		// 	"I=ON+O*gamma*beta?", input_ideal_order eq LeftIdeal(order,[elt*N:elt in Basis(order)] cat [elt*gamma*beta: elt in Basis(order)]);
		// end if;
		// loop on cp
		foundsol:=false;
		ap:=0; bp:=0;
		coeff_c := 2*p*lambda*C0;
		coeff_d := 2*p*lambda*D0;
		constant_term := Z!((L2 - p*lambda^2*(D0^2 + C0^2))/N);
		coeff_d_inv := Z!(IntegerRing(N)!1/coeff_d);
		cp0 := 0;
		dp0 := Z!(IntegerRing(N)!constant_term*coeff_d_inv);
		lattice_basis := N*Matrix([[1, -coeff_c*coeff_d_inv mod N],[0,N]]);
		lattice := LatticeWithBasis(lattice_basis);
		target := lambda*Vector([C0,D0]) + N*Vector([cp0,dp0]);
		closest := ClosestVectors(lattice,-target);
		distance := Norm(closest[1] + target);
		cp := Integers()!((closest[1][1])/N)+cp0;
		dp := Integers()!((closest[1][2])/N)+dp0;
		if DEBUG ge 3 then
			"mod N^2 is", Z!(L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) mod N^2 ;
		end if;
		close := CloseVectors(lattice,-target, Round(Round(Log(p)/2)*distance) : Max := Round(Log(p)*10));
		// if DEBUG ge 0 then "number of close vectors found:",#close; end if;
		for v in close do
			cp := Integers()!((v[1][1])/N)+cp0;
			dp := Integers()!((v[1][2])/N)+dp0;
			if DEBUG ge 2 then "possible e2 =", Log(p*((lambda*C0+cp*N)^2+(lambda*D0+dp*N)^2))/Log(2); end if;
			RHT:=Z!((L2-(lambda*C0+cp*N)^2*p-(lambda*D0+dp*N)^2*p ) / (N^2));
			if RHT lt 0 then break; end if; // gotta try again with a new N...
			if CornacciaNice(RHT) then
				foundsol,ap,bp:=NormEquation(q,RHT);
				if foundsol then
					repeatforcp:=false;
					break;
				end if;
			end if;
		end for;
		//end while;
		//if cnt eq 10^6 then "ERROR in QuaternionIsogenyPath: no solution found where RHT had solutions"; return 0; end if;
		if foundsol then
			if DEBUG ge 1 then "found a solution for betap"; end if;
			a:=N*ap;
			b:=N*bp;
			c:=N*cp + lambda*C0;
			d:=N*dp + lambda*D0;
			betap:=a+b*w1+c*w2+d*w1*w2;
			// if DEBUG ge 1 then "gamma*betap in ideal?",alpha*betap in ideal; "GCD(norm,N)/N=", GCD(Z!Norm(gamma*betap),N)/N; end if;

			alphabar:=Conjugate(betap*alpha);

			if DEBUG ge 1 then "Norm(alphabar)=",Norm(alphabar); Factorization(Z!Norm(alphabar)); end if;
			// Conjugate(alphabar) in prime_input_ideal_order;
			newideal:=input_ideal_order*lideal<RightOrder(input_ideal_order)|[alphabar/Norm(input_ideal_order)]>;

			newideal:=ComputeSIDHDiagramIdealOutgoing(order,LeftOrder(input_ideal),newideal,N,Z!Norm(newideal));
			// IsMaximal(order);

			// check solution
			// if DEBUG ge 1 then "new ideal and ideal are isomorphic?",IsIsomorphic(newideal,ideal); "Factorization(norm)=",Factorization(Z!Norm(newideal));end if;
		end if;
	end while;
	return newideal;
end function;
QuaternionIsogenyPath_special_Extended2:=function(order,w1,w2,input_ideal,connecting_ideal,L:addit_factor:=1)
  B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Integers()!Max(Norm(B.1),Norm(B.2));
	q := 1;
	D := 1;
	E := p;
	index:=0;
	foundsol:=false;	// below we will need cp to satisfy some quadratic residuosity assumption; heuristically we hope it will hold every other time
	counter := 1;
	N:=Z!Norm(connecting_ideal);
	ZN:=quo<Z|N>;
	input_ideal_order:=ComputeSIDHDiagramIdealIngoing(order,LeftOrder(input_ideal),input_ideal,N,Z!Norm(input_ideal));

	MARGIN:=1.01;// maybe 1.01 is safer?
	L2 := Ceiling((N^3*p)^MARGIN);
	e2:=Ceiling(Log(L2)/Log(L));
	L2 := L^e2;
	counter:=1;
	// alpha in input_ideal_order*lideal<RightOrder(input_ideal_order)|Conjugate(delta)/Norm(input_ideal_order)>;
	while not foundsol do
		// "round", counter;
		counter:=counter+1;
		new_ideal_order,prime_input_ideal_order,alpha,delta,L1,index:=QuaternionIsogenyPath_special_for_Extended2(order,w1,w2,input_ideal_order,N,connecting_ideal,L:index_prime_ideal:=index,additional_factor:=addit_factor);
		alpha:=alpha*delta*Norm(input_ideal_order)/Norm(delta);
    newideal:=input_ideal_order*lideal<RightOrder(input_ideal_order)|[Conjugate(alpha)/Norm(input_ideal_order)]>;
    newideal:=ComputeSIDHDiagramIdealOutgoing(order,LeftOrder(input_ideal),newideal,N,Z!Norm(newideal));
		foundsol,_:=IsLeftIsomorphic(newideal,input_ideal);
	end while;
	return newideal;
end function;





TestQuaternionIsogenyPath_special:=procedure()
	repeat
		p:=RandomPrime(256);
	until ((p mod 4) eq 3);
	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
	order := MaximalOrder(B);
	w1 := i;
	w2:= j;
	total:=0;
	n:=20;
	for i in [1..n] do
		i;
		// "Reducing\n\n";
		order2:=ReducedMaximalOrder(RandomOrder(B));
		// compute ideal connecting the two orders
		ideal := ConnectingIdeal(order,order2);
		// "\n\n";
		// "Starting the computation\n\n";
		t:=Cputime();
		new_ideal,_ := QuaternionIsogenyPath_special(order,w1,w2,ideal,2);
		total:=total+Cputime(t);
	end for;
	total/n;
	// 	binarylen := Round(Log(Norm(new_ideal))/Log(2));
	// "Binary length of new ideal:", binarylen;
end procedure;
TestQuaternionIsogenyPath_specialConstraint:=procedure()
	repeat
		p:=RandomPrime(256);
	until ((p mod 4) eq 3);
	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
	order := MaximalOrder(B);
	w1 := i;
	w2:= j;
	total:=0;
	n:=50;
	N:=Random(2^394,2^395);
	T:=NextPowerSmooth(N);
	T:=T^2;
	fT:=Factorization(T);
	size:=0;
	max:=size;
	for i in [1..n] do
		ideal:=RandomIdeal(order,2,300);
    cnt:=300;
    alpha:=0;
    found:=false;
    while alpha eq 0 do
      x:=Enumerate(ideal,2^cnt);
      cnt:=cnt+1;
      if #x ge 2 then
        alpha:=x[2];
      end if;
    end while;
    ideal:=LeftIdeal(order,[elt1*Conjugate(alpha)/Norm(ideal):elt1 in Basis(ideal)]);
		t:=Cputime();
		new_ideal,_ := QuaternionIsogenyPath_specialConstraint(order,w1,w2,ideal,-1,T,fT);
		total:=total+Cputime(t);
		b,_:=IsLeftIsomorphic(ideal,new_ideal);
		if not b then
			print("algo is not working");
		end if;
		e:=Ceiling(Log(Norm(new_ideal))/Log(2));
		size:=size+e;
		if e ge max then
			max:=e;
		end if;
    binarylen := Round(Log(Norm(new_ideal))/Log(2));
    // binarylen;
	// "ideal:", binarylen;
		// "result size :",Ceiling(Log(Norm(new_ideal))/Log(2));
		// "remaining torsion : ",T/Norm(new_ideal);
	end for;
	total/n;
	Floor(size/n);
	max;
end procedure;

TestQuaternionIsogenyPath_specialConstraint2:=procedure()
	repeat
		p:=RandomPrime(256);
	until ((p mod 4) eq 3);
	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
	order := QuaternionOrder([1,i,(1+k)/2,(i+j)/2]);
	w1 := i;
	w2:= j;
	total:=0;
  total2:=0;
	n:=2;
	N:=Random(2^394,2^395);
	T:=NextPowerSmooth(N);
	T:=T^2;
	fT:=Factorization(T);
	size:=0;
	max:=size;
	for i in [1..n] do
		ideal:=RandomIdeal(order,2,320);
    cnt:=2+Ceiling(Log(Integers()!Norm(ideal))/Log(2));
    alpha:=0;
    found:=false;
    while alpha eq 0 do
      x:=Enumerate(ideal,2^cnt);
      cnt:=cnt+1;
      if #x ge 2 then
        alpha:=x[2];
      end if;
    end while;
    //fideal:=LeftIdeal(order,[elt1*Conjugate(alpha)/Norm(ideal):elt1 in Basis(ideal)]);
    t:=Cputime();
    //"on";
		new_ideal,_ := QuaternionIsogenyPath_specialConstraint2(order,w1,w2,ideal,-1,T,fT);

    //"off";
		total:=total+Cputime(t);
		b,_:=IsLeftIsomorphic(ideal,new_ideal);
		if not b then
			print("algo is not working");
		end if;
		e:=Ceiling(Log(Norm(new_ideal))/Log(2));
		size:=size+e;
		if e ge max then
			max:=e;
		end if;
    binarylen := Round(Log(Norm(new_ideal))/Log(2));
    // binarylen;
	// "ideal:", binarylen;
		// "result size :",Ceiling(Log(Norm(new_ideal))/Log(2));
		// "remaining torsion : ",T/Norm(new_ideal);
	end for;
	total/n;
	Floor(size/n);
	// max;1
end procedure;

TestQuaternionIsogenyPath_specialConstraint2_small_power_of_2:=procedure()
	repeat
		p:=RandomPrime(256);
	until ((p mod 4) eq 3);
	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
	order := QuaternionOrder([1,i,(1+k)/2,(i+j)/2]);
	w1 := i;
	w2:= j;
	total:=0;
  total2:=0;
	n:=1;
	N:=Random(2^394,2^395);
	T:=NextPowerSmooth(N);
	T:=T^2;
	fT:=Factorization(T);
	size:=0;
	max:=size;
	for i in [1..n] do
		ideal:=RandomIdeal(order,2,64);
    cnt:=2+Ceiling(Log(Integers()!Norm(ideal))/Log(2));
    alpha:=0;
    found:=false;
    while alpha eq 0 do
      x:=Enumerate(ideal,2^cnt);
      cnt:=cnt+1;
      if #x ge 2 then
        alpha:=x[2];
      end if;
    end while;
    //fideal:=LeftIdeal(order,[elt1*Conjugate(alpha)/Norm(ideal):elt1 in Basis(ideal)]);
    t:=Cputime();
    //"on";
		new_ideal,_ := QuaternionIsogenyPath_specialConstraint_small2power_input(order,w1,w2,ideal,-1,T,fT);

    //"off";

		b,_:=IsLeftIsomorphic(ideal,new_ideal);
    if [bas in LeftOrder(ideal): bas in Basis(new_ideal)] ne [true,true,true,true] then
      print("the ideal in output is not integral");
    end if;
		if not b then
			print("algo is not working");
		end if;
		e:=Ceiling(Log(Norm(new_ideal))/Log(2));
		"val", Valuation(Integers()!Norm(new_ideal), 2);
		size:=size+e;
		if e ge max then
			max:=e;
		end if;
    binarylen := Round(Log(Norm(new_ideal))/Log(2));
    // binarylen;
	// "ideal:", binarylen;
		// "result size :",Ceiling(Log(Norm(new_ideal))/Log(2));
		// "remaining torsion : ",T/Norm(new_ideal);
	end for;
	Floor(size/n);
	// max;1

end procedure;


//
// TestQuaternionIsogenyPath_specialConstraint2_small_power_of_2:=procedure()
// 	repeat
// 		p:=RandomPrime(256);
// 	until ((p mod 4) eq 3);
// 	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
// 	order := QuaternionOrder([1,i,(1+k)/2,(i+j)/2]);;
// 	w1 := i;
// 	w2:= j;
// 	total:=0;
//   total2:=0;
// 	n:=2;
// 	N:=Random(2^394,2^395);
// 	T:=NextPowerSmooth(N);
// 	T:=T^2;
// 	fT:=Factorization(T);
// 	size:=0;
// 	max:=size;
// 	for i in [1..n] do
// 		ideal:=RandomIdeal(order,2,32);
//     cnt:=2+Ceiling(Log(Integers()!Norm(ideal))/Log(2));
//     alpha:=0;
//     found:=false;
//     while alpha eq 0 do
//       x:=Enumerate(ideal,2^cnt);
//       cnt:=cnt+1;
//       if #x ge 2 then
//         alpha:=x[2];
//       end if;
//     end while;
//     ideal:=LeftIdeal(order,[elt1*Conjugate(alpha)/Norm(ideal):elt1 in Basis(ideal)]);
//     t:=Cputime();
//     //"on";
// 		new_ideal,_ := QuaternionIsogenyPath_specialConstraint2_small_power_of_2(order,w1,w2,ideal,-1,T,fT);
//
//     //"off";
// 		total:=total+Cputime(t);
// 		b,_:=IsLeftIsomorphic(ideal,new_ideal);
// 		if not b then
// 			print("algo is not working");
// 		end if;
// 		e:=Ceiling(Log(Norm(new_ideal))/Log(2));
// 		size:=size+e;
// 		if e ge max then
// 			max:=e;
// 		end if;
//     binarylen := Round(Log(Norm(new_ideal))/Log(2));
//
//
//    "in order", Basis(new_ideal) subset order;
//    "valuation", Valuation(Integers()!Norm(new_ideal),2);
//
//     // binarylen;
// 	// "ideal:", binarylen;
// 		// "result size :",Ceiling(Log(Norm(new_ideal))/Log(2));
// 		// "remaining torsion : ",T/Norm(new_ideal);
// 	end for;
// 	total/n;
// 	Floor(size/n);
// 	// max;1
//
// end procedure;


TestQuaternionIsogenyPath_special_Extended:=procedure()
	repeat
		p:=RandomPrime(256);
	until ((p mod 4) eq 3);
	B<i,j,k>:=QuaternionAlgebra<RationalField()|-1,-p>;
	order := MaximalOrder(B);
	w1 := i;
	w2 := j;
	q:=1;
	L:=2;
	foundsol:=false;
	while not foundsol do
		N1:=RandomPrime(64);
		count :=2000;
		// if (LegendreSymbol(-p,N1) eq 1) and (LegendreSymbol(-q,N1) eq 1) and (GCD(N1,q) eq 1) and (IsSquare(IntegerRing(q)!(N1*p))) and ((L eq -1) or not(IsSquare(IntegerRing(N1)!L))) then
    if (LegendreSymbol(-q,N1) eq -1) and (GCD(N1,q) eq 1) and ((L eq -1) or not(IsSquare(IntegerRing(N1)!L))) then
			count:=1;
		end if;
		while not foundsol and count le 1000 do
			count:=count+1;
			N2:=Random(2^198,2^205);
			m:=Floor(Sqrt((N1*N2)/(2*p)));
			compt:=0;
			while compt le 1000 and not foundsol do
				compt:=compt+1;
				c:=Random(-m,m); d:=Random(-m,m);
				M:=N1*N2 - p*(c^2+d^2);
				foundsol:=CornacciaNice(M);
				if foundsol then
					foundsol,a,b:=NormEquation(1,M);   // computation repeated due to Magma syntax, can this be avoided?
				end if;
			end while;
		end while;
	end while;
	quat:=B![a,b,c,d];
	connecting_ideal:=lideal<order|[N1,quat]>;
	ideal:=RandomIdeal(RightOrder(connecting_ideal),3,200);

	"\n\n";
	"Starting the computation\n\n";
	time new_ideal := QuaternionIsogenyPath_special_Extended2(order,w1,w2,ideal,connecting_ideal,2);

	"\n\n";
	binarylen := Round(Log(Norm(new_ideal))/Log(2));
	"Binary length of new ideal:", binarylen;
	b,_,_:=IsLeftIsomorphic(ideal,new_ideal);
	if not b then print("wrong result"); end if;
end procedure;

// TestQuaternionIsogenfyPath_special_Extended();
//
// TestQuaternionIsogenyPath_specialConstraint2_small_power_of_2();
// TestQuaternionIsogenyPath_special_Extended();
//TestQuaternionIsogenyPath_specialConstraint2_small_power_of_2();
// TestSmallPrime();
