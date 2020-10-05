
// SetAssertions(false);

Attach("src/Montgomery.m");
Attach("src/Isogenies.m");
load "src/klpt_sqisign.m";
load "src/tools.m";
t:=Cputime();
c:=ClockCycles();
load "src/gen_data_256_7.m";
t:=Cputime(t);
c:=ClockCycles()-c;
//use this to convert clockcycles to time
Cpu_freq:= RealField(3)!c/t;
DEBUG:=0;
//bound under which we use the old method for isogenies computation
degree_bound:=120;
E0_twist:=Montgomery(a,twisters[1]);

B<i,j,k>:=Parent(Basis(O0)[1]);
remove_2_endo:=function(J)
	while [Jbas in lideal<O0|[i+1,2]>: Jbas in Basis(J)] eq [true,true,true,true] do
		J:=J*lideal<RightOrder(J)|(i-1)/2>;
	end while;
	return J;
end function;
// removes scalar factors from ideals
cyclic_ideal := function(I:full:=false);
	B<i,j,k>:=Parent(Basis(O0)[1]);
	coordinates := [[Integers()!x : x in Eltseq(LeftOrder(I)!b)] : b in Basis(I)];
	content := GCD([GCD(c) : c in coordinates]);
	J:= lideal<Order(I)|[b/content : b in Basis(I)]>;
	if full then
		return remove_2_endo(J);
	else
		return J;
	end if;
end function;




 //TODO: 	deterministic point generation (ok but not ok ? not the same function as in *.c)
 //				generate honest challenge (should be okay)
 //				verify done
 //				normalized walk (we have the basis for it, potential problem with the lift, might not be the same one that we have for verify so this needs to be checked)
 //				compress/decompress (compress is done by the normalizing process) : first draft OK
// check that all the above task have been done correctly

//compute the timedifference between the current clockcycles and the one in input
timediff := func <t | RealField(6)!((ClockCycles()-t) / Cpu_freq)>;



// //Only used for debugging
evaluate_endomorphism:=function(x,P,l);
	E := Curve(P);
	seq := [centered_reduction(Integers()!(2*s), 2*l) : s in Eltseq(B!x)];
	//if (Order(P) mod 2 eq 0) then //and (GCD(seq) mod 2 eq 0) then
	//	E2 := BaseExtend(E0,2);
	//end if;

	P2 := DivisionPoints(P,2)[1];
	P2_dist := E!distorsion_endomorphism(P2);

	result := seq[1]*P2;
	result +:= seq[2]*P2_dist; // Distorsion
	result +:= seq[3]*E!frobenius_endomorphism(P2); // Frobenius
	result -:= seq[4]*E!frobenius_endomorphism(P2_dist);
	return E!result;
end function;
// Only used for debugging
// assumes l is odd
evaluate_endomorphism_twist:=function(x,P,l,frob_twister);
	E := Curve(P);
	seq := [centered_reduction(Integers()!(2*s), 2*l) : s in Eltseq(B!x)];

	//if (Order(P) mod 2 eq 0) then //and (GCD(seq) mod 2 eq 0) then
	//	E2 := BaseExtend(E0,2);
	//end if;

	P2 := DivisionPoints(P,2)[1];
	P2_dist := E!distorsion_endomorphism(P2);

	result := seq[1]*P2;
	result +:= seq[2]*P2_dist; // Distorsion
	result +:= seq[3]*E!frobenius_endomorphism(P2); // Frobenius
	result -:= seq[4]*E!frobenius_endomorphism(P2_dist);
	return E!result;
end function;


// only for odd norm, take an O0 ideal
ideal_to_kernel_generator_prime_power_precomp:=function(I,l,n)
	b := Basis(I);
	ln := l^n;

	torsion_data_ln, basis_ln, action_dist_ln, action_frob_ln, action_distfrob_ln, frobenius_twisters_ln, m := get_torsion_data(ln);

	i := 1;
	repeat
		// find an endomorphism in the ideal that does not act trivially on the l-torsion
		endo_quaternion := 2*&+[Random(-50-i,50+i)*Basis(I)[i]: i in [1..4]];


		seq := Eltseq(B!endo_quaternion);
		endo := seq[1] * Matrix([[1,0],[0,1]])
			+ seq[2] * action_dist_ln
			+ seq[3] * action_frob_ln
			+ seq[4] * action_distfrob_ln;

		i +:= 1;
	until not IsZero(ChangeRing(endo,Integers(l)));

	endo := ChangeRing(endo,Integers(ln));
	// a non-trivial element in the kernel
	vec := [centered_reduction(Integers()!x, ln) : x in Eltseq(KernelMatrix(Transpose(endo))[1])];


	// in the case of prime power, maybe part of the torsion is in a subfield.
	// we take advantage of it by doing as much work as possible in the subfield
	R:=basis_ln[2];
	if (m ne 0) then
		torsion_data_lm, basis_lm, action_dist_lm, action_frob_lm, action_distfrob_lm, frobenius_twisters_lm := get_torsion_data(l^m);

		lk := l^(n-m);

		v1 := centered_reduction(vec[1], lk);
		v2 := centered_reduction(vec[2], lk);
		Q := v1*basis_ln[1] + v2*basis_ln[2];

		w1 := (vec[1]-v1) div lk;
		w2 := (vec[2]-v2) div lk;
		Q +:= Parent(Q)!(w1*basis_lm[1] + w2*basis_lm[2]);


	else // ln is already prime, or the torsion is already in the base field
		Q := vec[1]*basis_ln[1] + vec[2]*basis_ln[2];
		if vec[1] mod l eq 0 then
			R:=basis_ln[1];
		end if;
	end if;



	if DEBUG ge 1 then
		//"DEBUG: checking ideal_to_kernel_generator";
		correct := not(IsIdentity(Q)) and
		IsIdentity(evaluate_endomorphism_twist(b[1],Q,ln, frobenius_twisters_ln)) and
		IsIdentity(evaluate_endomorphism_twist(b[2],Q,ln, frobenius_twisters_ln)) and
		IsIdentity(evaluate_endomorphism_twist(b[3],Q,ln, frobenius_twisters_ln)) and
		IsIdentity(evaluate_endomorphism_twist(b[4],Q,ln, frobenius_twisters_ln));
		if not(correct) then
			"ERROR: wrong result in ideal_to_kernel_generator", l, n;
		end if;
	end if;

	// if not IsOne(frobenius_twisters_ln) then
	// 	Q := distorsion_endomorphism(Q); "TWIST", ln;
	// end if;

	return Q,R;
end function;



// same as above but only for power of 2
ideal_to_kernel_generator_2n_precomp:=function(I,n)
	b := Basis(I);


	if (n gt exponent_power_of_2_rational_torsion) then
		print "ERROR: precomputations only allow isogenies of degree at most 2^", exponent_power_of_2_rational_torsion;
		return 0*basis_2[1];
	end if;

	ln := 2^n;

	ctr := 1;

	repeat
		repeat
			endo_quaternion := &+[Random(-50-ctr,50+ctr)*Basis(I)[i]: i in [1..4]];
			while endo_quaternion/2 in I do
				endo_quaternion := endo_quaternion/2;
			end while;

		until not (endo_quaternion/2 in O0);
		seq := Eltseq(O0!endo_quaternion);
		endo := seq[1] * Matrix([[1,0],[0,1]])
			+ seq[2] * action_dist_2
			+ seq[3] * action_id_plus_distfrob_half_2
			+ seq[4] * action_dist_plus_frob_half_2;
		endo := ChangeRing(endo,Integers(ln));

		vec := [centered_reduction(Integers()!x, ln) : x in Eltseq(KernelMatrix(Transpose(endo))[1])];
		ctr +:= 1;
	until IsOdd(vec[1]) or IsOdd(vec[2]);

	Q := vec[1]*(basis_2[1]*2^(exponent_power_of_2_rational_torsion - n)) + vec[2]*(basis_2[2]*2^(exponent_power_of_2_rational_torsion - n));

	return Q;
end function;


// Decompose into several ideals and call ideals_to_kernel_generator_precomp
//decompose the kernel in two points : one on E0 and one on its twist;
ideal_to_kernel_generator_precomp := function(I,norm_factorized);

	g1:=ZeroPt(E0);
	g2:=ZeroPt(E0_twist);
	Q1:=g1;Q2:=g2;
	n1:=1;n2:=1;
	f1:=[];f2:=[];
	for f in norm_factorized do
		ide:=I + Order(I)*f[1]^f[2];
		P,Q:=ideal_to_kernel_generator_prime_power_precomp(ide, f[1],f[2]);
		if f[1] in torsion_prime then
			g1+:=P;
			Q1+:=Q;
			n1*:=f[1]^f[2];
			Append(~f1,<f[1],f[2]>);
		else
			g2+:=P;
			Q2+:=Q;
			n2*:=f[1]^f[2];
			Append(~f2,<f[1],f[2]>);
		end if;
	end for;
	return <<g1,n1,f1,Q1>,<g2,n2,f2,Q2>>;
end function;




// Evaluate isogenies on P
// isoms contains the needed isomorphism to perform the computation (when two consecutive isogenies don't have the same representation for their domain/codomain curves)
// twist indicates if we want to push P through isogenies with kernel defined on the quadratic twist (this could be used to slightly improve the dual computation but is not done in the current version of the code)
eval_isogenies:=function(P,isogenies: isoms :=[],twist:=true)

	if IsEmpty(isogenies) then return P; end if;
	//avoid computation when P is zero.
	if IsIdentity(P) then
		E_final:=codomain(isogenies[#isogenies]);
		return ZeroXZ(E_final);
	end if;
	x:=[P];
	count:=0;
	for i in [1..#isogenies] do
		iso:=isogenies[i];
		if not twist then
			if iso`degree in torsion_prime_twist then
				return x[1];
			end if;
		end if;
		// checking if the point and the isogeny have the same representation for the curve
		if iso`domain`A ne x[1]`curve`A then

			// if not either compute it or use provided isoms
			if isoms eq [] then
				M:=Montgomery(RecoverAlpha(iso`domain),Fq!1);
				M2:=Montgomery(x[1]`curve,Fq!1);
				isom:=Isomorphism(M2,M);
				R:=ApplyIsom(isom,M,x[1]);
			else
				count+:=1;
				isom:=isoms[count];
				R:=ApplyIsom(isom,iso`domain,x[1]);
			end if;

			x:=[R];
			x:=Evaluate(iso,x);
		else
			x:=Evaluate(iso,x);
		end if;

	end for;
	if DEBUG ge 1 and count ne #isoms then " there may be some problem with isomorphisms"; end if;
	return x[1];
end function;


//perform strategy to compute the isogeny
//this is used for degree 2,3,5
prime_power_isogeny:=function(generator,degree)
	isogenies := [];
	l:=degree[1];
	e:=degree[2];
	strats:=strategies[l];
	s:=[strat[2]: strat in strats | strat[1] eq degree ][1];

	R:=generator;
	index_s:=1;
	index_pts:=0;
	points:=[];
	pts_index:=[];
	index:=0;
	for j in [1..(e-1)] do
		while index lt (e)-j do
			if index_pts ge #pts_index then
				Append(~points,R);
				Append(~pts_index,index);
				index_pts+:=1;
			else
				points[index_pts+1]:=R;
				pts_index[index_pts+1]:=index;
				index_pts+:=1;
			end if;
			m:=s[index_s];index_s+:=1;
			R:=l^m*R;
			index+:=m;
			// "index:",index;
			// pts_index;
		end while;
		//
		// "index of kernel",index;
		// pts_index;
		// IsIdentity(l*R);
		isog:=Isogeny(R,l,degree_bound);
		M:=domain(isog);
		//adjusting the codomain of the previous isogeny when l=2 now that we know its alpha
		if isogenies ne [] and l eq 2 and isogenies[#isogenies]`codomain`alpha eq 0 then
			phi:=isogenies[#isogenies];
			phi:=AdjustingAlpha(phi,isog`isogeny`domain`alpha);
			isogenies[#isogenies]:=phi;
		end if;
		isogenies:=isogenies cat [isog];
		// for i in [0..index_pts-1] do
		// 	points[i+1]:=Evaluate(isog,[points[i+1]])[1];
		// end for;
		points:=[Evaluate(isog,[points[i+1]])[1] : i in [0..index_pts-1]];
		pts_index:=[pts_index[i+1]:i in [0..index_pts-1] ];
		R:=points[index_pts];
		index:=pts_index[index_pts];
		index_pts-:=1;
	end for;
	isog:=Isogeny(R,l,degree_bound);
	isogenies:=isogenies cat [isog];
	return isogenies;
end function;

//compute the isogeny from the generator of order factorized as degrees
	// degrees is of list of pairs <prime, power>, generator is a point
kernel_generator_to_isogeny_power:=function(generator, degrees);
		isogenies := [];


		for i in [1..#degrees] do
			l := degrees[i][1];
			if l eq 2 or l eq 3 or l eq 5 then
				isogenies:=isogenies cat prime_power_isogeny(generator,degrees[i]);
			else
				for e in [1..degrees[i][2]] do
					Q := generator*l^(degrees[i][2]-e);
					isog:=Isogeny(Q,l,degree_bound);
					M:=domain(isog);

					//adjusting the codomain of the preivous isogeny when l=2 now that we know its alpha
					if isogenies ne [] and l eq 2 and isogenies[#isogenies]`codomain`alpha eq 0 then
						phi:=isogenies[#isogenies];
						phi:=AdjustingAlpha(phi,isog`isogeny`domain`alpha);
						isogenies[#isogenies]:=phi;
					end if;

					isogenies := isogenies cat [isog];
					if (i ne #degrees) or (e ne degrees[i][2]) then
						generator:=Evaluate(isog,[M!generator])[1];
					end if;
					//hoping to do the same for the last curve
					if l eq 2 and e eq degrees[i][2] then
						if not IsIdentity(2*generator) then
							Q:=Evaluate(isog,[generator])[1];
							previous_iso:=isogenies[#isogenies];
							if previous_iso`codomain`alpha eq 0 then
								phi:=New(Isog);
								phi2:=New(TwoIsog);
								M:=RecoverAlpha(previous_iso`codomain,Q`X);
								phi`domain:=previous_iso`domain;
								phi2`domain:=previous_iso`domain;
								phi`codomain:=M;
								phi2`codomain:=M;
								phi2`kernel:=previous_iso`isogeny`kernel;
								phi`degree:=2;
								phi`isogeny:=phi2;
								isogenies[#isogenies]:=phi;
								Q:=SemiMontgomeryXZ(Q`X,Q`Z,M);
							end if;
						end if;
					end if;
				end for;
			end if;
			// t1:=timediff(t);
			// if l eq 2 or l eq 3 or l eq 5 then
			// 	c:=ClockCycles();iso_test:=isogenies;
			// 	isogenies:=prime_power_isogeny(gen_temp,degrees[i]);
			// 	// "l = ",l," naive :",t1," strategy :",timediff(c);
			// 	assert IsIsomorphic(codomain(iso_test[#iso_test]),codomain(isogenies[#isogenies]));
			// end if;
		end for;

		return isogenies;
end function;


//compute a list of isogeny from generator, the first argument is the point, the second its order, and the third the factorization of its order
list_kernel_generators_to_isogeny_single :=function( generator);
		isogenies := [];
		gen:=generator[1];
		k:=generator[2];
		norm_factorized:=generator[3];

		add:=0;
		//computing first the isogenies of degree less than 6 (3 and 5)
		if norm_factorized[1][1] le 6 then
			add:=1;
			k:=(k div norm_factorized[1][1]^norm_factorized[1][2]);
			ell_gen:=k*gen;
			isogenies_new := kernel_generator_to_isogeny_power( ell_gen, [norm_factorized[1]]);
			gen:=eval_isogenies(gen,isogenies_new);
			isogenies := isogenies cat isogenies_new;
		end if;
		//computing the remaining isogenies in reverse order
		for i in [1..#norm_factorized-add] do
			k:=(k div norm_factorized[#norm_factorized-i+1][1]^norm_factorized[#norm_factorized-i+1][2]);
			ell_gen:=k*gen;
			isogenies_new := kernel_generator_to_isogeny_power( ell_gen, [norm_factorized[#norm_factorized - i +1]]);
			gen:=eval_isogenies(gen,isogenies_new);
			isogenies := isogenies cat isogenies_new;
		end for;
		return isogenies;
end function;

//taking a generator decomposed as two point (one for the curve and one for its twist) and computing the isogeny
list_kernel_generators_to_isogeny :=function(g)
	isogenies1 := list_kernel_generators_to_isogeny_single(g[1]);
	g_twist_pushed_through:=<eval_isogenies(g[2][1],isogenies1),g[2][2],g[2][3]>;
	isogenies2:=list_kernel_generators_to_isogeny_single(g_twist_pushed_through);
	return isogenies1 cat isogenies2;
end function;


//compute the basis of the 2^32 torsion
basis_of_power_of_2_torsion := function(E);
	M:=SemiMontgomery(E);
	n := exponent_power_of_2_rational_torsion;
	// cofactor:=(p+1) div 2^(n+1);
	repeat
		B1 := cofactor*Random(M);
		B12n:=B1*2^(n);
	until not IsIdentity(B12n) and IsIdentity(B12n*2);

	repeat
		B2 := cofactor*Random(M);
		B22n:=B2*2^(n);
	until (not IsIdentity(B22n) and IsIdentity(B22n*2)) and (not (B12n eq B22n));
	return [M!(2*B1),M!(2*B2)];
end function;

//generate a random point of order dividing ell^e on the curve or its twist with a deterministic seed
deterministic_point:=function(M,ell,e,twist,seed)
	SetSeed(seed,10);
	cofactor:=1;
	F:=Parent(M`A);
	if twist then
		cofactor:= (p+1) div ell^e;
	else
		cofactor := (p-1) div ell^e;
	end if;
	repeat
		P:=RandomXZ(M);

	until IsOnCurve(P) eq twist;
	if twist then assert(IsIdentity((p+1)*P)); end if;
	P:=cofactor*P;
	return P;
end function;

//generate a random basis from deterministic seed
deterministic_two_basis:=function(M,n)
	seed:=100;
	repeat
		B1:=deterministic_point(M,2,n,true,seed);
		assert(IsIdentity(2^n*B1));
		B12n:=B1*2^(n-1);
		seed:=seed+100;
	until not IsIdentity(B12n) and IsIdentity(B12n*2);
	repeat
		B2 := deterministic_point(M,2,n,true,seed);
		B22n:=B2*2^(n-1);
		seed:=seed+100;
	until (not IsIdentity(B22n) and IsIdentity(B22n*2)) and (not (B12n eq B22n));

	return [M!(B1),M!(B2)];
end function;


//compute the dual of isogenies (a chain of two isogenies) and its kernel
dual_two_isogenies_kernel:=function(isogenies,kernel)
	kernel:=Lift(kernel,twisters[1]);
	M1:=Montgomery(domain(isogenies[1]),Fq!1);
	basis:=basis_of_power_of_2_torsion(domain(isogenies[1]));
	basis:=[M1!Lift(b,M1): b in basis];
	basis:=[2^(exponent_power_of_2_rational_torsion-#isogenies)*b :b in basis];
	n:=#isogenies;
	//computing a point orthogonal to the kernel
	repeat
		a:=Random(1,2^n);
		Q:=basis[1]+a*basis[2];
	until IsLinearlyIndependent(Q,kernel,2^#isogenies);
	//pushing it through phi, providing a generator for the kernel of the dual
	kernel_dual:=eval_isogenies(Project(Q),isogenies);
	return Reverse([DualIsogeny(iso): iso in isogenies]),kernel_dual;
end function;

//same as above but without the kernel, more efficient
dual_two_isogenies:=function(isogenies)
	return Reverse([DualIsogeny(iso): iso in isogenies]);
end function;

//compute the dual of an isogeny of odd degree, gen contains the generator of isogenies in the usual form, in the fourth argument, there is a point orthogonal to the kernel
//the kernel of the dual is included
dual_odd_isogeny := function(isogenies,gen)
	index:=1;
	index_twist:=2;
	F:=Parent(gen[1][1]`X);
	//compute the kernel of the dual
	gen_isogenies_dual:=	<<eval_isogenies(gen[i][4],isogenies),gen[i][2],gen[i][3]>: i in [1..2]>;
	isogenies_dual:=list_kernel_generators_to_isogeny(gen_isogenies_dual);
	return isogenies_dual,gen_isogenies_dual;
end function;

// same as above but propose an alternative : do not push both generators through, the twist is pushed only through the first half
// modifying aother things  it can provide an alternative to the current way of computing kernel, this requires some work and is supposed to be only slighty more efficient so not done yet
dual_odd_isogeny_other := function(isogenies,gen)
	index:=1;
	index_twist:=2;
	F:=Parent(gen[1][1]`X);
	// if IsTwistPoint(gen[1][1]) then
	// 	index:=2;
	// 	twist_index:=1;
	// end if;
	deg:=GCD([gen[index][2],tot]);
	deg_twist:=GCD([gen[index_twist][2],tot_twist]);
	cof:=(p+1) div deg;
	cof_twist:=(p-1) div deg_twist;
	M:=gen[index][1]`curve;
	M_twist:=gen[index_twist][1]`curve;
	// gen_isogenies_dual:=	<<eval_isogenies(gen[i][4],isogenies),gen[i][2],gen[i][3]>: i in [1..2]>;
	// isogenies_dual:=list_kernel_generators_to_isogeny(gen_isogenies_dual);
	gen_dual_twist:=<eval_isogenies(gen[2][4],isogenies),gen[2][2],gen[2][3]>;
	gen_dual:=<eval_isogenies(gen[1][4],isogenies:twist:=false),gen[1][2],gen[1][3]>;
	dual_twist:=list_kernel_generators_to_isogeny_single(gen_dual_twist);
	dual:=list_kernel_generators_to_isogeny_single(gen_dual);
	if codomain(dual_twist[#dual_twist])`A ne domain(dual[1])`A then "we are going to need an isomorphism"; end if;
	gen_isogenies_dual:=<gen_dual,gen_dual_twist>;
	isogenies_dual:=dual_twist cat dual;
	return isogenies_dual,gen_isogenies_dual;
end function;

// only used for debugging
// when E contains the 2^n torsion, i.e. n <= exponent_power_of_2_rational_torsion
ideal_to_isogeny_2_simple := function(I,n);
	generator := ideal_to_kernel_generator_2n_precomp(I, n);
	isogenies := kernel_generator_to_isogeny_power(generator,[<2,n>]);
	return generator,isogenies;
end function;

//take an ideal of norm dividing T and compute the kernel and the associated isogeny
ideal_to_isogeny_T := function(I,norm_factorized);
	g := ideal_to_kernel_generator_precomp(I, norm_factorized);
	g:=< <Project(gs[1]),gs[2],gs[3]>: gs in g>;

	isogenies := list_kernel_generators_to_isogeny(g);
	return g,isogenies;
end function;

//testing above function
//might be not updated to latest changes
test_ideal_to_isogeny_T := procedure();
	B<i,j,k>:=Parent(Basis(O0)[1]);

	l := 1069;

	I := Random(MaximalLeftIdeals(O0,l)) meet Random(MaximalLeftIdeals(O0,5));

	torsion_data_lm, basis_lm, action_dist_lm, action_frob_lm, action_distfrob_lm, frobenius_twisters_lm := get_torsion_data(l);
	generators, Es,isogenies := ideal_to_isogeny_T(I,[<5,1>,<l,1>]);


	isom := Isomorphism(BaseChange(curve_extensions_twist[1],field_extensions[2]),curve_extensions[2]);


	// (x,y) on twist -> (t*x, root(t)*y) on curve
	gen_twist := generators[2][1];

	root_twister := SquareRoot(field_extensions[2]!twisters[1]);

	if not IsZero(root_twister^(1-p) - frobenius_twisters_lm) then
		root_twister := -root_twister;
	end if;


	gen := curve_extensions[2]![gen_twist[1]/twisters[1], gen_twist[2]/root_twister^3,1];

	"Is the generator really in the kernel?";
	IsIdentity(eval_isogenies(gen,isogenies));

	"Is the twisted generator correct?";
	&and[IsIdentity(evaluate_endomorphism_twist(b,gen_twist,l,frobenius_twisters_lm)) : b in Basis(I)];

	"Is the generator correct?";
	&and[IsIdentity(evaluate_endomorphism(b,gen,l)) : b in Basis(I)];

	if not IsIdentity(eval_isogenies(gen,isogenies)) then
		"Problem in kernel_generator_to_isogeny";
	end if;
end procedure;


// M1,M2,M3,M4 are the action of the endo ring basis on the torsionbasis P,Q of order L^e
kernel_to_ideal_from_action := function(order,L,e,ker,P,Q,M1,M2,M3,M4)
  a:=DLP_dimension_2_power(ker,P,Q,L,e);
  v:=Matrix(IntegerRing(L^e),2,1,a);
  v1:=ChangeRing(M1,IntegerRing(L^e))*v;
  v2:=ChangeRing(M2,IntegerRing(L^e))*v;
  v3:=ChangeRing(M3,IntegerRing(L^e))*v;
  v4:=ChangeRing(M4,IntegerRing(L^e))*v;
  matsys:=Matrix(IntegerRing(L^e),4,2,[v1[1][1],v1[2][1],v2[1][1],v2[2][1],v3[1][1],v3[2][1],v4[1][1],v4[2][1]]);
  K:=Kernel(matsys);
  r:=Basis(K)[1];
  r:=ChangeRing(r,Z);

  repeat
    r:=&+[Random(-100,100)*Basis(K)[i]: i in [1..Dimension(K)]];
    r:=ChangeRing(r,Integers());
    alpha:=&+[r[i]*Basis(order)[i]:i in [1..4]];
    // r[1]*ker+r[2]*iota_map(ker)+r[3]*frob_map(ker)+r[4]*frob_map(iota_map(ker));
  until not alpha/L in order;
  I:=lideal<order|[alpha,L^e]>;
  return I;
end function;

//compute the ideal corresponding to the isogeny of kernel ker, P,Q is supposed to be the basis
kernel_to_ideal_O0_prime_power := function(L,e,ker,P,Q)
	ker:=Lift(ker,twisters[1]);
	M1 := Matrix([[1,0],[0,1]]);
	if L eq 2 then
		M2 := action_dist_2;
		M3 := action_id_plus_distfrob_half_2;
		M4 := action_dist_plus_frob_half_2;
	else
		torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
		//recompute the basis which was precomputed anyway
		P:=basis_Le[1];
		Q:=basis_Le[2];
		M2 := action_dist_Le;
		M3_double := (M1 + action_distfrob_Le);
		M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
		M4_double := (action_dist_Le + action_frob_Le);
		M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
	end if;

  return kernel_to_ideal_from_action(O0,L,e,ker,P,Q,M1,M2,M3,M4);
end function;


//compute the kernel from the isogeny, isom_mitm precise isomorphism if any are needed to evaluate the chain of isogenies
two_isogenies_to_kernel := function(phi:isom_mitm:=[]);
	M:=Montgomery(domain(phi[1]),Fq!1);
	basis := basis_of_power_of_2_torsion(domain(phi[1]));
	basis:=[M!Lift(b,M): b in basis];
	basis := [M!b*2^(exponent_power_of_2_rational_torsion - #phi) : b in basis];
	n:=#phi;
	M2:=Montgomery(codomain(phi[#phi]),Fq!1);
	//compute the image of the basis through the curve;
	image:=[eval_isogenies(Project(b),phi:isoms:=isom_mitm): b in basis];
	image := [M2!Lift(im,M2) : im in image];

	deg:=2^n;

	if IsIdentity(Project(image[1])*2^(#phi-1)) then
		tmp_image := image[1];
		image[1] := image[2];
		image[2] := tmp_image;

		tmp_basis := basis[1];
		basis[1] := basis[2];
		basis[2] := tmp_basis;
	end if;

	a := discrete_logarithm_power(image[2],image[1],2,#phi);
	//solve potential problem of sign during the lift of projective points
	if IsIdentity(eval_isogenies(Project(basis[2]-a*basis[1]),phi:isoms:=isom_mitm)) then
		return basis[2] - a*basis[1];
	else
		return basis[2]+a*basis[1];
	end if;


	return basis[2] - a*basis[1];
end function;


// J of norm dividing T^2, I of norm a power of 2
//return phi_J decomposed as two isogenies phi_H1 phi_H2 such that phi_J := dual (phi_H2) o phi_H1
special_ideal_to_isogeny := function(J,I,phi_I);

	T := available_odd_torsion;
	H1 := J + Order(J)*T;
	morph, beta := LeftIsomorphism(J,I);
	alpha := beta*Norm(J);
	H2 := O0*alpha + O0*Integers()!(Norm(J)/Norm(H1));

	generators_H1, isogenies_H1 := ideal_to_isogeny_T(H1,Factorisation(Integers()!Norm(H1)));


	generators_H2:= ideal_to_kernel_generator_precomp(H2,Factorisation(Integers()!Norm(H2)));
	generators_H2 := < <Project(gen[1]),gen[2],gen[3]>:gen in generators_H2>;
	generators_H2_pushed_through_phi_I := <<eval_isogenies(gen[1],phi_I),gen[2],gen[3]> : gen in generators_H2>;
	isogenies_H2 := list_kernel_generators_to_isogeny(generators_H2_pushed_through_phi_I);


	return generators_H1, isogenies_H1, generators_H2_pushed_through_phi_I, isogenies_H2;
end function;

//same as above but provide the result as phi_J := dual( phi_H2) o phi_H1, requires the computation of a dual for that
special_ideal_to_isogeny_dual := function(J,I,phi_I);

	T := available_odd_torsion;
	H1 := J + Order(J)*T;
	morph, beta := LeftIsomorphism(J,I);
	alpha := beta*Norm(J);
	H2 := O0*alpha + O0*Integers()!(Norm(J)/Norm(H1));

	generators_H1,isogenies_H1 := ideal_to_isogeny_T(H1,Factorisation(Integers()!Norm(H1)));

	generators_H2:= ideal_to_kernel_generator_precomp(H2,Factorisation(Integers()!Norm(H2)));
	generators_H2 := < <Project(gen[1]),gen[2],gen[3],Project(gen[4])>:gen in generators_H2>;
	generators_H2_pushed_through_phi_I := <<eval_isogenies(gen[1],phi_I),gen[2],gen[3],
	eval_isogenies(gen[4],phi_I)> : gen in generators_H2>;
 	isogenies_H2 := list_kernel_generators_to_isogeny(generators_H2_pushed_through_phi_I);
	isogenies_H2_dual,gen_H2_dual:=dual_odd_isogeny(isogenies_H2,generators_H2_pushed_through_phi_I );
	if not IsIsomorphic(codomain(isogenies_H2_dual[#isogenies_H2_dual]),domain(isogenies_H2[1]) ) then "problem with isogenies dual"; end if;
	return generators_H1,isogenies_H1, gen_H2_dual,isogenies_H2_dual, isogenies_H2;
end function;

//testing the above functions
//might not be updated
test_special_ideal_to_isogeny := function();
	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);

	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := 32;
	//boo, alpha := NormEquation_SpecialOrder_adaptive(i,j,5^2*3^10*7^4*11^2*13^2*19^2*23^2*(17*43*71*109*127*337*521*809*1069)^2*2^n,5);
	boo, alpha := NormEquation_SpecialOrder_adaptiveConstraint(i,j,2^n,T2,fT2);

	I := cyclic_ideal(O0*alpha);

	N := Integers()!(Norm(I));
	n := Valuation(N,2);
	N := N div 2^n;

	I_2 := cyclic_ideal(I + O0*2^n);

	I_dual := cyclic_ideal(O0*Conjugate(alpha));
	I_T := I_dual + O0*N;

	Q := ideal_to_kernel_generator_2n_precomp(I_2,n);
	// "Q curve:";
	// Curve(Q);
	// Q`curve;
	isogenies_2 := kernel_generator_to_isogeny_power(Q, [<2,n>]);

	b,_ := IsLeftIsomorphic(I_T,I_2);
	"Left-isomorphic ideals?", b;

	time
	gen_H1, Es_H1,isogenies_H1, gen_H2, Es_H2,isogenies_H2 := special_ideal_to_isogeny(I_T,I_2,isogenies_2);

	"Two halfs meet?", IsIsomorphic(Es_H1[#Es_H1], Es_H2[#Es_H2]);


	return 0;
end function;

//select a random ideal of norm l^n
random_ideal := function(l,n)
	I := Random(MaximalLeftIdeals(O0,l));
	O_prev := O0;
	O := RightOrder(I);
	for i in [2..n] do
		// non-backtraking
		repeat
			I_new := Random(MaximalLeftIdeals(O,l));
		until RightOrder(I_new) ne O_prev;
		I *:= I_new;
		O_prev := O;
		O := RightOrder(I_new);
	end for;
	return LeftIdeal(O0,Basis(I));
end function;



//takes an ideal and find an equivalent one of odd norm
equivalent_odd_ideal := function(ideal)
	order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));

	N:=Integers()!Norm(ideal);
	ctr := 0;
	repeat
		odd_vector := &+[Random(-50-ctr, 50+ctr)*b : b in Basis(ideal)];
		ctr +:= 1;
	until IsOdd(Integers()!Norm(odd_vector) div N);

	ideal2:=LeftIdeal(order,[elt*Conjugate(odd_vector)/Norm(ideal): elt in Basis(ideal)]);
	if DEBUG ge 1 then "ideal 2 and ideal are isomorphic?",IsIsomorphic(ideal,ideal2); "new ideal of odd norm?",IsOdd(Integers()!Norm(ideal2));end if;
	return ideal2;
end function;

//same as above but the norm needs to be comprime to L
equivalent_coprime_ideal := function(ideal, L)
	order := Order(ideal);
	B<i,j,k>:=Parent(Basis(order)[1]);
	p:=Max(Norm(B.1),Norm(B.2));

	//basis:=ReducedBasis(ideal);

	N:=Integers()!Norm(ideal);


	ctr := 0;
	repeat
		odd_vector := &+[Random(-50-ctr, 50+ctr)*b : b in Basis(ideal)];
		ctr +:= 1;
	until GCD(Integers()!Norm(odd_vector) div N, L) eq 1;


	ideal2:=LeftIdeal(order,[elt*Conjugate(odd_vector)/Norm(ideal): elt in Basis(ideal)]);
	if DEBUG ge 1 then "ideal 2 and ideal are isomorphic?",IsIsomorphic(ideal,ideal2); "new ideal of odd norm?",IsOdd(Integers()!Norm(ideal2));end if;

	return ideal2;
end function;

//now finds the smallest equivalent ideal
small_equivalent_ideal:=function(I)
	//the dimension being 4, LLL finds the shortest vector in the lattice
	bas:=LLLReducedBasis(I);
	if Norm(bas[1]) ne Norm(I)^2 then
		return I*lideal<RightOrder(I)| Conjugate(bas[1])/Norm(I)>;
	else
		return I;
	end if;
end function;


// given a 2^n torsion point P in codomain_2 = Codomain(isogenies_2), compute its preimage in Domain(isogenies_1) through (isogenies_H1 o isogenies_H2)
// B1,B2 is a basis of the 2^n torsion on Es_H1[1]
// P := ker1;
//  isogenies_1 := phi_J2_step ;
//   codomain_1 := codomain_J2_step;
//    isogenies_2 := phi_J1_step;
//     codomain_2 := codomain_J1_step;
//      B1 := basis[1];
//       B2 := basis[2];
two_torsion_through_special_isogeny := function(P,isogenies_1,isogenies_2 ,B1, B2);
	B1:=Project(B1);
	B2:=Project(B2);
	n:=exponent_power_of_2_rational_torsion+1;
	repeat
		n:=n-1;
	until not IsIdentity(2^(n-1)*P);
	t:=Cputime();
	P_pushed := eval_isogenies(Project(P),isogenies_2);
	B1:=2^(exponent_power_of_2_rational_torsion-n)*B1;
	B2:=2^(exponent_power_of_2_rational_torsion-n)*B2;
	B1_pushed := eval_isogenies(Project(B1),isogenies_1);
	B2_pushed := eval_isogenies(Project(B2),isogenies_1);

	P_pushed:=Lift(P_pushed,twisters[1]);
	B1_pushed:=Lift(B1_pushed,twisters[1]);
	B2_pushed:=Lift(B2_pushed,twisters[1]);
	deg:=&*[iso`degree:iso in isogenies_1];
	M:=Montgomery(B1`curve,Fq!1);
	B1:=Lift(B1,M);
	B2:=Lift(B2,M);
	if WeilPairing(B1,B2,2^n)^(deg) ne WeilPairing(B1_pushed,B2_pushed,2^n) then
		B2_pushed:=-B2_pushed;
	end if;

	M_P:=Curve(P_pushed);
	M_B1:=Curve(B1_pushed);
	//in case the curves have not the same representation
	if IsIsomorphic(M_P,M_B1) then
		if M_P`A eq - M_B1`A then
			P_pushed:=MontgomeryPt(-P_pushed`x,a*P_pushed`y,P_pushed`z,MontgomeryA(-M_P`A,M_P`B));
		else
			if M_P`A ne M_B1`A then
				isom:=Isomorphism(M_P,M_B1);
				P_pushed:=ApplyIsom(isom,M_B1,P_pushed);
			end if;
		end if;
	else
		"Curves are not isomorphic !";
	end if;

	dlp:=DLP_dimension_2_power(P_pushed,B1_pushed,B2_pushed,2,n);
	P_E0 := dlp[1]*B1+dlp[2]*B2;
	return P_E0;
end function;

//only used for debugging, might not be updated to the latest version
// ker1 is a generator of the kernel of E0 -> E1 of degree 2^(exponent_power_of_2_rational_torsion)
// phi1 is the isogeny of kernel ker1
// ker2 is a generator of the kernel of E1 -> E2 of degree 2^(exponent_power_of_2_rational_torsion)
kernel_to_ideal_power_of_2_small := function(ker1,phi1,ker2);
	B<i,j,k>:=Parent(Basis(O0)[1]);

	P1 := basis_2[1];
	P2 := basis_2[2];
	t:=Cputime();
	I1 := kernel_to_ideal_O0_prime_power(2,exponent_power_of_2_rational_torsion,ker1,P1,P2);
	T := available_odd_torsion;


	T2 := T^2;
	fT2 := Factorisation(T2);
	J1 := QuaternionIsogenyPath_specialConstraint_small2power_input(O0,i,j,I1,-1,T2,fT2);
	J1 := cyclic_ideal(J1);
	morph, beta := LeftIsomorphism(J1,I1);
	alpha := beta*Norm(J1);
	gen_H1, isogenies_H1, gen_H2, isogenies_H2 := special_ideal_to_isogeny(J1,I1,phi1);

	ker2_iso:=ker2;

	ker2_E0 := two_torsion_through_special_isogeny(ker2_iso,isogenies_H1,
	isogenies_H2, basis_2[1], basis_2[2]);
	I2 := kernel_to_ideal_O0_prime_power(2,exponent_power_of_2_rational_torsion,ker2_E0,P1,P2);
	H := I2 meet J1;
	H_odd := equivalent_odd_ideal(H);
	ctr := Ceiling(Log(Integers()!(Norm(H_odd)*Norm(I1)))/Log(2)+exponent_power_of_2_rational_torsion);
	repeat
		ctr +:= 1;
		vec := Enumerate(I1 meet Conjugate(H_odd),2^ctr);
	until #vec gt 1;

	alpha := vec[2];
	return cyclic_ideal(O0*alpha + O0*4^(exponent_power_of_2_rational_torsion));
end function;

//testing the above function
//might not be updated to the latest version
test_kernel_to_ideal_power_of_2_small := function()
	n := exponent_power_of_2_rational_torsion;
	P1 := basis_2[1];
	P2 := basis_2[2];

	ker1 := (1+2*Random(2^(n-1)-1))*P1 + Random(2^(n)-1)*P2;
	phi1 := kernel_generator_to_isogeny_power(ker1,[<2,n>]);

	repeat
    	ker2 := RandomXZ(codomain(phi1[#phi1]),true)*cofactor;
    until IsIdentity(ker2*2^(n)) and not(IsIdentity(ker2*2^(n-1)));

	time I12 := kernel_to_ideal_power_of_2_small(ker1,phi1,ker2);

	return 0;
end function;

//only used for debugging
// #kernels is 4, the maximum size of handled by this function is 128
kernel_to_ideal_power_of_2 := function(kernels)

	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);

	phi1 := kernel_generator_to_isogeny_power(kernels[1],[<2,n>]);
	I12 := kernel_to_ideal_power_of_2_small(kernels[1],phi1,kernels[2]);

	J12 := QuaternionIsogenyPath_specialConstraint_small2power_input(O0,i,j,I12,-1,T2,fT2);
	J12 := cyclic_ideal(J12);

	ker2:=kernels[2];
	phi2 := kernel_generator_to_isogeny_power(ker2,[<2,n>]);
	gen_H1,isogenies_H1, gen_H2, isogenies_H2 := special_ideal_to_isogeny(J12,I12,phi1 cat phi2);

	ker3:=kernels[3];
	t:=Cputime();
	ker3_E0 := two_torsion_through_special_isogeny(ker3, isogenies_H1, isogenies_H2, basis_2[1], basis_2[2]);
	phi3 := kernel_generator_to_isogeny_power(ker3,[<2,n>]);
	phi3_E0 := kernel_generator_to_isogeny_power(Project(ker3_E0),[<2,n>]);

	gen_H1_through_phi3 := <<eval_isogenies(gen[1],phi3_E0), gen[2],gen[3]> : gen in gen_H1>;
	gen_H2_through_phi3 := <<eval_isogenies(gen[1],phi3), gen[2],gen[3]> : gen in gen_H2>;
  isogenies_H1_through_phi3 := list_kernel_generators_to_isogeny(gen_H1_through_phi3);
	isogenies_H2_through_phi3 := list_kernel_generators_to_isogeny(gen_H2_through_phi3);

	ker4 := kernels[4];

	M3:=Montgomery(domain(isogenies_H1_through_phi3[1]),Fq!1);
	basis3 := basis_of_power_of_2_torsion(domain(isogenies_H1_through_phi3[1]));
	basis3:=[M3!Lift(b,M3): b in basis3];
	ker4_E0 := two_torsion_through_special_isogeny(ker4, isogenies_H1_through_phi3, isogenies_H2_through_phi3, basis3[1], basis3[2]);
	I34 := kernel_to_ideal_power_of_2_small(ker3_E0,phi3_E0,ker4_E0);
	K_odd := equivalent_odd_ideal(I34 meet J12);

	ctr := Ceiling(Log(Integers()!(Norm(K_odd)*Norm(I12)))/Log(2)+2*exponent_power_of_2_rational_torsion);
	repeat
		ctr +:= 1;
		vec := Enumerate(I12 meet Conjugate(K_odd),2^ctr);
	until #vec gt 1;
	alpha := vec[2];
	return cyclic_ideal(O0*alpha + O0*2^(4*exponent_power_of_2_rational_torsion));
end function;

//testing the above functions
//might not be updated
test_kernel_to_ideal_power_of_2 := function()
	n := exponent_power_of_2_rational_torsion;
	P1 := basis_2[1];
	P2 := basis_2[2];

	t:=Cputime();
	ker1 := (1+2*Random(2^(n-1)-1))*P1 + Random(2^(n)-1)*P2;
	ker1:=Project(ker1);
	// Normalized(2^(n-1)*Project(ker1))`X;
	phi1 := kernel_generator_to_isogeny_power((ker1),[<2,n>]);
	// _,_ := kernel_generator_to_isogeny_power(Project(ker1),[<2,n>]);
	// Factorization(available_odd_torsion);
	repeat
			ker2 := RandomXZ(codomain(phi1[#phi1]),true)*cofactor;
    	// ker2 := RandomPt(Montgomery(codomain(phi1[#phi1]),ker1`curve))*(cofactor);
    until IsIdentity(ker2*2^(n+1)) and not(IsIdentity(ker2*2^(n))) and not IsZero((ker2*2^(n))`X);
	t1:=Cputime();
	phi2 := kernel_generator_to_isogeny_power(2*ker2,[<2,n>]);
	// "time to compute 32 2-isogenies: ", Cputime(t1);
	repeat
    	ker3 := RandomXZ(codomain(phi2[#phi2]),true)*cofactor;
    until IsIdentity(ker3*2^(n+1)) and not(IsIdentity(ker3*2^(n)))and not IsZero((ker3*2^(n))`X);
	phi3 := kernel_generator_to_isogeny_power(2*ker3,[<2,n>]);

	repeat
    	ker4 := RandomXZ(codomain(phi3[#phi3]),true)*cofactor;
    until IsIdentity(ker4*2^(n+1)) and not(IsIdentity(ker4*2^(n)))and not IsZero((ker4*2^(n))`X);
	phi4 := kernel_generator_to_isogeny_power(2*ker4,[<2,n>]);
	// "time generating the kernel: ",Cputime(t);
	I1234 := kernel_to_ideal_power_of_2(<ker1,2*ker2,2*ker3,2*ker4>);
	// "done";
	return 0;
end function;

//build the list of 2^distance isogenies starting from E1
build_list_meet_in_the_middle := function(E1, distance);
	if IsZero(distance) then
		return [];
	end if;
	basis := basis_of_power_of_2_torsion(E1);
	E1:=Montgomery(E1,basis[1],twisters[1]);
	basis[1] := basis[1]*2^(exponent_power_of_2_rational_torsion - distance-1);
	basis[2] := basis[2]*2^(exponent_power_of_2_rational_torsion - distance-1);
	basis_lifted:=[E1!Lift(basis[1],E1),E1!Lift(basis[2],E1)];

	// make sure P2 is the kernel of a backtraking isogeny
	if (basis[2]*2^distance)`X eq 0 then
		P1 := basis_lifted[1];
		P2 := basis_lifted[2];
	elif (basis[1]*2^(distance))`X eq 0 then
		P1 := basis_lifted[2];
		P2 := basis_lifted[1];
	else
		P1 := basis_lifted[1];
		P2 := basis_lifted[1] + basis_lifted[2];
	end if;
	P:=P1;
	Q:=(P1+P2);
	R:=P+Q;
	list := <<[],Project(P),Project(Q),Project(R)>>;
	for t in [1..distance] do
		new_list := <>;
		for l in list do

			Q1 := (l[2])*2^(distance-t+1);
			phi1 := Isogeny(Q1,2,degree_bound);
			//adjusting the domain for the other point Q2
			M:=phi1`domain;
			invalpha:=-M`A-M`alpha;
			Q2:=SemiMontgomeryXZ(invalpha,Fq!1,RecoverAlpha(M,invalpha));
			temp:=XAdd(l[3],l[4],l[2]);

			pushed_points:=Evaluate(phi1,[M!l[2],M!temp,M!XAdd(temp,l[2],2*l[3])]);

			//adjusting the codomain of the previous iso now that we know a value for alpha
			previous_iso:=l[1];
			if previous_iso ne [] then
				phi:=previous_iso[#previous_iso];
				phi:=AdjustingAlpha(phi,domain(phi),M`alpha);
				previous_iso[#previous_iso]:=phi;
			end if;

			new_list := Append(new_list, <previous_iso cat [phi1], pushed_points[1], pushed_points[2], pushed_points[3]>);

			phi2 := Isogeny(Q2,2,degree_bound);
			temp:=XAdd(l[2],l[4],l[3]);
			M:=phi2`domain;
			pushed_points2:=Evaluate(phi2,[M!temp,M!l[3],M!XAdd(temp,l[3],2*l[2])]);
			previous_iso:=l[1];
			if previous_iso ne [] then
				phi:=previous_iso[#previous_iso];
				phi:=AdjustingAlpha(phi,domain(phi),M`alpha);
				previous_iso[#previous_iso]:=phi;
			end if;

			new_list := Append(new_list, <previous_iso cat [phi2], pushed_points2[1], pushed_points2[2], pushed_points2[3]>);
		end for;
		list:=new_list;

	end for;

	return [l[1] : l in list];
end function;


// There is a non-backtraking path of 2-isogenies of length "distance" from E1 to E2.
isogeny_meet_in_the_middle := function( E1, E2, distance);
	if distance eq 0 then
		return [Isomorphism(E1, E2)];
	end if;

	n1 := Ceiling(distance/2);
	n2 := distance - n1;


	list1 := build_list_meet_in_the_middle(E1, n1);
	list2 := build_list_meet_in_the_middle( E2, n2);

	list1 := [<l, jInvariant(codomain(l[#l]))> : l in list1];
	list2 := [<l, jInvariant(codomain(l[#l]))> : l in list2];

	middle := SetToSequence(Set([l[2] : l in list1]) meet Set([l[2] : l in list2]));

	if IsEmpty(middle) then
		"meet in the middle failed !";
		return 0;
	end if;

	middle := middle[1];


	path1 := [l : l in list1 | l[2] eq middle][1][1];
	path2 := [l : l in list2 | l[2] eq middle][1][1];
	path2[#path2]:=AdjustingAlpha(path2[#path2]);
	assert IsIsomorphic(E2,domain(path2[1]));

	corrected_isogeny := path1[#path1];
	// The following avoids some annoying sequence mutation error
	if distance eq 1 then
		return [corrected_isogeny];
	else
		path1[#path1] := corrected_isogeny;
		//we need the dual of path2
		path2_dual:=Reverse([DualIsogeny(iso) : iso in path2]);
		assert IsIsomorphic(domain(path2[1]),codomain(path2_dual[#path2_dual]));
		assert IsIsomorphic(domain(path2_dual[1]),codomain(path2[#path2]));
		assert IsIsomorphic(domain(path2_dual[1]),codomain(path1[#path1]));
		M1:=codomain(path1[#path1]);
		M2:=domain(path2_dual[1]);
		isom:=[];
		//this handles when the representation for the meeting point are not the same
		// isom contains the needed isomorphism
		if M1`A ne M2`A then
			isom:=[Isomorphism(M1,M2)];
		end if;
		return path1 cat path2_dual,isom;
	end if;
end function;

//testing the above function
//might not be up to date
test_isogeny_meet_in_the_middle := function()
	n := exponent_power_of_2_rational_torsion;
	diameter:=2;
	l := diameter + 2;
	P := basis_2[2]*2^(n-1);
	ker := (basis_2[1] + Random(2^(l-1))*basis_2[2])*2^(n-l);
	isogenies := kernel_generator_to_isogeny_power(Project(ker),[<2,l>]);
	[jInvariant(domain(iso)): iso in isogenies];
	E1 := codomain(isogenies[1]);
	E2 := domain(isogenies[#isogenies]);
	jInvariant(E1);
	jInvariant(E2);
	distance := diameter;
	t:=ClockCycles();
	path := isogeny_meet_in_the_middle(E1,E2,distance);
	timediff(t);
	&and[IsIsomorphic(codomain(path[i]),domain(path[i+1])) : i in [1..#path-1]];
	IsIsomorphic(domain(path[1]),E1);
	IsIsomorphic(codomain(path[#path]),E2);
	#path eq distance;

	return 0;
end function;



// I of norm d*2^(2*exponent_power_of_2_rational_torsion + epsilon) where d divides available_torsion^2
// J containing I, of norm d
// K equivalent to J, of norm a power of two
// returns the isogeny phi such that phi_I = phi o phi_J, and an ideal of norm dividing available_odd_torsion^2 equivalent to I
//dual option is if we want the dual of phi instead of phi
ideal_to_isogeny_remote_small_power_of_2_new := function(I, J, K, distance, phi_J, phi_K,isom_K:dual:=false);
	B<i,j,k>:=Parent(Basis(O0)[1]);
	n := exponent_power_of_2_rational_torsion;
	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);

	isom_K_loc:=[];
	n1 := Minimum(Ceiling(distance/2), n);
	n2 := Minimum(distance - n1, n);
	epsilon := distance - n1 - n2;

	assert Norm(I) eq Norm(J)*2^Valuation(Integers()!Norm(I),2);
	assert Valuation(Integers()!Norm(I),2) eq distance;
	assert [bas in J: bas in Basis(I)] eq [true,true,true,true];

	if #phi_K ne 0 then
		assert IsIsomorphic(codomain(phi_K[#phi_K]),codomain(phi_J[#phi_J]));
		assert IsIsomorphic(domain(phi_K[1]),domain(phi_J[1]));
	end if;


	if dual and epsilon ne 0 then
		"there may be a problem with the dual of the meet in the middle";
	end if;
	if epsilon gt 60 then
		"WARNING: meet-in-the-middle distance is very large";
	end if;

	//using It as the smallest equivalent ideal, this is to avoid unecessary factors + make KLPT faster
	//L is the KLPT odd equivalent ideal
	It:=small_equivalent_ideal(I);
	if #phi_K + distance lt 120 then
		v1:=Valuation(Integers()!Norm(I),2);
		v2:=Valuation(Integers()!Norm(It),2);
		if v1 ne v2 then
			"modified loop";
			I:=It;
			n2-:=v1-v2;
		end if;
		L:=cyclic_ideal(QuaternionIsogenyPath_specialConstraint_small2power_input(O0,i,j,I,-1,T2,fT2));
	else
		good:=Floor(Log(Norm(It))/Log(2)) le 80 ;
		L := cyclic_ideal(QuaternionIsogenyPath_specialConstraint2(O0,i,j,It,-1,T2,fT2:good_input:=good));
	end if;

	// in this case, the computation is quick we don't need to compute all the complicated stuff, this assumes that this is used during the last round of computation, otherwise some of the output might not be correct
	if distance le n then
		n1:=distance;
		I1:=I+O0*2^distance;
		ker1 := ideal_to_kernel_generator_2n_precomp(I1,n1);
		ker1_E1:=eval_isogenies(Project(ker1),phi_J);
		assert IsIdentity(2^n1*ker1_E1);
		assert not IsIdentity(2^(n1-1)*ker1_E1);

		phi1 := kernel_generator_to_isogeny_power(Project(ker1_E1),[<2,distance>]);
		return phi1,L,[],[];
	end if;
	assert GCD([Integers()!Norm(L),2]) eq 1;
	//compute phi1
	I1 := I + O0*2^n1;
	I1_extended:=I+O0*2^(n1+epsilon);
	ker1 := ideal_to_kernel_generator_2n_precomp(I1,n1);
	ker1_E1:=eval_isogenies(Project(ker1),phi_J);
	assert IsIdentity(2^n1*ker1_E1);
	assert not IsIdentity(2^(n1-1)*ker1_E1);
	phi1 := kernel_generator_to_isogeny_power(Project(ker1_E1),[<2,n1>]);
	//compute the two ideals H_1,H_2
	morph, alpha_ := LeftIsomorphism(J,K);
	alpha := alpha_*Norm(J);
	morph, beta_ := LeftIsomorphism(L,I);
	beta := beta_*Norm(L);
	gamma := beta*alpha/Norm(J);
	g := GCD([Integers()!g : g in Eltseq(O0!gamma)]);
	// when g is not 1, it means there is some backtrakingn need to be careful...
	assert gamma in O0;
	//first half of L sent to O0 with K
	H1 := O0*gamma + O0*T;
	gen_H1 := ideal_to_kernel_generator_precomp(H1,Factorisation(Integers()!Norm(H1)));
	assert <IsIdentity(gen[2]*gen[1]): gen in gen_H1> eq <true,true>;
	gen_H1:=<<Project(gen[1]),gen[2],gen[3],Project(gen[4])>: gen in gen_H1>;
	phi_K_and_1 := phi_K cat phi1;
	gen_H1_through_phi := <<eval_isogenies(gen[1],phi_K_and_1:isoms:=isom_K),gen[2],gen[3],eval_isogenies(gen[4],phi_K_and_1:isoms:=isom_K)> : gen in gen_H1>;
	assert <IsIdentity(gen[2]*gen[1]): gen in gen_H1_through_phi> eq <true,true>;

	isogenies_H1_through_phi := list_kernel_generators_to_isogeny(gen_H1_through_phi);

	//compute the dual as well, this appears to be more efficient if we have it
	// t1:=ClockCycles();
	isogenies_H1_dual_through_phi,gen_H1_dual_through_phi:=dual_odd_isogeny(isogenies_H1_through_phi,gen_H1_through_phi);
	// "dual time :",timediff(t1);
	//second half of L
	H2 := O0*Conjugate(gamma) + O0*(Norm(gamma)/(Norm(H1) * 2^Valuation(Integers()!Norm(gamma),2)));
	assert Norm(H1)*Norm(H2) eq Norm(L);
	gen_H2 := ideal_to_kernel_generator_precomp(H2,Factorisation(Integers()!Norm(H2)));
	gen_H2:=<<Project(gen[1]),gen[2],gen[3]>: gen in gen_H2>;
	assert <IsIdentity(gen[2]*gen[1]): gen in gen_H2> eq <true,true>;
	phi_H2 := list_kernel_generators_to_isogeny(gen_H2);
	//computation of phi2
	I2 := O0*Conjugate(gamma/g) + O0*2^n2; // divide by g, is case phi1 backtracks along phi_K
	assert [bas in O0: bas in Basis(I2)] eq [true,true,true,true];
	assert [bas in O0: bas in Basis(H2)] eq [true,true,true,true];
	assert [bas in O0: bas in Basis(I1)] eq [true,true,true,true];
	assert [bas in O0: bas in Basis(H1)] eq [true,true,true,true];
	assert Norm(I2)*Norm(I1) eq 2^(distance - epsilon);

	ker2 := ideal_to_kernel_generator_2n_precomp(I2,n2);
	ker2:=Project(ker2);
	ker2_pushed := eval_isogenies(ker2,phi_H2);
	assert IsIdentity(2^n2*ker2_pushed);
	phi2 := kernel_generator_to_isogeny_power(ker2_pushed,[<2,n2>]);

	//now entering the meet in the middle part, epsilon is the meet in the middle distance
	if epsilon gt 0 then
		//compute the mitm path
		path_mitm,isom_mit := isogeny_meet_in_the_middle(codomain(isogenies_H1_through_phi[#isogenies_H1_through_phi]), codomain(phi2[#phi2]), epsilon);
		ker_mitm := two_isogenies_to_kernel(path_mitm:isom_mitm:=isom_mit);
		//push it through the dual
		ker_mitm_pullback :=eval_isogenies(Project(ker_mitm),isogenies_H1_dual_through_phi);
		phi_mitm := kernel_generator_to_isogeny_power(Project(ker_mitm_pullback),[<2,epsilon>]);
	else
		assert IsIsomorphic(codomain(isogenies_H1_through_phi[#isogenies_H1_through_phi]),codomain(phi2[#phi2]));
		path_mitm:=  [];
		phi_mitm := [];
		isom_mit:=[];
	end if;
	assert <IsIdentity( (gen[2])*gen[1]): gen in gen_H1_dual_through_phi> eq <true,true>;
	//pushing the dual of H1 through the path_mitm
	gen_H1_final:=<<eval_isogenies(gen[1],path_mitm:isoms:=isom_mit),gen[2],gen[3]>:gen in gen_H1_dual_through_phi>;
	if #path_mitm ne 0 then
		assert IsIsomorphic(codomain(path_mitm[#path_mitm]),codomain(phi2[#phi2]));
	end if;
	assert <IsIdentity(gen[2]*gen[1]): gen in gen_H1_final> eq <true,true>;

	//now computing the final half of L through phi2
	phi2_dual,ker_phi2_dual:=dual_two_isogenies_kernel(phi2,ker2_pushed);
	assert IsIsomorphic(domain(phi2_dual[1]),gen_H1_final[1][1]`curve);
	gen_H1_final:=<<eval_isogenies(gen[1],phi2_dual),gen[2],gen[3]>:gen in gen_H1_final>;
	assert <IsIdentity(gen[2]*gen[1]): gen in gen_H1_final> eq <true,true>;
	isogenies_H1_final:=list_kernel_generators_to_isogeny(gen_H1_final);

	//pushing the final part of the two isogeny through the second half of L and computing the dual
	assert IsIsomorphic(codomain(phi2_dual[#phi2_dual]),domain(phi2[1]));
	assert IsIsomorphic(ker2_pushed`curve,domain(isogenies_H1_final[1]) );
	ker_phi2_pullback := eval_isogenies(ker2_pushed,isogenies_H1_final);
	phi2_pullback := kernel_generator_to_isogeny_power(Project(ker_phi2_pullback),[<2,n2>]);
	//computing isomorphisms if the two halves dont meet with the same representation
	if not dual then
		phi2_dual_pullback:=dual_two_isogenies(phi2_pullback);
		if #phi_mitm ne 0 then
			assert IsIsomorphic(codomain(phi_mitm[#phi_mitm]),codomain(phi2_pullback[#phi2_dual_pullback]));
		end if;
		i:=n1+epsilon;
		new_phi:=phi1 cat phi_mitm cat phi2_dual_pullback;
		M1:=codomain(new_phi[i]);
		M2:=domain(new_phi[i+1]);
		if M1`A ne M2`A then
			isom:=Isomorphism(M1,M2);
			isom_K_loc:=[isom];
		end if;
	else
		phi1_dual:=dual_two_isogenies(phi1);
		assert IsIsomorphic(domain(phi1_dual[1]),codomain(phi2_pullback[#phi2_pullback]));
		M1:=codomain(phi2_pullback[#phi2_pullback]);
		M2:=domain(phi1_dual[1]);
		if M1`A ne M2`A then
			isom:=Isomorphism(M1,M2);
			isom_K_loc:= [isom];
		end if;
		new_phi:=phi2_pullback cat phi1_dual;
	end if;

	return new_phi, L, phi_H2 cat isogenies_H1_final,isom_K_loc;
end function;



// I of norm 2^N*d2 where d2 divides T
// J of norm d1 dividing T^2 where O_R(J) = O_L(I)
// K equivalent to J, of norm a power of two
// returns the isogeny phi_I
//other_side_* correspond to isogenies and ideal at the end of the desired isogeny
//in the context of sqisign this is known and can help to improve the computation time by computing a 2^32 isogeny from the end
ideal_to_isogeny_power_of_two := function(I, J, K, phi_J, phi_K,isom_K,epsilon:other_side_isogeny:=[],other_side_ideal:=lideal<O0|1>);
	n := exponent_power_of_2_rational_torsion;
	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	other_side:=0;
	//other side parameter is the length of the isogeny at the end
	if other_side_isogeny ne [] then
		other_side:=n;
	end if;
	N_tot:=Valuation(Integers()!Norm(I), 2);

	N := N_tot-other_side;
	odd_norm:=Z!Norm(I) div 2^N_tot;
	//contains the path of size N that will be computed straightforwardly
	I_first:= I + LeftOrder(I)*2^N;
	//I_second contains the odd torsion + the other_size bit
	I_second:=Conjugate(I_first)*I*lideal<RightOrder(I)|1/2^N>;
	I_odd:=I_second + LeftOrder(I_second)*odd_norm;
	I_last:=Conjugate(I_odd)*I_second*lideal<RightOrder(I_second) | 1/odd_norm>;
	I_long:=J*I_first;
	I_tot:=I_long*I_second;

	long_isogeny := [];
	iterations := Floor(N/(2*n + epsilon));
	I_step := I_long + O0*(T2*2^(2*n + epsilon));
	assert Valuation(Integers()!Norm(I_step),2) eq 2*n+epsilon;
	J_step := J;
	K_step := K;
	phi_K_step := phi_K;
	phi_J_step := phi_J;
	isom_K_step:=isom_K;
	isom_isogeny:=[];
	for ctr in [1..iterations] do
		isogeny, J_step,
		phi_J_step, isom_K := ideal_to_isogeny_remote_small_power_of_2_new(I_step, J_step, K_step, 2*n + epsilon, phi_J_step, phi_K_step,isom_K_step);
		isom_isogeny:=isom_isogeny cat isom_K;
		isom_K_step:=isom_K_step cat isom_K;
		long_isogeny := long_isogeny cat isogeny;
		phi_K_step := phi_K_step cat isogeny;
		//update K_step
		bound := Ceiling(Log(Integers()!(Norm(J_step)*Norm(K_step)))/Log(2)+(2*n + epsilon));
		isct:=K_step meet Conjugate(J_step);
		repeat
			bound +:= 1;
			vec := Enumerate(isct,2^bound);
		until #vec gt 1;
		alpha := vec[2];
		K_step := O0*alpha + O0*2^Valuation(Integers()!Norm(alpha),2);
		assert Valuation(Integers()!Norm(K_step),2) eq #phi_K_step;
		assert 2^Valuation(Integers()!Norm(K_step),2) eq Z!Norm(K_step);

		//updating I_step
		if ctr ne iterations then
			I_next:=I_long + O0*(T2*2^((ctr+1)*(2*n + epsilon)));
		else
			I_next:=I_long + O0*(T2*2^(N));
		end if;
		I_step:=J_step*small_equivalent_ideal(Conjugate(J_step)* (I_next) );
		assert 2^Valuation(Z!Norm(I_step),2) eq Z!(Norm(I_step)/Norm(J_step));
		assert Valuation(Integers()!Norm(I_step),2) eq 2*n+epsilon or Valuation(Integers()!Norm(I_step),2) eq N-iterations*(2*n+epsilon);
	end for;
	distance := N - iterations * (2*n + epsilon);
	if IsZero(distance) then
		return long_isogeny,isom_isogeny,J_step,phi_J_step ;
	//performing a last step when the count is not exact
	//for efficieny we would like this last step to be smaller than n
	else
		last_isogeny,J_step,
		phi_J_step,isom_K := ideal_to_isogeny_remote_small_power_of_2_new(I_step, J_step, K_step, distance, phi_J_step, phi_K_step,isom_K_step);
		isom_isogeny:=isom_isogeny cat isom_K;
		long_isogeny:=long_isogeny cat last_isogeny;
		phi_K_step := phi_K_step cat last_isogeny;
		isom_K_step:=isom_K_step cat isom_K;
	end if;
	//in case the odd_norm is not one.
	if odd_norm ne 1 then
		"odd norm";
		K_step:=K_step*small_equivalent_ideal(Conjugate(K_step)*J_step);
		_,delta:=LeftIsomorphism(K_step,I_long);
		I_odd:=I_odd*lideal<RightOrder(I_odd)|Conjugate(delta)/Norm(delta)>;
		I_odd:=rideal<LeftOrder(I_odd)|delta>*I_odd;
		H:= K_step*I_odd + O0*odd_norm;
		gen_H := ideal_to_kernel_generator_precomp(H,Factorisation(odd_norm));
		gen_H1:=<<Project(gen[1]),gen[2],gen[3],Project(gen[4])>: gen in gen_H>;
		gen_H_through_phi_K := <<eval_isogenies(gen[1],phi_K_step:isoms:=isom_K_step),gen[2],gen[3]> : gen in gen_H1>;
		isogenies_H_through_phi_K := list_kernel_generators_to_isogeny(gen_H_through_phi_K);
		long_isogeny:=long_isogeny cat isogenies_H_through_phi_K;
		_,delta:=LeftIsomorphism(J_step,K_step);
		I_odd:=I_odd*lideal<RightOrder(I_odd)|Conjugate(delta)/Norm(delta)>;
		I_odd:=rideal<LeftOrder(I_odd)|delta>*I_odd;
		J_step:=J_step*I_odd;
	end if;
	//in case the other_side is not zero
	//this is an optimization
	if not IsZero(other_side) then
		_,delta:=LeftIsomorphism(other_side_ideal,I_tot);
		I_last:=I_last*lideal<RightOrder(I_last)|Conjugate(delta)/Norm(delta)>;
		I_last:=rideal<LeftOrder(I_last)|delta>*I_last;
		I1:=(other_side_ideal*Conjugate(I_last) ) + O0*2^n;
		I1_extended :=(other_side_ideal*Conjugate(I_last) ) + O0*2^other_side;
		ker := ideal_to_kernel_generator_2n_precomp(I1,n);
		ker_pushed:=eval_isogenies(Project(ker),other_side_isogeny);
		phi_last:=kernel_generator_to_isogeny_power(ker_pushed,[<2,n>]);
		phi_last_dual:=dual_two_isogenies(phi_last);
		assert IsIsomorphic(codomain(long_isogeny[#long_isogeny]),codomain(phi_last[#phi_last]));
		if codomain(long_isogeny[#long_isogeny])`A ne domain(phi_last_dual[1])`A then
			isom:=Isomorphism(codomain(long_isogeny[#long_isogeny]),domain(phi_last_dual[1]));
			isom_isogeny:=isom_isogeny cat [isom];
		end if;
		long_isogeny:=long_isogeny cat phi_last_dual;
	end if;
	return long_isogeny,isom_isogeny,J_step,phi_J_step;
end function;


//generates the sqisign key
//uses the optimization that N = p^1/4
gen_keys :=function()
	q:=1;
	L:=2;
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	bitsize_p:=Floor(Log(p)/Log(L));
	//size of the L^e secret isogeny
	size:=256;
	N2:=L^size;
	//generating a random ideal of norm N1 with log(N1) = bitsize_N
	//the point is to take N1 << sqrt(p) (for instance N1 = p^1/4)
	bitsize_N:=bitsize_p div 4;

	foundsol:=false;
	repeat
		while not foundsol do
			repeat
			N1:=RandomPrime(bitsize_N);
			until N1*N2 gt 2*p and (LegendreSymbol(-q,N1) eq -1) and (GCD(N1,q) eq 1) and ((L eq -1) or not(IsSquare(IntegerRing(N1)!L)));

				m:=Floor(Sqrt((N1*N2)/(2*p)));
				compt:=0;
				while compt le Minimum(1000,2*m^2) and not foundsol do
					compt:=compt+1;
					repeat
						c:=Random(-m,m); d:=Random(-m,m);
					until c^2+d^2 ne 0;
					M:=N1*N2 - p*(c^2+d^2);
					foundsol:=CornacciaNice(M);
					if foundsol then
						foundsol,a,b:=NormEquation(1,M);   // computation repeated due to Magma syntax, can this be avoided?
					end if;

				end while;
		end while;
		quat:=B![a,b,c,d];
		secret_ideal:=lideal<order|[N1,quat]>;
		K:=cyclic_ideal(lideal<order|[N2,Conjugate(quat)]>:full:=true);

		//this is necessary because of some error happening sometimes in the translation
		//I did not find what was the problem, the error has a 10% chance of occurring approx.
		try
			phi_K,isom_K,J,phi_J:=ideal_to_isogeny_power_of_two(K,lideal<O0|1>,lideal<O0|1>,[],[],[],0);
		catch e
			foundsol:=false;
		end try;
	until foundsol;
	pk:=codomain(phi_K[#phi_K]);
	return secret_ideal,pk, K,phi_K,isom_K,J,phi_J;
end function;

//first set of commitment/challenge that are odd : this is more efficient
//the challenge uses the 128 bits of 3 and 5 torsions
// the commitment needs to have 256 bits at least, this is obtained by taking all the remaining odd torsion
gen_commitment_odd:=function()
	M1 := Matrix([[1,0],[0,1]]);
	M:=SemiMontgomery(E0);
	cof:= GCD([p+1,available_odd_torsion]) div (5^21);
	cof_twist:= GCD( [(p-1),available_odd_torsion]) div (3^53);
	ker:=ZeroPt(E0);
	ker_orth:=ZeroPt(E0);
	ker_twist:=ZeroPt(E0_twist);
	ker_orth_twist:=ZeroPt(E0_twist);
	H:=lideal<O0|1>;
	for i in [1..#basis] do
		L:=torsion_data[i][1];
		e:=torsion_data[i][2];
		if L ne 5 then
			if i ne #basis then
				if L ne torsion_data[i+1][1] then
					torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
					P:=basis_Le[1];
					Q:=basis_Le[2];
					M2 := action_dist_Le;
					M3_double := (M1 + action_distfrob_Le);
					M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
					M4_double := (action_dist_Le + action_frob_Le);
					M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
					kerL:=P+Random(1,L)*Q;
					ker:=ker+kerL;
					ker_orth:=ker_orth+Q;
					H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
				end if;
			else
				torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
				P:=basis_Le[1];
				Q:=basis_Le[2];
				M2 := action_dist_Le;
				M3_double := (M1 + action_distfrob_Le);
				M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
				M4_double := (action_dist_Le + action_frob_Le);
				M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
				kerL:=P+Random(1,L)*Q;
				ker:=ker+kerL;
				ker_orth:=ker_orth+Q;
				H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
			end if;
		end if;
	end for;
	for i in [1..#basis_twist] do
		L:=torsion_data_twist[i][1];
		e:=torsion_data_twist[i][2];
		if L ne 3 then
			if i ne #basis_twist then
				if L ne torsion_data_twist[i+1][1] then
					torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
					P:=basis_Le[1];
					Q:=basis_Le[2];
					M2 := action_dist_Le;
					M3_double := (M1 + action_distfrob_Le);
					M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
					M4_double := (action_dist_Le + action_frob_Le);
					M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
					kerL:=P+Random(1,L)*Q;
					ker_twist:=ker_twist+kerL;
					ker_orth_twist:=ker_orth_twist+Q;
					H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
				end if;
			else
				torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
				P:=basis_Le[1];
				Q:=basis_Le[2];
				M2 := action_dist_Le;
				M3_double := (M1 + action_distfrob_Le);
				M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
				M4_double := (action_dist_Le + action_frob_Le);
				M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
				kerL:=P+Random(1,L)*Q;
				ker_twist:=ker_twist+kerL;
				ker_orth_twist:=ker_orth_twist+Q;
				H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
			end if;
		end if;
	end for;
	gen_commit:=< <Project(ker),cof,Factorization(cof),Project(ker_orth)>,<Project(ker_twist),cof_twist,Factorization(cof_twist),Project(ker_orth_twist)> >;
	phi_commit:=list_kernel_generators_to_isogeny(gen_commit);
	phi_dual:=dual_odd_isogeny(phi_commit,gen_commit);
	commitment:=codomain(phi_commit[#phi_commit]);
	return commitment,phi_commit,phi_dual,H;
end function;

//for now the challenge is just random
// the degree of the challenge isogeny is hardcoded in this function
gen_challenge_odd:=function(phi_commit_dual,I_commit)
	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	cof:=(p+1) div 5^21;
	cof_twist:=(p-1) div 3^53;
	M:=domain(phi_commit_dual[1]);
	repeat
		ker:=RandomXZ(M,true)*cof;
		ker5:=5^20*ker;
	until IsIdentity(5*ker5) and not IsIdentity(ker5);
	repeat
		ker_twist:=RandomXZ(M,false)*cof_twist;
		ker3_twist:=3^52*ker_twist;
	until IsIdentity(3*ker3_twist) and not IsIdentity(ker3_twist);
	gen:=< <ker,5^21,[<5,21>] >,<ker_twist,3^53,[<3,53>]> >;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen> eq <true,true>;
	isogenies_challenge:=list_kernel_generators_to_isogeny(gen);
	challenge:=codomain(isogenies_challenge[#isogenies_challenge]);
	gen0:=<<eval_isogenies(gene[1],phi_commit_dual),gene[2]> : gene in gen>;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen0> eq <true,true>;
	H1:=kernel_to_ideal_O0_prime_power(5,21,gen0[1][1],gen0[1][1],gen0[1][1]);
	H2:=kernel_to_ideal_O0_prime_power(3,53,gen0[2][1],gen0[2][1],gen0[2][1]);
	H := H1 meet H2;
	assert Norm(H) eq Norm(H1)*Norm(H2);
	H_challenge:= H meet I_commit;
	assert Norm(H_challenge) eq Norm(H)*Norm(I_commit);
	return isogenies_challenge,challenge,H_challenge;
end function;

//second set of commitment/challenge
//now the challenge is a chain of 2-isogenies
// gen_commitment gives one odd and one power of 2 isogenies, both equivalent
gen_commitment :=function()
	n:=exponent_power_of_2_rational_torsion;
	epsilon:=0;
	L:=2;
	q:=1;
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	T := available_odd_torsion;
	T2:=T^2;
	fT:=Factorization(T);
	N2:=L^128;
	foundsol:=false;
	while not foundsol do
		N1:=NextPowerSmoothConstraint(Ceiling(1000*p/N2),T,fT);
			m:=Floor(Sqrt((N1*N2)/(2*p)));
			compt:=0;
			while compt le Minimum(1000,2*m^2) and not foundsol do
				compt:=compt+1;
				repeat
					c:=Random(-m,m); d:=Random(-m,m);
				until c^2+d^2 ne 0;
				M:=N1*N2 - p*(c^2+d^2);
				foundsol:=CornacciaNice(M);
				if foundsol then
					foundsol,a,b:=NormEquation(1,M);   // computation repeated due to Magma syntax, can this be avoided?
				end if;

			end while;
	end while;
	quat:=B![a,b,c,d];
	Ic_odd:=lideal<O0|[quat,N1]>;
	Ic_even:=cyclic_ideal(lideal<O0|[Conjugate(quat),N2]>);
	N:=Valuation(Integers()!Norm(Ic_even),L);
	Ic_start:=Ic_even+O0*L^(2*n+epsilon);
	J_step:=lideal<O0|1>;
	K_step:=lideal<O0|1>;
	genc_odd := ideal_to_kernel_generator_precomp(Ic_odd,Factorisation(Integers()!Norm(Ic_odd)));
	genc_odd := <<Project(gen[1]),gen[2],gen[3]>: gen in genc_odd>;
	phic_odd:=list_kernel_generators_to_isogeny(genc_odd);
	phic_even, J ,phi_J,isom:=ideal_to_isogeny_remote_small_power_of_2_new(Ic_start,J_step,K_step,2*n+epsilon,[],[],[]:dual:=true);
	J_step:=J;
	bound := Ceiling(Log(Integers()!(Norm(J_step)*Norm(K_step)))/Log(2)+(2*n + epsilon));
	isct:=K_step meet Conjugate(J);
	repeat
		bound +:= 1;
		vec := Enumerate(isct,2^bound);
	until #vec gt 1;
	alpha := vec[2]; // vec[1] is 0
	K_step := cyclic_ideal(O0*alpha + O0*2^Valuation(Integers()!Norm(alpha),2));
	I_short_next_odd := equivalent_coprime_ideal(Ic_even + O0*(T2*2^((2)*(2*n + epsilon))), 2*Integers()!Norm(J_step));
	distance:=N - (2*n + epsilon);
	bound := Ceiling(Log(Integers()!(Norm(I_short_next_odd)*Norm(J_step)))/Log(2)+(distance ));
	K_isct:=J_step meet Conjugate(I_short_next_odd);
	repeat
		vec := Enumerate(K_isct,2^bound);
		bound +:= 1;
	until #vec gt 1;
	alpha := vec[2]; // vec[1] is 0
	I_step := cyclic_ideal(O0*alpha + O0*(Norm(J_step)*2^Valuation(Integers()!Norm(alpha),2)));
	n1 := Minimum(Ceiling(distance/2), n);
	n2 := Minimum(distance - n1, n);
	epsilon:=distance -n1 -n2;
	if epsilon ne 0 then "there should be a mitm or somehting else"; end if;
	I1 := I_step + O0*2^n1;
	ker1 := ideal_to_kernel_generator_2n_precomp(I1,n1);
	ker1_E1:=eval_isogenies(Project(ker1),phi_J);
	phi1 := kernel_generator_to_isogeny_power(Project(ker1_E1),[<2,n1>]);
	morph, alpha_ := LeftIsomorphism(J_step,K_step);
	alpha := alpha_*Norm(J_step);
	morph, beta_ := LeftIsomorphism(Ic_odd,I_step);
	beta := beta_*Norm(Ic_odd);
	gamma := beta*alpha/Norm(J_step);
	g := GCD([Integers()!g : g in Eltseq(O0!gamma)]);
	I2 := O0*Conjugate(gamma/g) + O0*2^n2; // divide by g, is case phi1 backtracks along phi_K
	ker2 := ideal_to_kernel_generator_2n_precomp(I2,n2);
	ker2:=Project(ker2);
	ker2_pushed := eval_isogenies(ker2,phic_odd);
	phi2 := kernel_generator_to_isogeny_power(ker2_pushed,[<2,n2>]);
	assert IsIsomorphic(codomain(phi1[#phi1]),codomain(phi2[#phi2]));
	phi1_dual:=dual_two_isogenies(phi1);
	phic_even:= phi2 cat phi1_dual cat phic_even;
	M1:=codomain(phi2[#phi2]);
	M2:=domain(phi1_dual[1]);
	if M1`A ne M2`A then
		isomorph:=Isomorphism(M1,M2);
		isom:= [isomorph] cat isom;
	end if;
	return Ic_odd,phic_odd,genc_odd,Ic_even,phic_even,isom;
end function;

//for now the challenge is just random
gen_challenge:=function(phic_even,isomc_even,Ic_even)
	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	cof:=(p+1) div 5^21;
	cof_twist:=(p-1) div 3^53;
	M:=domain(phic_even[1]);
	repeat
		ker:=RandomXZ(M,true)*cof;
		ker5:=5^20*ker;
	until IsIdentity(5*ker5) and not IsIdentity(ker5);
	repeat
		ker_twist:=RandomXZ(M,false)*cof_twist;
		ker3_twist:=3^52*ker_twist;
	until IsIdentity(3*ker3_twist) and not IsIdentity(ker3_twist);
	gen:=< <ker,5^21,[<5,21>] >,<ker_twist,3^53,[<3,53>]> >;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen> eq <true,true>;
	isogenies_challenge:=list_kernel_generators_to_isogeny(gen);
	challenge:=codomain(isogenies_challenge[#isogenies_challenge]);
	gen0:=<<eval_isogenies(gene[1],phic_even:isoms:=isomc_even),gene[2]> : gene in gen>;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen0> eq <true,true>;
	H1:=kernel_to_ideal_O0_prime_power(5,21,gen0[1][1],gen0[1][1],gen0[1][1]);
	H2:=kernel_to_ideal_O0_prime_power(3,53,gen0[2][1],gen0[2][1],gen0[2][1]);
	H := H1 meet H2;
	assert Norm(H) eq Norm(H1)*Norm(H2);
	H_challenge:= H meet Ic_even;
	assert Norm(H_challenge) eq Norm(H)*Norm(Ic_even);
	return isogenies_challenge,challenge,H_challenge;
end function;

//generate the challenge honestly, mostly like gen-challenge_odd but the kernel depends on the message and the commitment
// the degree of the challenge isogeny is hardcoded in this function
// given the randomness in magma, we assume that the message is given as a pair of 32,64 bit integers (32 for the seed and 64 for the number of steps)
//this is the challenge for the prover, the conversion into ideal is also handled in that function
gen_honest_challenge_prover:=function(phi_commit_dual,I_commit,m)
	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	cof:=(p+1) div 5^21;
	cof_twist:=(p-1) div 3^53;
	M:=domain(phi_commit_dual[1]);
	//set the seed according to the message
	SetSeed(m[1],1);
	repeat
		ker:=RandomXZ(M,true)*cof;
		ker5:=5^20*ker;
	until IsIdentity(5*ker5) and not IsIdentity(ker5);
	repeat
		ker_twist:=RandomXZ(M,false)*cof_twist;
		ker3_twist:=3^52*ker_twist;
	until IsIdentity(3*ker3_twist) and not IsIdentity(ker3_twist);
	gen:=< <ker,5^21,[<5,21>] >,<ker_twist,3^53,[<3,53>]> >;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen> eq <true,true>;
	isogenies_challenge:=list_kernel_generators_to_isogeny(gen);
	challenge:=codomain(isogenies_challenge[#isogenies_challenge]);
	gen0:=<<eval_isogenies(gene[1],phi_commit_dual),gene[2]> : gene in gen>;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen0> eq <true,true>;
	H1:=kernel_to_ideal_O0_prime_power(5,21,gen0[1][1],gen0[1][1],gen0[1][1]);
	H2:=kernel_to_ideal_O0_prime_power(3,53,gen0[2][1],gen0[2][1],gen0[2][1]);
	H := H1 meet H2;
	assert Norm(H) eq Norm(H1)*Norm(H2);
	H_challenge:= H meet I_commit;
	assert Norm(H_challenge) eq Norm(H)*Norm(I_commit);
	return isogenies_challenge,challenge,H_challenge;
end function;

//basically same as above but for the verifier so without there is no isogeny to ideal conversion
gen_honest_challenge_verifier:=function(commit,m)
	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	cof:=(p+1) div 5^21;
	cof_twist:=(p-1) div 3^53;
	M:=commit;
	//set the seed according to the message
	SetSeed(m[1],1);
	repeat
		ker:=RandomXZ(M,true)*cof;
		ker5:=5^20*ker;
	until IsIdentity(5*ker5) and not IsIdentity(ker5);
	repeat
		ker_twist:=RandomXZ(M,false)*cof_twist;
		ker3_twist:=3^52*ker_twist;
	until IsIdentity(3*ker3_twist) and not IsIdentity(ker3_twist);
	gen:=< <ker,5^21,[<5,21>] >,<ker_twist,3^53,[<3,53>]> >;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen> eq <true,true>;
	isogenies_challenge:=list_kernel_generators_to_isogeny(gen);
	challenge:=codomain(isogenies_challenge[#isogenies_challenge]);
	return challenge;
end function;

//take a walk,
//decomposed as a sequence of two isogenies whose successive domain and codomain is isomorphic (but not necessarily equal)
//and output a normalized walk (groups of isogenies of degree 2^32)
normalized_two_walk:=function(phi,isom)
	n:=32;
	len:=#phi div n;
	walk:=[];
	zip:=[];
	//the role of swap is to determine the order of the basis used
	swap:=[];
	Mt:=Montgomery(domain(phi[1]),Fq!1);
	index_isom:=1;
	isom_temp:=isom;
	for i in [1..len] do
		M:=Montgomery(domain(phi[1+n*(i-1)]),Fq!1);
		basis := deterministic_two_basis(SemiMontgomery(Mt),n);
		basis:=[Mt!Lift(Normalized(b),Mt): b in basis];
		M2:=Montgomery(codomain(phi[n*(i)]),Fq!1);
		index_add:=0;
		for j in [1..n-1] do
			if codomain(phi[j+n*(i-1)])`A ne domain(phi[j+1+(n)*(i-1)])`A then
				index_add+:=1;
			end if;
		end for;
		//compute the image of the basis through the curve;
		image:=basis;
		if M`A ne Mt`A then
			// "case to be treated here";
			isom:=Isomorphism(Mt,M);
			image:=[ApplyIsom(isom,M,im): im in image];
		end if;
		sub_iso:=[phi[j+ n*(i-1)]: j in [1..n]];
		image:=[eval_isogenies(Project(b),sub_iso:isoms:=isom_temp): b in image];
		// the lift depends on M2 which will depend on the isomorphic representative chosen so it is not good.
		//edit : this does not seem to be problematic
		image := [M2!Lift(im,M2) : im in image];

		deg:=2^n;
		if IsIdentity(Project(image[1])*2^(n-1)) then
			tmp_image := image[1];
			image[1] := image[2];
			image[2] := tmp_image;

			tmp_basis := basis[1];
			basis[1] := basis[2];
			basis[2] := tmp_basis;
			Append(~swap,1);
		else
			Append(~swap,0);
		end if;



		a := discrete_logarithm_power(image[2],image[1],2,n);
		//solve potential problem of sign during the lift of projective points
		// if IsIdentity(eval_isogenies(Project(basis[2]-a*basis[1]),phi:isoms:=isom_mitm)) then
		test_iso:=kernel_generator_to_isogeny_power(Project(basis[2] - a*basis[1]),[<2,n>]);
		kern:=basis[2];
		if IsIsomorphic(codomain(test_iso[#test_iso]),SemiMontgomery(M2)) then
			Append(~zip,Z!(-a mod 2^n));
			kern:=basis[2] - a*basis[1];
			// Append(~kernels,<kern>);
		else
			Append(~zip,Z!(a mod 2^n));
			kern:=basis[2] + a*basis[1];
			// Append(~kernels,<kern>);
		end if;
		for j in [1..index_add] do
			Remove(~isom_temp,1);
		end for;
		Append(~walk,kernel_generator_to_isogeny_power(Project(kern),[<2,n>]));
		Mt:=Montgomery(codomain(walk[#walk][n]),Fq!1);
		assert(IsIsomorphic(SemiMontgomery(Mt),codomain(phi[n*i])));
	end for;

	//handle the last step which might not be of complete size n
	last_step:=#phi - len*n;
	if last_step ne 0 then
		M:=Montgomery(domain(phi[1+n*(len)]),Fq!1);

		basis := deterministic_two_basis(SemiMontgomery(Mt),n);
		basis:=[ 2^(n-last_step)*bas: bas in basis ];
		basis:=[Mt!Lift(Normalized(b),Mt): b in basis];

		M2:=Montgomery(codomain(phi[#phi]),Fq!1);
		index_add:=0;
		for j in [1..last_step-1] do
			if codomain(phi[j+n*(len)])`A ne domain(phi[j+1+(n)*(len)])`A then
				index_add+:=1;
			end if;
		end for;
		//compute the image of the basis through the curve;
		image:=basis;
		if M`A ne Mt`A then
			// "case to be treated here";
			isom:=Isomorphism(Mt,M);
			image:=[ApplyIsom(isom,M,im): im in image];
		end if;
		sub_iso:=[phi[j+n*len]: j in [1..last_step]];
		image:=[eval_isogenies(Project(b),sub_iso:isoms:=isom_temp): b in image];
		image := [M2!Lift(im,M2) : im in image];

		deg:=2^last_step;
		if IsIdentity(Project(image[1])*2^(last_step-1)) then
			tmp_image := image[1];
			image[1] := image[2];
			image[2] := tmp_image;

			tmp_basis := basis[1];
			basis[1] := basis[2];
			basis[2] := tmp_basis;
			Append(~swap,1);
		else
			Append(~swap,0);
		end if;

		a := discrete_logarithm_power(image[2],image[1],2,last_step);

		//solve potential problem of sign during the lift of projective points
		// if IsIdentity(eval_isogenies(Project(basis[2]-a*basis[1]),phi:isoms:=isom_mitm)) then
		test_iso:=kernel_generator_to_isogeny_power(Project(basis[2] - a*basis[1]),[<2,last_step>]);
		kern:=basis[2];
		if IsIsomorphic(codomain(test_iso[#test_iso]),SemiMontgomery(M2)) then
			Append(~zip,Z!(-a mod 2^last_step));
			kern:=basis[2] - a*basis[1];
			// Append(~kernels,basis[2] - a*basis[1]);
		else
			Append(~zip,Z!(a mod 2^last_step));
			kern:=basis[2] + a*basis[1];
			// Append(~kernels,basis[2] + a*basis[1]);
		end if;
		// for j in [1..index_add] do
		// 	Remove(~isom_temp,1);
		// end for;
		Append(~walk,kernel_generator_to_isogeny_power(Project(kern),[<2,last_step>]));

		// Mt:=Montgomery(codomain(walk[#walk]),Fq!1);

	end if;

	return walk, <zip,swap>, last_step,len;
end function;

// zip is a compressed representation of the signature isogeny
//This function returns the codomain of the isogeny
decompress:=function(pk,zip,len,last_step)
	n:=32;
	Mt:=Montgomery(pk,Fq!1);
	for i in [1..len] do
		basis:=deterministic_two_basis(SemiMontgomery(Mt),n);
		basis:=[Mt!Lift(Normalized(b),Mt): b in basis];
		if zip[2][i] eq 1 then
			Reverse(~basis);
		end if;
		ker:=basis[2] + zip[1][i]*basis[1];
		phi:=kernel_generator_to_isogeny_power(Project(ker),[<2,n>]);
		Mt:=Montgomery(codomain(phi[#phi]),Fq!1);
	end for;
	if last_step ne 0 then
		basis:=deterministic_two_basis(SemiMontgomery(Mt),n);
		basis:=[2^(n-last_step)*bas: bas in basis];
		basis:=[Mt!Lift(Normalized(b),Mt): b in basis];
		if zip[2][#zip[2]] eq 1 then
			Reverse(~basis);
		end if;
		ker:=basis[2] + zip[1][#zip[1]]*basis[1];
		phi:=kernel_generator_to_isogeny_power(Project(ker),[<2,last_step>]);
		Mt:=codomain(phi[#phi]);
	end if;
	return Mt;
end function;

//verification function
verify:= function(commit,message,zip,pk,len,last_step)
	challenge:=gen_honest_challenge_verifier(commit,message);
	check:=decompress(pk,zip,len,last_step);
	return IsIsomorphic(check,challenge);
end function;

//takes the parameter generated as the key and perform a random signature
//no message for now, challenges are just random
//sign_odd_torsion determines if we want odd torsion in the signature
//for now we consider that 3 and 5 are acceptable
sqisign := function(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	// signing_odd_torsion:=3^53*5^21; //should not be bigger than p/N
	signing_odd_torsion:=1;

	message := [Random(1,2^32-1),Random(1,2^64-1) ];
		//generate  challenge + commitment
		t:=ClockCycles();
		commitment,phi_commit,phi_commit_dual,I_commit:=gen_commitment_odd();
		commit_time:=timediff(t);
		tt:=ClockCycles();
		phi_chall,chall,H_chall:=gen_honest_challenge_prover(phi_commit_dual,I_commit,message);
		challenge_time :=timediff(tt);

		//generate the signature ideal
		tt:=ClockCycles();
		equivalent_ideal:=small_equivalent_ideal(Conjugate(sk)*H_chall);
		_,alpha:=LeftIsomorphism(J,sk);
		sign_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,sk,2:addit_factor:=signing_odd_torsion);
		sign_ideal:=cyclic_ideal(sign_ideal:full:=true);
		klpt_time:=timediff(tt);
		sign_ideal:=sign_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
		sign_ideal:=rideal<LeftOrder(sign_ideal)|alpha>*sign_ideal;

		//computing the signature isogeny
		tt:=ClockCycles();
		sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_commit cat phi_chall,other_side_ideal:=H_chall);
		 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
		 translate_time:=timediff(tt);
		//normalizing and compressing
		walk, zip, last_step,len:=normalized_two_walk(sign_isogeny,sign_isom);
		sign_time:=timediff(t);




		//computing the verification
		tt:=ClockCycles();
		ver:=verify(commitment,message,zip,pk,len,last_step);
		assert(ver);
		if not ver then "problem with the verification"; end if;
		verif_time:=timediff(tt);

	return commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,Valuation(Z!Norm(sign_ideal),2);
end function;

//testing the above function
//test sqisign
Test_sqisign:=procedure()
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	epsilon:=14;
	number_batch:=1;
	number_round:=1;
	sign_times:=[];
	klpt_times:=[];
	commit_times:=[];
	challenge_times:=[];
	translate_times:=[];
	gen_times:=[];
	times_not_sorted:=[];
	sizes:=[];
	verif_times:=[];
	//generate the key

		"\n Test_sqisign \n number of batches:",number_batch," number of rounds:",number_round," \n";
	for index in [1..number_batch] do
		t:=ClockCycles();
		sk,pk,K,phi_K,isom_K,J,phi_J:=gen_keys();
		gen_time:=timediff(t);
		gen_times:=sort_insert(gen_times,gen_time);
		for ind in [1..number_round] do
			t:=ClockCycles();
			commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,size:=sqisign(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon);
			commit_times:=sort_insert(commit_times,commit_time);
			challenge_times:=sort_insert(challenge_times,challenge_time);
			klpt_times:=sort_insert(klpt_times,klpt_time);
			translate_times:=sort_insert(translate_times,translate_time);
			sign_times:=sort_insert(sign_times,sign_time);
			verif_times:=sort_insert(verif_times,verif_time);
			Append(~times_not_sorted,sign_time);
			Append(~sizes,size);
		end for;
	end for;



	"median generation time is ",gen_times[#gen_times div 2 +1];
	"median signing time for epsilon = ",epsilon," is ",sign_times[#sign_times div 2 +1];
	"median verification time is", verif_times[#verif_times div 2+1];
	"median commit time is", commit_times[#commit_times div 2+1];
	"median challenge time is", challenge_times[#challenge_times div 2+1];
	"median klpt time is", klpt_times[#klpt_times div 2+1];
	"median translate time is", translate_times[#translate_times div 2+1];

	gen_times;
	sign_times;
	verif_times;
	sizes;
end procedure;

//testing sqisign to find the best epsilon
Test_sqisign_epsilon :=procedure()
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;

	//generate the key
	t:=ClockCycles();
	sk,K,phi_K,isom_K,J,phi_J:=gen_keys();
	pk:=codomain(phi_K[#phi_K]);
	"key generated in ",timediff(t)," s";
	"";
	number_round:=5;
	epsilons:=[10,12,13,14,16];
	epsilon_times:=[ [] : eps in [1..#epsilons]];
	for round in [1..number_round] do
		signing_odd_torsion:=3^53*5^21;
		commitment,phi_commit,phi_commit_dual,I_commit:=gen_commitment_odd();
		phi_chall,chall,H_chall:=gen_challenge_odd(phi_commit_dual,I_commit);
		//generate the signature ideal
		equivalent_ideal:=small_equivalent_ideal(Conjugate(sk)*H_chall);
		_,alpha:=LeftIsomorphism(J,sk);
		// t:=ClockCycles();
		sign_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,sk,2:addit_factor:=signing_odd_torsion);
		sign_ideal:=cyclic_ideal(sign_ideal:full:=true);
		Factorization(Z!Norm(sign_ideal));

		sign_ideal:=sign_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
		sign_ideal:=rideal<LeftOrder(sign_ideal)|alpha>*sign_ideal;
		for eps in [1..#epsilons] do
			epsilon:=epsilons[eps];
			t:=ClockCycles();
			sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_commit cat phi_chall,other_side_ideal:=H_chall);
			 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
			sign_time:=timediff(t);
			epsilon_times[eps]:=sort_insert(epsilon_times[eps],sign_time);
		end for;
	end for;
	for eps in [1..#epsilons] do
		"for epsilon = ", epsilons[eps], " median time is ",epsilon_times[eps][Floor(number_round/ 2) +1],"total times  :",epsilon_times[eps];
	end for;

	// "Is it correct ?",IsIsomorphic(codomain(sign_isogeny[#sign_isogeny]),chall);
end procedure;





Test_sqisign();
