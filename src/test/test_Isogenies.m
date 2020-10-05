/* Test SemiMontgomery curves */

// Define y² = x³ + x / GF(103)
repeat
	cofactor:=Random(1,2^100);
	p:=4*cofactor*13-1;
until IsPrime(p);
"the prime: ",p;
k<i> := ExtensionField<GF(p), i | i^2+1>;
M := SemiMontgomery(i);
cofactor*:=4;


/* Testing compatibility with group law */
repeat
	P := cofactor * RandomXZ(M, true);
until not IsIdentity(P);
Q := RandomXZ(M);
Phi1:=SmallIsogeny(P,13);
Rs := Evaluate(Phi1, [Q,3*Q,11*Q]);
P1:=Rs[1];
assert Rs[2] eq 3*Rs[1];
assert Rs[3] eq 11*Rs[1];
Phi2:=BigIsogeny(P,13);
Rs := Evaluate(Phi2, [Q,3*Q,11*Q]);
assert jInvariant(Phi2`codomain) eq jInvariant(Phi1`codomain);
assert Rs[2] eq 3*Rs[1];
assert Rs[3] eq 11*Rs[1];
P2:=Rs[1];
assert P1 eq P2;
/* Testing correctness by sending a point through phi and using it to compute the dual*/
repeat
	R:=cofactor*RandomXZ(M,true);
	// R;
	// P:=Lift(P,k!1);
	// R:=Lift(R,k!1);
	// IsLinearlyIndependent(R,P,13);
	PhiR:=Evaluate(Phi1,[R])[1];
until not IsIdentity(R) and not IsIdentity(PhiR);
Phi3:=SmallIsogeny(PhiR,13);
assert jInvariant(Phi3`codomain) eq jInvariant(M);
repeat
	R:=cofactor*RandomXZ(M,true);
	PhiR:=Evaluate(Phi2,[R])[1];
until not IsIdentity(R) and not IsIdentity(PhiR);
Phi4:=BigIsogeny(PhiR,13);
assert jInvariant(Phi4`codomain) eq jInvariant(M);

print "All tests passed";
