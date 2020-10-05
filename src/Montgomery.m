/*
 * Semi-Montgomery curves are curves of the form
 *
 *    y² = x (x - α) (x - 1/α) = x³ - (α + 1/α) x² + x
 *
 * This is a special case of Montgomery curves. Several
 * isogeny-related operations are easier on Semi-Montgomery curves.
 */


/******** Montgomery curves**************/
declare type Mnty[MntyPt];
declare attributes Mnty: alpha,A,B,A24;
declare attributes MntyPt: x,y,z,curve;

intrinsic Montgomery(alpha::FldFinElt,B::FldFinElt) -> Mnty
	{Create By² = x (x - α) (x - 1/α)}
	assert alpha ne 0;
	assert B ne 0;
	assert (alpha+1)^4 ne 4;
	M := New(Mnty);
	M`alpha := alpha;
	M`A := - M`alpha - 1/M`alpha;
	M`B:=B;
	M`A24 := (M`A + 2) / 4;
	return M;
end intrinsic;

intrinsic Montgomery(M::SmiMnty,Mref::Mnty) -> Mnty
	{convert the SmiMntyto a Mnty, with the twister of Mref}
	return Montgomery(RecoverAlpha(M)`alpha,Mref`B);
end intrinsic;

intrinsic Montgomery(M::SmiMnty,B::FldFinElt) -> Mnty
	{construct the curve from M and with twisting parameter B}
	if M`alpha ne 0 then
		return Montgomery(M`alpha,B);
	else
		return MontgomeryA(M`A,B);
	end if;
end intrinsic;

intrinsic Montgomery(M::Mnty,B::FldFinElt) -> Mnty
	{return M}
	return M;
end intrinsic;

intrinsic Montgomery(M::SmiMnty,P::SmiMntyXZ,twister::FldFinElt) -> Mnty
	{construct the curve from M on which P using potentially twister as twisting parameter}
	if IsOnCurve(P) then
		return Montgomery(P`curve,Parent(P`X)!1);
	end if;
	return Montgomery(P`curve,twister);
end intrinsic;

intrinsic MontgomeryA(A::FldFinElt,B::FldFinElt) -> Mnty
	{Compute the montgomery curve from A, alpha is set to zero in this case}
	M:=New(Mnty);
	M`A:=A;
	M`alpha:=Parent(A)!0;
	M`B:=B;
	M`A24:=(A+2)/4;
	return M;
end intrinsic;

intrinsic QuadraticTwist(M::Mnty,twister::FldFinElt) -> Mnty
 {construct the quadratic twist of M}
	F:=Parent(M`B);
 	if M`B eq 1 then
	 	return MontgomeryA(M`A,twister);
 	else
	 	return MontgomeryA(M`A,F!1);
 	end if;
end intrinsic;

intrinsic Print(M::Mnty)
	{Print M}
	printf "%o y² = x³ + %o x² + x",M`B, M`A;
end intrinsic;

intrinsic jInvariant(M::Mnty) -> FldFinElt
	{The j-invariant of M}
	A2 := M`A^2;
	return 256 * (A2 - 3)^3 / (A2 - 4);
end intrinsic;

intrinsic IsIsomorphic(M1::Mnty,M2::Mnty) -> BoolElt
	{assert if the two curves are isomorphic}
	return jInvariant(M1) eq jInvariant(M2);
end intrinsic;

intrinsic EllipticCurve(M::Mnty) -> CrvEll
	{Magma's native elliptic curve object from this curve}
	// require M`B eq 1: "the curve has a non-trivial twisting factor";
	k := Parent(M`A);
	return EllipticCurve([k!0, M`A, k!0, k!1, k!0]);
end intrinsic;

intrinsic Isomorphism(M1::Mnty,M2::Mnty) -> func
	{compute the isomorphism between the two curves, the output is [r,s,t,u]}
	E1:=EllipticCurve(M1);
	E2:=EllipticCurve(M2);
	phi:=Isomorphism(E1,E2);
	return IsomorphismData(phi);
end intrinsic;

intrinsic ApplyIsom(isom::[FldFinElt],M::Mnty,P::MntyPt) -> MntyPt
 {apply isom = [r,s,t,u] on the point P}
 r:=isom[1];
 s:=isom[2];
 t:=isom[3];
 u:=isom[4];
 Q:=MontgomeryPt(P`x*u^2 + P`z*r,u^3*P`y+s*P`x*u^2+t*P`z,P`z,M);
 return Q;
end intrinsic;
intrinsic ApplyIsom(isom::[FldFinElt],M::Mnty,P::SmiMntyXZ) -> SmiMntyXZ
 {apply isom = [r,s,t,u] on the point P}
 r:=isom[1];
 s:=isom[2];
 t:=isom[3];
 u:=isom[4];
 Q:=SemiMontgomeryXZ(P`X*u^2 + P`Z*r,P`Z,SemiMontgomery(M));
 return Q;
end intrinsic;
intrinsic ApplyIsom(isom::[FldFinElt],M::SmiMnty,P::SmiMntyXZ) -> SmiMntyXZ
 {apply isom = [r,s,t,u] on the point P}
 r:=isom[1];
 s:=isom[2];
 t:=isom[3];
 u:=isom[4];
 Q:=SemiMontgomeryXZ(P`X*u^2 + P`Z*r,P`Z,M);
 return Q;
end intrinsic;

intrinsic WeierstrassForm(P::MntyPt) -> PtEll
	{Convert a point P to its equivalent on E the weierstrass curve equivalent to the curve of P}
	M:=P`curve;
	P:=Normalized(P);
	F:=Parent(P`x);
	_<x>:=PolynomialRing(F);
	t1:=M`B^2;
	t2:=M`A/3;
	c1:=t1*(1-M`A*t2);c2:=M`B*t1*(t2)*(2*t2^2-1);
	E:=EllipticCurve(x^3+c1*x+c2);
	return elt<E|M`B*(P`x+M`A/3),M`B^2*P`y,F!1>;
end intrinsic;

intrinsic MontgomeryPt(M::Mnty,P::PtEll) -> MntyPt
	{Convert back P to the montgomery point}
	F:=Parent(P[1]);
	return MontgomeryPt(P[1]/M`B-M`A/3,P[2]/M`B^2,F!1,M);
end intrinsic;

/****************************************/

/******** Semi-Montgomery curves ********/
declare type SmiMnty[SmiMntyXZ];
declare attributes SmiMnty: alpha,A,A24;
declare attributes SmiMntyXZ: X, Z, curve;


intrinsic SemiMontgomery(alpha::FldFinElt) -> SmiMnty
	{Create y² = x (x - α) (x - 1/α)}
	// require alpha ne 0: "Undefined curve";
	// require (alpha+1)^4 ne 4: "Curve is singular";
	M := New(SmiMnty);
	M`alpha := alpha;
	M`A := - M`alpha - 1/M`alpha;
	M`A24 := (M`A + 2) / 4;
	return M;
end intrinsic;

intrinsic SemiMontgomery(M::SmiMnty) -> SmiMnty
	{return M}
	return M;
end intrinsic;

intrinsic SemiMontgomeryA(A::FldFinElt) -> SmiMnty
	{compute the montgomery curve By² =x(x²+Ax+1) without computing alpha, this is to avoid computing unnecessary square roots during two isogenies }
	M := New(SmiMnty);
	F:=Parent(A);
	M`alpha := F!0;
	M`A := A;
	M`A24 := (M`A + 2) / 4;
	return M;
end intrinsic;

intrinsic SemiMontgomery(M::Mnty) -> SmiMnty
	{Return the semi-montgomery curve associated with M}
	SM:=New(SmiMnty);
	SM`alpha:=M`alpha;
	SM`A:=M`A;
	SM`A24:=M`A24;
	return SM;
end intrinsic;

intrinsic RecoverAlpha(M::SmiMnty) -> SmiMnty
	{Recover the coefficient alpha when it is set to 0}
	if M`alpha ne 0 then
		return M;
	end if;

	_<x>:=PolynomialRing(Parent(M`A));
	alpha:=Roots(x^2+M`A*x+1)[1][1];

	return RecoverAlpha(M,alpha);
end intrinsic;

intrinsic RecoverAlpha(M::SmiMnty,alpha::FldFinElt) -> SmiMnty
	{add the knowledge of alpha to the curve}
	Mt:=New(SmiMnty);
	Mt`alpha:=alpha;
	Mt`A:=M`A;
	Mt`A24:=M`A24;
	return Mt;
end intrinsic;

intrinsic RecoverAlphaSpecialCase(A1::FldFinElt,A2::FldFinElt) -> SmiMnty
	{this is when A2 is computed from A1 as the arrival curve of the isogeny of kernel (0:1), the formula allows efficient computation of alpha}
	M:=New(SmiMnty);
	M`A:=A2;
	M`A24:=(M`A + 2) / 4;
	M`alpha:=-( (2+A1)*A2)/(2*A1);
	return M;
end intrinsic;

intrinsic Print(M::SmiMnty)
	{Print M}
	printf " y²  = x³ + %o x² + x", M`A;
end intrinsic;

intrinsic MontgomeryA(M::SmiMnty) -> FldFinElt
	{The Montgomery A coefficient}
	return M`A;
end intrinsic;

intrinsic jInvariant(M::SmiMnty) -> FldFinElt
	{The j-invariant of M}
	A2 := M`A^2;
	return 256 * (A2 - 3)^3 / (A2 - 4);
end intrinsic;

intrinsic IsIsomorphic(M1::SmiMnty,M2::SmiMnty) -> BoolElt
	{assert if the two curves are isomorphic}
	return jInvariant(M1) eq jInvariant(M2);
end intrinsic;

intrinsic EllipticCurve(M:SmiMnty) -> CrvEll
	{Magma's native elliptic curve object from this curve}
	k := Parent(M`A);
	return EllipticCurve([k!0, M`A, k!0, k!1, k!0]);
end intrinsic;

intrinsic Isomorphism(M1::SmiMnty,M2::SmiMnty) -> func
	{compute the isomorphism between the two curves, the output is [r,s,t,u]}
	E1:=EllipticCurve(M1);
	E2:=EllipticCurve(M2);
	phi:=Isomorphism(E1,E2);
	return IsomorphismData(phi);
end intrinsic;

/******** Semi-Montgomery XZ points ********/
intrinsic SemiMontgomeryXZ(X::FldFinElt, Z::FldFinElt, M::SmiMnty) -> SmiMntyXZ
	{Create point on curve}
	// require Z ne 0 or X eq 0: X,Z,"(*:0) point not valid when * is not 0";
	P := New(SmiMntyXZ);
	P`X := X;
	P`Z := Z;
	P`curve := M;
	return P;
end intrinsic;

intrinsic Parent(P::SmiMntyXZ) -> SmiMnty
	{Return parent curve}
	return P`curve;
end intrinsic;

intrinsic Print(P::SmiMntyXZ)
	{Print point}
	printf "(%o:%o)", P`X, P`Z;
end intrinsic;

intrinsic IsIdentity(P::SmiMntyXZ) -> BoolElt
	{says if the point is the identity}
	return P`Z eq 0;
end intrinsic;

intrinsic Curve(P::SmiMntyXZ) -> SmiMnty
	{return the curve of P}
	return P`curve;
end intrinsic;

intrinsic 'eq'(P::SmiMntyXZ, Q::SmiMntyXZ) -> BoolElt
	{Test equality of points}
	// if P`X eq 0 and P`Z eq 0 then
	// 	return Q`Z eq 0 and Q`X eq 0;
	// elif Q`Z eq 0 and Q`X eq 0 then
	// 	return P`X eq 0 and P`Z eq 0;
	// end if;
	return P`X * Q`Z eq P`Z * Q`X;
end intrinsic;

intrinsic IsOnCurve(P::SmiMntyXZ) -> BoolElt
	{Test whether point is on curve}
	if IsZero(P`X) then return true; end if;
	return not not IsSquare((P`X^3+P`curve`A*P`X^2*P`Z+P`X*P`Z^2)*P`Z);
end intrinsic;

intrinsic IsOnTwist(P::SmiMntyXZ) -> BoolElt
	{Test whether point is on quadratic twist}
	return not IsOnCurve(P);
end intrinsic;

intrinsic ZeroXZ(M::SmiMnty) -> SmiMntyXZ
	{Point at infinity}
	k := Parent(M`alpha);
	return SemiMontgomeryXZ(k!1, k!0, M);
end intrinsic;

intrinsic IsCoercible(M::SmiMnty, x::.) -> BoolElt, .
	{Point of coordinates (x:1)}
	k := Parent(M`alpha);
	isc, X := IsCoercible(k, x);
	if isc then
		return true, SemiMontgomeryXZ(X, k!1, M);
	else
		return false;
	end if;
end intrinsic;

intrinsic IsCoercible(M::SmiMnty,P::SmiMntyXZ) -> BoolElt,.
	{Point of coordinates (x:1)}
	k := Parent(M`A);
	isc1, x := IsCoercible(k, P`X);
	isc2,z:=IsCoercible(k,P`Z);
	if isc1 and isc2 then
		return true, SemiMontgomeryXZ(x,z, M);
	else
		return false;
	end if;
end intrinsic;

intrinsic RandomXZ(M::SmiMnty, oncurve::BoolElt) -> SmiMntyXZ
	{Random non-zero point on M if oncurve == true, on the twist otherwise}
	repeat
		P := RandomXZ(M);
	until IsOnCurve(P) eq oncurve;
	return P;
end intrinsic;

intrinsic Random(M::SmiMnty) -> SmiMntyXZ
	{random non-zero point on M}
	return RandomXZ(M,true);
end intrinsic;

intrinsic RandomXZ(M::SmiMnty) -> SmiMntyXZ
	{Random non-zero point on M (or the twist)}
	k := Parent(M`alpha);

	return SemiMontgomeryXZ(Random(k), k!1, M);
end intrinsic;

intrinsic Normalized(P::SmiMntyXZ) -> SmiMntyXZ
	{Return normalized (X:1) copy of point}
	if P`Z eq 0 then
		return ZeroXZ(P`curve);
	else
		k := Parent(P`X);
		return SemiMontgomeryXZ(P`X / P`Z, k!1, P`curve);
	end if;
end intrinsic;

intrinsic Lift(P::SmiMntyXZ,M::Mnty) -> MntyPt
	{Lift the point in X,Z coordinates to the full x:y:z coordinates}
	// "Lifting points !";
	// "Lifting Point !";
	k:=Parent(P`X);
	if IsIdentity(P) then
		 return ZeroPt(M);
	end if;
	x:=P`X;
	z:=P`Z;
	y:=Sqrt((x^3+M`A*x^2*z+x*z^2)/(M`B*z));
	return MontgomeryPt(x,y,z,M);
end intrinsic;

intrinsic Lift(P::SmiMntyXZ,twister:FldFinElt) -> MntyPt
	{Lift the point P as a MntyPt on P`curve or its twist, the twisting param is twister}
	if IsOnCurve(P) then
		return Lift(P,Montgomery(P`curve,Parent(P`X)!1));
	else
		return Lift(P,Montgomery(P`curve,twister));
	end if;
end intrinsic;

intrinsic Lift(P::SmiMntyXZ, E::CrvEll) -> PtEll
	{The two points (X:Y:1) in E above P}
	return Points(E, P`X / P`Z);
end intrinsic;


////// Arithmetic

intrinsic Double(P::SmiMntyXZ) -> SmiMntyXZ
	{Double point}
	tmp1 := (P`X + P`Z)^2;
	tmp2 := (P`X - P`Z)^2;
	tmp3 := tmp1 - tmp2;
	tmp4 := P`curve`A24 * tmp3 + tmp2;
	return SemiMontgomeryXZ(tmp1 * tmp2, tmp3 * tmp4, P`curve);
end intrinsic;

intrinsic XAdd(P::SmiMntyXZ, Q::SmiMntyXZ, PQ::SmiMntyXZ) -> SmiMntyXZ
	{Differential addition P + Q}
	// if P eq ZeroXZ(P`curve) then
	// 	return Q;
	// elif Q eq ZeroXZ(P`curve) then
	// 	return P;
	// end if;
	if IsIdentity(PQ) then
		return Double(P);
	end if;
	tmp1 := (P`X + P`Z) * (Q`X - Q`Z);
	tmp2 := (P`X - P`Z) * (Q`X + Q`Z);
	return SemiMontgomeryXZ(PQ`Z * (tmp1 + tmp2)^2, PQ`X * (tmp1 - tmp2)^2, P`curve);
end intrinsic;

intrinsic '*'(n::RngIntElt, P::SmiMntyXZ) -> SmiMntyXZ
	{Montgomery ladder}
	if n eq 0 then return ZeroXZ(P`curve); end if;
	if n le 0 then n := -n; end if;
	if n eq 1 then return P; end if;
	Q := P;
	R := Double(P);
	i := ShiftLeft(1, Ilog2(n) - 1);
	while i ge 1 do
		if BitwiseAnd(n, i) ne 0 then
			Q := XAdd(Q, R, P);
			R := Double(R);
		else
			R := XAdd(Q, R, P);
			Q := Double(Q);
		end if;
		i := ShiftRight(i, 1);
	end while;
	return Q;
end intrinsic;
intrinsic '*'(P::SmiMntyXZ,n::RngIntElt) -> SmiMntyXZ
	{Montgomery ladder}
	return n*P;
end intrinsic;

intrinsic Ladder(n::RngIntElt, P::SmiMntyXZ) -> SmiMntyXZ,SmiMntyXZ
	{Montgomery ladder with both point in output}
	if n eq 0 then return ZeroXZ(P`curve); end if;
	if n le 0 then n := -n; end if;
	Q := P;
	R := Double(P);
	i := ShiftLeft(1, Ilog2(n) - 1);
	while i ge 1 do
		if BitwiseAnd(n, i) ne 0 then
			Q := XAdd(Q, R, P);
			R := Double(R);
		else
			R := XAdd(Q, R, P);
			Q := Double(Q);
		end if;
		i := ShiftRight(i, 1);
	end while;
	return Q,R;
end intrinsic;



/***** Montgomery Points ************/
intrinsic MontgomeryPt(x::FldFinElt,y::FldFinElt,z::FldFinElt,M::Mnty) -> MntyPt
	{create a point on M}
	assert (z ne 0 and M`B*y^2*z eq x^3 + M`A*z*x^2 + z^2*x) or ( z eq 0 and (x eq 0 and y eq 1));
	P:=New(MntyPt);
	P`x:=x;
	P`y:=y;
	P`z:=z;
	P`curve:=M;
	return P;
end intrinsic;

intrinsic Parent(P::MntyPt) -> Mnty
	{return the parent of the point}
	return P`curve;
end intrinsic;

intrinsic Print(P::MntyPt)
	{Print point}
	printf "(%o:%o:%o)", P`x,P`y, P`z;
end intrinsic;

intrinsic IsOnCurve(P::MntyPt) -> BoolElt
  {confirm that the point is indeed on its curve}
	M:=P`curve;
	return M`B*P`z*P`y^2 eq P`x^3 + M`A*P`z*P`x^2 + P`z^2*P`x;
end intrinsic;

intrinsic IsOnCurve(P::MntyPt,M::Mnty) -> BoolElt
  {confirm that the point is on the given curve M}
	return M`B*P`z*P`y^2 eq P`x^3 + M`A*P`z*P`x^2 + P`z^2*P`x;
end intrinsic;


intrinsic IsIdentity(P::MntyPt) -> BoolElt
	{says if the point is the identity}
	return P eq ZeroPt(P`curve);
end intrinsic;

intrinsic Curve(P::MntyPt) -> Mnty
	{return the curve of P}
	return P`curve;
end intrinsic;

intrinsic 'eq'(P::MntyPt, Q::MntyPt) -> BoolElt
	{Test equality of points}
	return P`x * Q`z eq P`z * Q`x and P`y * Q`z eq P`z * Q`y;
end intrinsic;

intrinsic Normalized(P::MntyPt) -> MntyPt
	{Return normalized (x:y:1) copy of point}
	if P`z eq 0 then
		return ZeroPt(P`curve);
	else
		k := Parent(P`x);
		return MontgomeryPt(P`x / P`z,P`y/P`z, k!1, P`curve);
	end if;
end intrinsic;

intrinsic ZeroPt(M::Mnty) -> MntyPt
	{Point at infinity}
	k := Parent(M`alpha);
	return MontgomeryPt(k!0,k!1, k!0, M);
end intrinsic;

intrinsic IsCoercible(M::Mnty, x::.,y::.) -> BoolElt, .
	{Point of coordinates (x:y:1)}
	k := Parent(M`alpha);
	isc, X := IsCoercible(k, x);
	isc2,Y:=IsCoercible(k,y);
	if isc and isc2 then
		return true, MontgomeryPt(X,Y,k!1, M);
	else
		return false;
	end if;
end intrinsic;

intrinsic IsCoercible(M::Mnty, P::MntyPt) -> BoolElt, .
	{Coerce P in M}
	k := Parent(M`alpha);
	isc, X := IsCoercible(k,P`x);
	isc2,Y:=IsCoercible(k,P`y);
	isc3,Z:=IsCoercible(k,P`z);
	if isc and isc2 and isc3 then
		return true, MontgomeryPt(X,Y,Z, M);
	else
		return false;
	end if;
end intrinsic;

intrinsic IsTwistPoint(P::MntyPt) -> BoolElt
	{check if the point is on the twist of the curve}
	return not P`curve`B eq 1;
end intrinsic;

intrinsic Project(P::MntyPt) -> SmiMntyXZ
	{return the projection of P on (X:Z) on the SmiMnty curve obtained from the curve of P}
	return SemiMontgomeryXZ(P`x,P`z,SemiMontgomery(P`curve));
end intrinsic;
intrinsic Project(P::SmiMntyXZ) -> SmiMntyXZ
	{return P}
	return P;
end intrinsic;

intrinsic Recover(P::MntyPt,Q::SmiMntyXZ,QP::SmiMntyXZ) -> MntyPt
	{recover the full coordinates of Q given information on the P+Q for some P}
	M:=P`curve;
	if Q eq ZeroXZ(Q`curve) then return ZeroPt(M); end if;
	if Project(P) eq Q then
		if QP eq ZeroXZ(Q`curve) then
			return -P;
		else
			return P;
		end if;
	end if;
	v1:=P`x*Q`Z;
	v2:=Q`X*P`z+v1;
	v3:=Q`X*P`z-v1;
	v3:=v3^2;
	v3*:=QP`X;
	v1:=2*M`A*Q`Z*P`z;
	v2:=v2+v1;
	v4:=P`x*Q`X;
	v4+:=Q`Z*P`z;
	v2*:=v4;
	v1*:=Q`Z*P`z;
	v2:=v2-v1;
	v2*:=QP`Z;
	y:=v2-v3;
	v1:=2*M`B*P`y;
	v1*:=Q`Z*QP`Z*P`z;
	x:=v1*Q`X;
	z:=v1*Q`Z;
	return MontgomeryPt(x,y,z,M);
end intrinsic;

intrinsic RandomPt(M::Mnty) -> MntyPt
	{Random non-zero point on M}
	// "rando";
	F:=Parent(M`A);
	if M`B eq F!1 then
		P := RandomXZ(SemiMontgomery(M),true);
		return Lift(P,M);
	else
		P := RandomXZ(SemiMontgomery(M),false);
		return Lift(P,M);
	end if;
end intrinsic;

intrinsic Random(M::Mnty) -> MntyPt
	{random non-zero point on M}
	return RandomPt(M);
end intrinsic;

intrinsic Lift(P::MntyPt,twister:FldFinElt) -> MntyPt
	{return P}
	return P;
end intrinsic;

intrinsic '-'(P::MntyPt) -> MntyPt
	{return -P}
	if IsIdentity(P) then return P; end if;
	// IsOnCurve(P);
	return MontgomeryPt(P`x,-P`y,P`z,P`curve);
end intrinsic;

intrinsic '+'(P::MntyPt,Q::MntyPt) -> MntyPt
 {point addition}
	M:=P`curve;
	if IsIdentity(P) then return Q; end if;
	if IsIdentity(Q) then return P; end if;
	k:=Parent(P`x);
	lambda:=k!1;
	if P eq (-Q) then return ZeroPt(P`curve); end if;
	if P eq Q then
		lambda:=(3*P`x^2+ 2*M`A*P`x*P`z+P`z^2)/(2*M`B*P`y*P`z);
	else
		lambda:=(Q`y*P`z-P`y*Q`z)/(Q`x*P`z-P`x*Q`z);
	end if;
	zplus:=Q`z*P`z;
	xplus:=(M`B*lambda^2-M`A)*zplus - (P`x*Q`z+Q`x*P`z);
	yplus:=lambda*(P`x*Q`z - xplus) - Q`z*P`y;
	return MontgomeryPt(xplus,yplus,zplus,M);
end intrinsic;
intrinsic '-'(P::MntyPt,Q::MntyPt) -> MntyPt
	{return P-Q}
	return P + (-Q);
end intrinsic;

intrinsic '*'(n::RngIntElt,P::MntyPt) -> MntyPt
	{return n*P}
	if n eq 0 then return ZeroPt(P`curve); end if;
	if n eq -1 then return -P; end if;
	if n eq 1 then return P; end if;
	sign:=1;
	if n lt 0 then n:=-n;sign:=-1; end if;
	xP:=Project(P);
	xQ,xPQ:=Ladder(n,xP);
	if sign eq 1 then
		return Recover(P,xQ,xPQ);
	else
		return -Recover(P,xQ,xPQ);
	end if;
end intrinsic;
intrinsic '*'(P::MntyPt,n::RngIntElt) -> MntyPt
	{return n*P}
	return n*P;
end intrinsic;


// compute the discrete logarithm of Q in base P, given that P is of order l
// returns -1 if DLP does not exist
discrete_logarithm_BSGS:=function(Q,P,l);
  m := Ceiling(Sqrt(l));
    table := AssociativeArray();
    e := ZeroPt(Parent(P));
    for i in [0..m-1] do
        table[e] := i;
        e := e + P;
    end for;
    step := (-m)*P;
    e := Q;
    for i in [0..m-1] do
        if IsDefined(table,e) then
            return i*m + table[e];
        end if;
        e := e + step;
    end for;
    "ERROR in discrete_logarithm_BSGS: logarithm does not exist";
    return -1;
end function;
// compute the discrete logarithm of Q in base P, given that P is of order l^n
// returns -1 if DLP does not exist
discrete_logarithm_power:=function(Q,P,l,n);
  log := 0;
  Ps := [ZeroPt(Parent(P)) : i in [1..n]];
  Ps[1] := P;
  for i in [2..n] do
    Ps[i] := l*Ps[i-1];
  end for;

  h := Q;
  for i in [0..n-1] do
    hi := (l^(n-1-i))*h;
    ai := discrete_logarithm_BSGS(hi,Ps[n],l);
    if ai eq -1 then return -1; end if;
    log +:= (l^i)*ai;
    h := h - ai*Ps[i+1];
  end for;
  return log;
end function;

//the following functions uses magma Elliptic Curves functions

intrinsic IsLinearlyIndependent(P::MntyPt,Q::MntyPt,ln::RngIntElt) -> BoolElt
	{return true if P and Q of ln torsion are linearly independant}
	P1:=WeierstrassForm(P);
	P2:=Curve(P1)!WeierstrassForm(Q);
	return IsLinearlyIndependent(P1,P2,ln);
end intrinsic;

intrinsic DivisionPoint(P::MntyPt,n::RngIntElt) -> MntyPt
	{compute one division point Q of P such that P = n*Q}
 R:=WeierstrassForm(P);
 return MontgomeryPt(P`curve,DivisionPoints(R,n)[1]);
end intrinsic;

intrinsic DivisionPoints(P::MntyPt,n::RngIntElt) -> MntyPt
	{compute one division point Q of P such that P = n*Q}
 R:=WeierstrassForm(P);
 return [MontgomeryPt(P`curve,divis):divis in DivisionPoints(R,n)] ;
end intrinsic;

intrinsic WeilPairing(P::MntyPt,Q::MntyPt,l::RngIntElt) -> FldFinElt
	{compute the weil pairing of P,Q points of l torsion}
	P1:=WeierstrassForm(P);
	P2:=Curve(P1)!WeierstrassForm(Q);
	return WeilPairing(P1,P2,l);
end intrinsic

intrinsic Log(P::MntyPt,Q::MntyPt) -> RngIntElt
	{use magma type to compute DLP}
	R1:=WeierstrassForm(P);
	R2:=WeierstrassForm(Q);
	return Log(Q,P);
end intrinsic;
