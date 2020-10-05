


//verify that the given curve is supersingular by looking at correct torsion points
 IsSupersingular:=function(M)
   p:=73743043621499797449074820543863456997944695372324032511999999999999999999999;
   n:=33;
   number:=100;
   cofactor:=(p+1 ) div 2^n;
   for i in [1..number] do
     P:=RandomXZ(M,true);
     P:=P*cofactor;
     if IsIdentity(2^n*P) and not IsIdentity(2^(n-1)*P) then return true; end if;
   end for;
   return false;
 end function;

//test the isogeny by computing several evaluations and verify that they are correct
 TestIsogeny:=procedure(iso)
   "entering the isogeny test";
   p:=73743043621499797449074820543863456997944695372324032511999999999999999999999;
   n:=33;
   cofactor:=(p+1 ) div 2^n;
   F:=Parent(iso`domain`A);
   if IsIsomorphic(iso`domain,iso`codomain) then
     "the codomain and the domain are the same for",iso;
   end if;
   b1:=IsSupersingular(SemiMontgomery(iso`codomain));
   if not b1 then
     "the codomain is not supersingular for",iso;
   end if;
   M:=Montgomery(iso`domain,F!1);
   SM:=SemiMontgomery(M);
   P1:=RandomPt(M)*cofactor*2^17;
   if not IsIdentity(2^16*P1) then "point is not of the supposed order"; end if;
   P2:=RandomPt(M)*cofactor*2^17;
   rando:=[1,1,Random(1,1000)];
   // rando:=[Random(1,2^200): i in [1..2]];
   points:=[SM!Project(P1),SM!Project(P2),SM!Project(rando[1]*P1+rando[2]*P2),SM!Project(rando[3]*P1) ];
   ev:=Evaluate(iso,points);

   Mt:=Montgomery(RecoverAlpha(iso`codomain)`alpha,P1`curve`B);
   // Mt;
   // ev[1]`curve;
   ev:=[Mt!Lift(P,Mt): P in ev];
   b2:=ev[3] eq ev[1]+ev[2] or ev[3] eq ev[1]-ev[2] or ev[3] eq ev[2]-ev[1] or ev[3] eq -ev[2]-ev[1];
   Q:=rando[3]*ev[1];
   b3:=ev[4] eq Q or ev[4] eq -Q;
   if not b2 then "addition through eval is wrong for",iso; end if;
   if not b3 then "multiplication through eval is wrong for",iso; end if;
   // if b1 and b2 then "isogeny is fine",iso; end if;
 end procedure;


 /*
  * Generic type of Isogenies
  *
  * isogeny contains either TwoIsog, OddBigIsog or OddSmallIsog

  */


declare type Isog;
declare attributes Isog: domain,codomain,degree,isogeny;

intrinsic Isogeny(ker::SmiMntyXZ, ell::RngIntElt,deg_bound::RngIntElt) -> Isog
  {generate a generic object isogeny, its concrete type will depend on the degree}
  Phi:=New(Isog);
  Phi`degree:=ell;
  if ell eq 2 then
    iso:=TwoIsogeny(ker);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
    Phi`domain:=iso`domain;
  elif ell le deg_bound then
    iso:=SmallIsogeny(ker,ell);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
    Phi`domain:=iso`domain;
  else
    iso:=BigIsogeny(ker,ell);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
    Phi`domain:=iso`domain;
  end if;
  return Phi;
end intrinsic;

intrinsic Isogeny(ker::MntyPt, ell::RngIntElt,deg_bound::RngIntElt) -> Isog
  {generate a generic object isogeny, its concrete type will depend on the degree}
  // require IsIdentity(ell*ker) and not IsIdentity((ell-1)*ker): "incorrect kernel";
  M:=ker`curve;
  Phi:=New(Isog);
  Phi`degree:=ell;
  ker:=Project(ker);
  M:=ker`curve;
  Phi`domain:=M;
  if ell eq 2 then
    iso:=TwoIsogeny(ker);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
  elif ell le deg_bound then
    iso:=SmallIsogeny(ker,ell);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
  else
    iso:=BigIsogeny(ker,ell);
    Phi`codomain:=iso`codomain;
    Phi`isogeny:=iso;
  end if;
  return Phi;
end intrinsic;

intrinsic Evaluate(iso::Isog,points::[SmiMntyXZ]) -> SeqEnum
  {Evaluate the isogeny on points}
  return Evaluate(iso`isogeny,points);
end intrinsic;

intrinsic Evaluate(iso::Isog,points::[MntyPt]) -> SeqEnum
  {evaluate on iso on points }
  "slow evaluation !";

  if points eq [] then
    return [];
  end if;
  for P in points do
    if not IsOnCurve(P,Montgomery(RecoverAlpha(iso`domain),P`curve`B)) then "point not on curve !"; end if;
  end for;
  if iso`degree eq 2 then

    Q := iso`isogeny`kernel;
    F:=Parent(Q`X);
    //check if the isogeny is the endomorphism 1+i on y² = x³ + x
    if Q eq SemiMontgomeryXZ(F!0,F!1,Parent(Q)) and jInvariant(iso`domain) eq 1728 then
      "endo i computation";
      sq:=Sqrt(F!(-1));
      Rs:=[MontgomeryPt(-point`x,sq*point`y,point`z,point`curve)+point: point in points];
      return Rs;
    end if;
  end if;
  ev:=  Evaluate(iso`isogeny,[SemiMontgomery(iso`domain)!Project(point): point in points]);
  M:=Montgomery(RecoverAlpha(iso`codomain)`alpha,points[1]`curve`B);
  return [M!Lift(P,M): P in ev];
end intrinsic;

intrinsic DualIsogeny(iso::Isog) -> Isog
  {return the Dual Isogeny}
  return DualIsogeny(iso`isogeny);
end intrinsic;

intrinsic codomain(iso::Isog) -> SmiMnty
  {return the codomain}
  return iso`codomain;
end intrinsic;

intrinsic domain(iso::Isog) -> SmiMnty
  {return the domain}
  return iso`domain;
end intrinsic;

intrinsic Print(iso::Isog)
  {print iso}
  print "isogeny from ",iso`domain," to ",iso`codomain,"of degree ",iso`degree;
end intrinsic;

/*
 * Two isogenies of semi-Montgomery curves.
 *
 * kernel contains the kernel point normalized and dual indicates if this isogeny was computed as a dual of another one. It is used during the evaluation to determine what formula we want to use
 */

declare type TwoIsog;
declare attributes TwoIsog: domain,codomain,kernel,dual;


intrinsic TwoIsogeny(ker::SmiMntyXZ) -> TwoIsog
 {generate the two-isogeny of kernel ker}
 F:=Parent(ker`X);
 assert not IsIdentity(ker);
 M:=ker`curve;
 Phi:=New(TwoIsog);
 Phi`dual:=false;
 //handles the case of endomorphism of degree 2 at j=1728
 if ker`X eq 0 and jInvariant(M) eq 1728 then
   Phi`domain:=M;
   Phi`codomain := M;
   Phi`kernel:=ker;
   Phi`dual:=false;
 //when ker`X is zero, apply the special formula
 //if this happends for a curve computed as a dual, this will not give the same value for A of the arrival curve
 //this should not be used to compute duals
 elif ker`X eq 0 then
   Phi`kernel:=ker;
   M:=RecoverAlpha(ker`curve);
   Phi`domain:=M;
   A:=-2*M`A/(2*M`alpha+M`A);
   Phi`codomain:=RecoverAlphaSpecialCase(M`A,A);
  //remaining cases, normalizes the kernel and compute the value alpha if it was not computed before
 else
   alpha:=M`alpha;
   if alpha eq 0 then
     alpha:=ker`X/ker`Z;
   elif alpha*ker`Z ne ker`X then
     alpha:=-M`A-M`alpha;
   end if;
   Phi`domain:=RecoverAlpha(M,alpha);
   Phi`kernel:=SemiMontgomeryXZ(alpha,F!1,Phi`domain);
   A:=2*(1-2*(alpha)^2);
   Phi`codomain:=SemiMontgomeryA(A);
 end if;
 return Phi;
end intrinsic;

intrinsic AdjustingAlpha(previous_iso::Isog) -> Isog
  {adjust the codomain of the 2-isog so that alpha is not zero, when alpha is not known}
  phi:=New(Isog);
  phi2:=New(TwoIsog);
  M:=RecoverAlpha(previous_iso`codomain);
  phi`domain:=previous_iso`domain;
  phi2`domain:=previous_iso`domain;
  phi`codomain:=M;
  phi2`codomain:=M;
  phi2`kernel:=previous_iso`isogeny`kernel;
  phi2`dual:=previous_iso`isogeny`dual;
  phi`degree:=2;
  phi`isogeny:=phi2;
  return phi;
end intrinsic;

intrinsic AdjustingAlpha(previous_iso::Isog,alpha::FldFinElt) -> Isog
  {adjust the codomain of the isog of degree 2 so that alpha is not zero}
  assert previous_iso`degree eq 2;
  phi:=New(Isog);
  phi2:=New(TwoIsog);
  M:=RecoverAlpha(previous_iso`codomain,alpha);
  phi`domain:=previous_iso`domain;
  phi2`domain:=previous_iso`domain;
  phi`codomain:=M;
  phi2`codomain:=M;
  phi2`kernel:=previous_iso`isogeny`kernel;
  phi2`dual:=previous_iso`isogeny`dual;
  phi`degree:=2;
  phi`isogeny:=phi2;
  return phi;
end intrinsic;

intrinsic AdjustingAlpha(previous_iso::Isog,dom::SmiMnty,alpha::FldFinElt) -> Isog
  {same as above but with domain specified dom}
  phi:=New(Isog);
  phi2:=New(TwoIsog);
  M:=RecoverAlpha(previous_iso`codomain,alpha);
  phi`domain:=dom;
  phi2`domain:=dom;
  phi`codomain:=M;
  phi2`codomain:=M;
  phi2`kernel:=previous_iso`isogeny`kernel;
  phi2`dual:=previous_iso`isogeny`dual;
  phi`degree:=2;
  phi`isogeny:=phi2;
  return phi;
end intrinsic;

intrinsic Print(iso::TwoIsog)
  {print iso}
  print "isogeny from ",iso`domain," to ",iso`codomain,"of degree ",2;
end intrinsic;

intrinsic DualIsogeny(iso::TwoIsog) -> Isog
  {return the Dual Isogeny of the given two isogeny}
  F:=Parent(iso`kernel`X);
  ker:=SemiMontgomeryXZ(F!0,F!1,iso`codomain);
  M:=ker`curve;
  Phi:=New(Isog);
  Phi`degree:=2;
  Phi`domain:=M;
  Phi`codomain:=iso`domain;
  dual_iso:=New(TwoIsog);
  dual_iso`domain:=iso`codomain;
  dual_iso`codomain:=iso`domain;
  dual_iso`kernel:=ker;
  Phi`isogeny:=dual_iso;
  //if the isogeny given in input has kernel`X = 0, then we want to stick with the formula used in TwoIsogeny to obtain a consistent dual
  if iso`kernel`X eq 0 then
    dual_iso`dual:=false;
  else
    dual_iso`dual := true;
  end if;
  return Phi;
end intrinsic;



//multipoint evaluation tools

//compute the SubProductTree from the points
 SubProductTree:=function(points)
   Q<x>:=PolynomialRing(Parent(points[1]));
   n:=#points;
   len:=2*n-1;
   tree:=[Q!0 : i in [1..len]];
   //first non binary step :
   for i in [1..n] do
     tree[i]:=x-points[i];
   end for;
   for i in [1..n-1] do
    tree[n+i]:=tree[2*i-1]*tree[2*i];
   end for;
   return tree;
 end function;


//compute the SubProductTree from the leafs
 SubProductTreePolynomials:=function(polys)
   zero:=0*polys[1];
   n:=#polys;
   tree:=polys cat [zero : i in [1..(n-1)]];
   for i in [1..n-1] do
    tree[n+i]:=tree[2*i-1]*tree[2*i];
   end for;
   return tree;
 end function;

//compute the sub product tree whose leafs are biquadratic polynomials partly evaluated on T
//this was used as a test, it is not used in current version
SubProductTreeBiquadraticPolynomials:=function(points,T)
  Q<y>:=PolynomialRing(Parent(points[1]`X));
  n:=#points;
  len:=2*n-1;
  A0:=points[1]`curve`A;
  tree:=[Q!0 : i in [1..len]];
   //first non binary step :
  for i in [1..n] do
    Qtemp:=points[i];
    tree[i]:=((y*Qtemp`Z-Qtemp`X)^2*T^2 - T*2*(y*Qtemp`Z^2+Qtemp`X*Qtemp`Z+y*Qtemp`X*(2*A0*Qtemp`Z+y*Qtemp`Z+Qtemp`X))+(y*Qtemp`X-Qtemp`Z)^2);
  end for;
  for i in [1..n-1] do
    tree[n+i]:=tree[2*i-1]*tree[2*i];
  end for;
  return tree;
end function;

 // SubProductTreePolynomials_old:=function(polys,height)
 //   zero:=0*polys[1];
 //   tree:=[zero : i in [1..2^(height)]];
 //   //first non binary step :
 //   for i in [1..#polys] do
 //     tree[2^(height-1)-1+i]:=polys[i];
 //   end for;
 //   for k in [1..(height-1)] do
 //     for i in [1..2^(height-1-k)] do
 //       index:=2^(height-1-k)-1+i;
 //       if tree[2*index+1] eq 0 and tree[2*index] ne 0 then
 //         tree[index]:=tree[2*index];
 //       else
 //         tree[index]:=tree[2*index]*tree[2*index+1];
 //       end if;
 //     end for;
 //   end for;
 //   return tree;
 // end function;

 MultipointEvaluation:=function(tree,P)
   zero:=0*tree[1];
   n:=(#tree +1) div 2;
   tree_eval:=[zero: i in [1..#tree]];
   tree_eval[2*n-1]:= P mod tree[2*n-1];
   for i in [1..(n-1)] do
     index:=n - i;
     tree_eval[2*index] :=tree_eval[n+index] mod tree[2*index];
     tree_eval[2*index-1] :=tree_eval[n+index] mod tree[2*index-1];
   end for;
   return [Evaluate(tree_eval[i],1): i in [1..n]];
 end function;

//Evaluate the polynomials with roots P`X / P`Z with P in points, when we don't want to inverse elements
Eval_not_frac:=function(points,x)
  return &*[x*point`Z-point`X:point in points];
end function;

//same as above but points contains the values P`X / P`Z
Eval:=function(points,x)
  return &*[x-point: point in points];
end function;

// Evaluate the biquadratic polynomial from precomputed Values
//this was used as a test, it is not used in current version
EvalQuadratic:=function(p2,p5,ev)
  _<x>:=PolynomialRing(Parent(p5[1][1]));
  return &*[x^2*(p2[i]`Z*ev-p2[i]`X)^2 + x*(-2*p5[i][1]*(ev^2+1) -2*ev*p5[i][2]) + (ev*p2[i]`X-p2[i]`Z)^2 : i in [1..#p2]];
end function;

/*
 * Odd-degree isogenies of semi-Montgomery curves.
 *
 * Small isogeny are evaluated using the naive method. kernel_points contains the points of the kernel used in the computation
 * Big Isogeny are evaluated using the fast method. isogeny contains all the information necessary to evaluate the isogeny
 */

declare type OddSmallIsog;
declare attributes OddSmallIsog: domain, codomain,degree,kernel_points;

declare type OddBigIsog;
declare attributes OddBigIsog: domain, codomain,degree,isogeny;


intrinsic SmallIsogeny(ker::SmiMntyXZ, ell::RngIntElt) -> OddSmallIsog
	{Create a small isogeny of degree ell with kernel generator ker}
	assert not IsIdentity(ker);
  M:=ker`curve;
	Phi:=New(OddSmallIsog);
	Phi`domain:=M;
	Phi`degree:=ell;
	F:=Parent(ker`X);
	kernel_points:=[ker];
  p1:=(ker`X-ker`Z);p2:=(ker`X+ker`Z);
	temp:=ker;
	dif:=ZeroXZ(M);
  a:=M`A+2;
  d:=M`A-2;
	for i in [2..(ell-1) div 2] do
		tt:=temp;
		temp:=XAdd(ker,temp,dif);
		dif:=tt;
     p1*:=(temp`X-temp`Z);p2*:=(temp`X+temp`Z);
		Append(~kernel_points,temp);
	end for;

	Phi`kernel_points:=kernel_points;
  a1:=a^(ell)*p2^8;
  d1:=d^(ell)*p1^8;
  A2:=2*(a1+d1)/(a1-d1);
  M2:=SemiMontgomeryA(A2);
  Phi`codomain:=M2;
	return Phi;
end intrinsic;

intrinsic BigIsogeny(ker::SmiMntyXZ, ell::RngIntElt) -> OddBigIsog
	{create a BigIsogeny with kernel generator ker}
	assert not IsIdentity(ker);
  M:=ker`curve;
	Phi:=New(OddBigIsog);
	Phi`domain:=M;
	Phi`degree:=ell;
	A0:=M`A;
  doubleA0:=2*A0;
	F:=Parent(A0);
  m:=Floor(Sqrt(ell/2));
  k:=Floor(m/2);
  if m^2+m ge Ceiling(ell/2) then
    m:=m-1;
  end if;
  _<x>:=PolynomialRing(F);
  _<y,T>:=PolynomialRing(F,2);
	frac:=ker`X/ker`Z;
  p1:=[frac];
  Ptemp:=ker;
  Pdiff:=ZeroXZ(M);
  Q:=(2*m)*ker;
  Qtemp:=Q;
  Qdiff:=ZeroXZ(M);
  Stemp:=m*ker;
  Sdiff:=Stemp;
  frac2:=Q`X/Q`Z;
  p2:=[frac2];
  sq:=frac2^2;
  doublefrac2:=2*frac2;
  p3:=[ y^2*T^2 - y^2*T*doublefrac2 + y^2 *sq - y*T^2*(doublefrac2)
  - y*T*2*(1 + sq +doubleA0*frac2) + T^2*sq - T*doublefrac2 - y* doublefrac2 +1];
  p4:=[Stemp`X/Stemp`Z];
  g1:=1;
  for i in [2..(m-1)] do
    Pttemp:=Ptemp;
    Ptemp:=XAdd(Ptemp,ker,Pdiff);
    Pdiff:=Pttemp;
		frac:=Ptemp`X/Ptemp`Z;
    Append(~p1,frac);
  end for;
  for i in [2..k] do
    Qttemp:=Qtemp;
    Qtemp:=XAdd(Qtemp,Q,Qdiff);
    Qdiff:=Qttemp;
    Sttemp:=Stemp;
    Stemp:=XAdd(Stemp,Q,Sdiff);
    Sdiff:=Sttemp;
    frac2:=Qtemp`X/Qtemp`Z;
    Append(~p2,frac2);
    Append(~p4,Stemp`X/Stemp`Z);
    sq:=frac2^2;
    doublefrac2:=2*frac2;
    Append(~p3, y^2*T^2 - y^2*T*doublefrac2 + y^2 *sq - y*T^2*(doublefrac2)
    - y*T*2*(1 + sq +doubleA0*frac2) + T^2*sq - T*doublefrac2 - y* doublefrac2 +1 );
  end for;
  R:=(2*k*m+m)*ker;
  Rdiff:=(2*k*m+m-1)*ker;
  Append(~p4,R`X/R`Z);
  Rtemp:=R;
  for i in [(2*k*m+m+1)..(ell-1) div 2] do
    Rttemp:=Rtemp;
    Rtemp:=XAdd(Rtemp,ker,Rdiff);
    Rdiff:=Rttemp;
    Append(~p4,Rtemp`X/Rtemp`Z);
  end for;
  tree1:=SubProductTree(p1);
	poly1:=tree1[#tree1];
	Phi`isogeny:=<tree1,p2,p3,p4>;
  a:=M`A+2;
  d:=M`A-2;
  poly3:=&*[UnivariatePolynomial(Evaluate(poly3,2,1)): poly3 in p3];
  prod3:=Evaluate(poly1,1)*Eval(p2,1)*Eval(p4,1)*(&*MultipointEvaluation(tree1,poly3));
  poly3:=&*[UnivariatePolynomial(Evaluate(poly3,2,-1)): poly3 in p3];
  prod4:=Evaluate(poly1,-1)*Eval(p2,-1)*Eval(p4,-1)*(&*MultipointEvaluation(tree1,poly3));
  a1:=a^(ell)*prod4^8;
  d1:=d^(ell)*prod3^8;
  A2:=2*(a1+d1)/(a1-d1);
  M2:=SemiMontgomeryA(A2);
	Phi`codomain:=M2;
	return Phi;
end intrinsic;

intrinsic Print(iso::OddBigIsog)
  {print iso}
  print "isogeny from ",iso`domain," to ",iso`codomain,"of degree ",iso`degree;
end intrinsic;
intrinsic Print(iso::OddSmallIsog)
  {print iso}
  print "isogeny from ",iso`domain," to ",iso`codomain,"of degree ",iso`degree;
end intrinsic;


intrinsic Evaluate(isogeny::OddSmallIsog,points::[SmiMntyXZ]) -> SeqEnum
	{evaluate the isogeny on points using the naive method}
	F:=Parent(isogeny`domain`alpha);
	image_points:=[];
	for P in points do
		if IsIdentity(P) then
			Append(~image_points,ZeroXZ(isogeny`codomain));
		else
			X:=1;
			Z:=1;
			for Q in isogeny`kernel_points do
				X*:=Q`X * P`X - Q`Z * P`Z;
				Z*:=P`X * Q`Z - P`Z * Q`X;
			end for;
			X^:=2;
			Z^:=2;
			X*:=P`X;
			Z*:=P`Z;
      if Z eq F!0 then
        Append(~image_points,ZeroXZ(isogeny`codomain));
      else
			  Append(~image_points,SemiMontgomeryXZ(X,Z,isogeny`codomain));
      end if;
		end if;
	end for;
	return image_points;
end intrinsic;

intrinsic Evaluate(iso::OddBigIsog,points::[SmiMntyXZ]) -> SeqEnum
	{evaluate the isogeny on points using the fast method}
	F:=Parent(iso`domain`alpha);
	image_points:=[];
	for P in points do
		if P`Z eq 0 then
			Append(~image_points,ZeroXZ(iso`codomain));
    elif P`X eq 0 then
      Append(~image_points,SemiMontgomeryXZ(F!0,F!1,iso`codomain));
		else
			v:=P`X/P`Z;
			inv:=1/v;
			isog:=iso`isogeny;
			tree1:=isog[1];poly2:=isog[2];
			p3:=isog[3];poly4:=isog[4];
      poly1:=tree1[#tree1];
	  	poly3:=&*[UnivariatePolynomial(Evaluate(poly3,2,v)): poly3 in p3];
	  	denom:=Evaluate(poly1,v)*Eval(poly2,v)*Eval(poly4,v)*(&*MultipointEvaluation(tree1,poly3));

      poly3:=&*[UnivariatePolynomial(Evaluate(poly3,2,inv)): poly3 in p3];
			num:=Evaluate(poly1,inv)*Eval(poly2,inv)*Eval(poly4,inv)*(&*MultipointEvaluation(tree1,poly3));
      if denom eq 0 then
        Append(~image_points,ZeroXZ(iso`codomain));
      else
			  Append(~image_points,SemiMontgomeryXZ(v^iso`degree*num^2,denom^2,iso`codomain));
      end if;
		end if;
	end for;
	return image_points;
end intrinsic;

intrinsic Evaluate(iso::TwoIsog,points::[SmiMntyXZ]) -> SeqEnum
  {evaluate the isogeny on points}
  // [Normalized(point)`X: point in points ];
  F:=Parent(iso`domain`A);
  image_points:=[];
  for P in points do
    if P`Z eq 0 then
      Append(~image_points,ZeroXZ(iso`codomain));
    elif iso`kernel`X eq 0 then
      //two possibilities : dual or not, we don't use the same formula for the two cases
      M:=iso`domain;
      non_dual:=false;
      if M`alpha eq 0 then
        A1:=iso`domain`A;
        A2:=iso`codomain`A;
        //if not a dual, we have a formula to recover alpha
        if not iso`dual then
          alpha_test:=-( (2+A1)*A2)/(2*A1);
          M:=RecoverAlpha(M,alpha_test);
        end if;
      end if;
      //first case, where this is not a dual
      if not iso`dual then
        //small test, should not happen
        if M`alpha eq 0 then "alpha is zero in non dual case"; M:=RecoverAlpha(M); end if;
        x1 := (P`X - P`Z)^2; z1 := P`X * P`Z;
        alpha:=M`alpha;
        sq:=2*alpha+M`A;
        Append(~image_points,SemiMontgomeryXZ(x1+z1*(M`A+2),z1*sq,RecoverAlpha(iso`codomain)));
      //second case where the isogeny is truly a dual
      else
        alpha:=iso`codomain`alpha;
        //small test, this should not happen
        if alpha eq 0 then "alpha is zero in dual"; M:=RecoverAlpha(iso`codomain); alpha:=M`alpha; end if;
        Append(~image_points,SemiMontgomeryXZ( (P`X+P`Z)^2,4*alpha*P`X*P`Z,iso`codomain ));
      end if;
    // generic case where kernel`X not zero
    else
      X:=iso`kernel`X;
      Z:=iso`kernel`Z;
      Append(~image_points,SemiMontgomeryXZ(P`X*(P`X*X-P`Z*Z),P`Z*(P`X*Z-P`Z*X),iso`codomain));
    end if;
  end for;
  return image_points;
end intrinsic;
