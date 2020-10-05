
Attach("src/Montgomery.m");
load "src/tools.m";

p := 73743043621499797449074820543863456997944695372324032511999999999999999999999;

Fp := FiniteField(p);
R<X> := PolynomialRing(Fp);
Fq<a> := ExtensionField<Fp,a|X^2+1>;
R<X> := PolynomialRing(Fq);

E0 := Montgomery(a,Fq!1);

degree_bound:=120;
max_degree := 1;
smoothness_bound := 30000;


exponent_power_of_2_rational_torsion := Valuation(p+1,2);
cofactor := (p+1) div 2^exponent_power_of_2_rational_torsion;

//COMPUTING STRATEGIES
strategies:=[ []: i in [1..5] ];

strat3:=[];
for i in [1..53] do
  Append(~strat3,<<3,i>,strategy(i,37,26)>);
end for;
strategies[3]:=strat3;
strat5:=[];
for i in [1..21] do
  Append(~strat5,<<5,i>,strategy(i,50,46)>);
end for;
strategies[5]:=strat5;
strat2:=[];
for i in [1..32] do
  Append(~strat2,<<2,i>,strategy(i,13,15)>);
end for;
strategies[2]:=strat2;

  QQ:= Rationals();
  B<i,j,k> := QuaternionAlgebra< QQ | -1, -p>; // i in distorsion, j is frobenius, k is i*j is dist o frob
  O0 := QuaternionOrder([1,i,(1+k)/2,(i+j)/2]);//QuaternionOrder([1,i,(1+k)/2,(i+j)/2]);




quadratic_non_residue := function(F)
  repeat
    r := Random(F);
  until not(IsSquare(r));
  return r;
end function;


// COMPUTING WHICH TORSION IS ACCESSIBLE
root_order_in_extension:=function(p,i);
  return p^i - (-1)^i;
end function;

root_order_in_extension_mod_l:=function(p,i,l);
  return (Modexp(-p,i,l) - 1) mod l;
end function;

extension_degree_torsion:=function(p,l);
  i := 1;
  while (root_order_in_extension_mod_l(p,i,l) ne 0) and (i le max_degree) do
    i +:= 1;
  end while;
  return i;
end function;

root_order_in_extension_mod_l_twist:=function(p,i,l);
  return (Modexp(-p,i,l) + 1) mod l;
end function;

extension_degree_torsion_twist:=function(p,l);
  i := 1;
  while (root_order_in_extension_mod_l_twist(p,i,l) ne 0) and (i le max_degree) do
    i +:= 1;
  end while;
  return i;
end function;


torsion_data := [];
torsion_data_twist := [];
l := 3;


div_condition:=function(d);
  return true; // (30 mod d eq 0) or (36 mod d eq 0) or (42 mod d eq 0) or (44 mod d eq 0);
end function;


while l le smoothness_bound do
  d := extension_degree_torsion(p,l);
  i := 1;
  while (d le max_degree) and (l*d le smoothness_bound) do
    torsion_data := Append(torsion_data,<l,i,d>);
    i +:= 1;
    d := extension_degree_torsion(p,l^i);
  end while;


  d := extension_degree_torsion_twist(p,l^i);
  while (d le max_degree) and (l*d le smoothness_bound) do
    torsion_data_twist := Append(torsion_data_twist,<l,i,d>);
    i +:= 1;
    d := extension_degree_torsion_twist(p,l^i);
  end while;

  l := NextPrime(l);
end while;


tot := &*[t[1] : t in torsion_data];

tot_twist := &*[t[1] : t in torsion_data_twist];





available_odd_torsion := &*[t[1] : t in torsion_data | t[1] ne 2] * &*[t[1] : t in torsion_data_twist];
available_odd_torsion_fac := Factorisation(available_odd_torsion);


extension_degrees := [d : d in Set([t[3] : t in torsion_data cat torsion_data_twist])];

sparse_irred:=function(deg);
  poly := R!0;
  ctr := 0;
  while true do
    ctr +:= 1;
    poly := X^(deg) + ((1 - (deg mod 2))*a + ctr)*X + 1;
    if IsIrreducible(poly) then
      break;
    end if;
  end while;
  return poly;
end function;


polynomials := [sparse_irred(d) : d in extension_degrees];
field_extensions := [ExtensionField<Fq, b | P : Check := false> : P in polynomials];
 curve_extensions := [E0];

twisters := <quadratic_non_residue(F) : F in field_extensions>;
twisterp:=twisters[1]^((p-1) div 2);

 distorsion_endomorphism:=function(P);
   return MontgomeryPt(-P`x,a*P`y,P`z,P`curve);
 end function;

 frobenius_endomorphism:=function(P);
   if P`curve`B eq 1 then
     twist:=1;
   else
     twist:=twisterp;
   end if;
   return MontgomeryPt(Frobenius(P`x,Fp),Frobenius(P`y,Fp)*twist,Frobenius(P`z,Fp),P`curve);
 end function;




// COMPUTING BASES OF THE TORSION


points := <RandomPt(E) : E in curve_extensions>;


SmoothPoint:=function(P);
  degree := 1;
  //"smooth point", degree;
  a,b := smooth_part(root_order_in_extension(p,degree),smoothness_bound);
  return b * P;
end function;


smooth_points := <SmoothPoint(P) : P in points>;




torsion_points:=function(t, smooth_points);
  //"torsion point", t;
  order := root_order_in_extension(p,t[3]);
  a,b := smooth_part(order,smoothness_bound);

  i := 0;
  repeat
    i := i+1;
  until t[3] eq Degree(polynomials[i]);
  res := (a div (t[1]^t[2])) * smooth_points[i];
  return res;
end function;


torsion_points := <torsion_points(t, smooth_points) : t in torsion_data>;


torsion_point:=function(t,P);
  order := root_order_in_extension(p,t[3]);
  a,b := smooth_part(order,smoothness_bound);

  i := 0;
  repeat
    i := i+1;
  until t[3] eq Degree(polynomials[i]);
  res := (a div (t[1]^t[2])) * P;
  return res;
end function;


 for i in [1..#torsion_points] do
  while IsIdentity((torsion_data[i][1]^(torsion_data[i][2]-1))*torsion_points[i]) do
    // point := random_point(Curve(torsion_points[i]));
    point:=RandomPt(torsion_points[i]`curve);
    point := SmoothPoint(point);
    torsion_points[i] := torsion_point(torsion_data[i], point);
  end while;
end for;


clean_basis:=function(torsion_points,torsion_data)
  torsion_points_new := torsion_points;
  for i in [1..#torsion_points] do
    if (i eq #torsion_points) or (torsion_data[i][1] ne torsion_data[i+1][1]) then
      for j in [k : k in [1..i-1] | torsion_data[k][1] eq torsion_data[i][1]] do
        factor := torsion_data[j][1]^(torsion_data[i][2]-torsion_data[j][2]);
        torsion_points_new[j] := Parent(torsion_points[j])!(factor*torsion_points[i]);
      end for;
    end if;
  end for;
  return torsion_points_new;
end function;

torsion_points := clean_basis(torsion_points,torsion_data);


precomp_basis:=function(torsion_data,torsion_points)
  torsion_points_2 := torsion_points;
  for i in [1..#torsion_points] do
    factor := torsion_data[i][1]^(torsion_data[i][2] - 1);
    torsion_points_2[i] := distorsion_endomorphism(torsion_points_2[i]);
    // test if torsion_points[i] and torsion_points_2[i] form a basis
    if not(
      IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
      ) then

      // try again by applying frobenius
      //"SPECIAL:", torsion_data[i];
      torsion_points_2[i] := frobenius_endomorphism(torsion_points[i]);
      if not(
        IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
        ) then

        // Final try
        torsion_points_2[i] := distorsion_endomorphism(torsion_points_2[i]);
        if not(
          IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
          ) then
          "ERROR: NO BASIS FOUND";
        end if;
      end if;
    end if;
  end for;
  return torsion_points_2;
end function;


torsion_points_2 := precomp_basis(torsion_data,torsion_points);


basis := <<torsion_points[i], torsion_points_2[i]> : i in [1..#torsion_points]>;


// COMPUTING THE ACTION OF THE ENDOMORPHISM RING
precomp_action:=function(endo, torsion_data, basis);
  distorsion_matrix := [];
  for i in [1..#basis] do
    if (i eq #basis) or (torsion_data[i][1] ne torsion_data[i+1][1]) then
      // torsion_data[i];
      ln := torsion_data[i][1]^torsion_data[i][2];

      P1 := basis[i][1];
      P2 := basis[i][2];
      P1_endo := endo(P1);
      P2_endo := endo(P2);
      // "dlp1"; time
      dlp1 := DLP_dimension_2_power(P1_endo,P1,P2,torsion_data[i][1],torsion_data[i][2]);

      //"dlp2"; time
      dlp2 := DLP_dimension_2_power(P2_endo,P1,P2,torsion_data[i][1],torsion_data[i][2]);
      dlp1 := [centered_reduction(i,ln) : i in dlp1];
      dlp2 := [centered_reduction(i,ln) : i in dlp2];

      m := Transpose(Matrix([dlp1,dlp2]));
      distorsion_matrix := distorsion_matrix cat [m];



      for j in [k : k in [1..i-1] | torsion_data[k][1] eq torsion_data[i][1]] do
        ln := torsion_data[j][1]^torsion_data[j][2];
        factor := torsion_data[j][1]^(torsion_data[i][2]-torsion_data[j][2]);
        distorsion_matrix[j] := Matrix(
          [ [centered_reduction(m[1][1],ln),centered_reduction(m[1][2],ln)],
            [centered_reduction(m[2][1],ln),centered_reduction(m[2][2],ln)]
          ]
          );
      end for;


    else
      distorsion_matrix := distorsion_matrix cat [Matrix([[0,0],[0,0]])];
    end if;
  end for;
  return distorsion_matrix;
end function;

precomp_action_list:=function(endomorphisms, torsion_data, basis);
  distorsion_matrix := [];
  for i in [1..#basis] do
    // torion_data[i];
    ln := torsion_data[i][1]^torsion_data[i][2];

    P1 := basis[i][1];
    P2 := basis[i][2];

    //"i", i, torsion_data[i][1],torsion_data[i][2];

    P1_endo := endomorphisms(P1);
    P2_endo := endomorphisms(P2);


    dlp1 := DLP_dimension_2_power(P1_endo,P1,P2,torsion_data[i][1],torsion_data[i][2]);
    dlp2 := DLP_dimension_2_power(P2_endo,P1,P2,torsion_data[i][1],torsion_data[i][2]);
    dlp1 := [centered_reduction(i,ln) : i in dlp1];
    dlp2 := [centered_reduction(i,ln) : i in dlp2];

    m := Transpose(Matrix([dlp1,dlp2]));
    distorsion_matrix := distorsion_matrix cat [m];


  end for;
  return distorsion_matrix;
end function;


 action_dist := precomp_action(distorsion_endomorphism, torsion_data, basis);
 action_frob := precomp_action(frobenius_endomorphism, torsion_data, basis);


distfrob := func <P | distorsion_endomorphism(frobenius_endomorphism(P))>;
distfrob_twist := func <P | distorsion_endomorphism(frobenius_endomorphism(P))>;

action_distfrob := [action_dist[i]*action_frob[i] : i in [1..#action_dist]];


DistorsionEndomorphism:=distorsion_endomorphism;

  FrobeniusEndomorphism:=frobenius_endomorphism;

basis_of_power_of_2_torsion := function(E);
  n := exponent_power_of_2_rational_torsion;

  repeat
    B1 := cofactor*RandomPt(E);
  until not IsIdentity(B1*2^(n-1));

  repeat
    B2 := cofactor*RandomPt(E);
  until (not IsIdentity(B2*2^(n-1))) and (not (B1*2^(n-1) eq B2*2^(n-1)));
  return [B1,B2];
end function;


basis_2 := basis_of_power_of_2_torsion(E0);

basis_2:=[2*bas_2:bas_2 in basis_2];

exponent_power_of_2_rational_torsion-:=1;

action_dist_2 := precomp_action(distorsion_endomorphism, [<2,exponent_power_of_2_rational_torsion,1>], [basis_2])[1];
 action_frob_2 := precomp_action(frobenius_endomorphism, [<2,exponent_power_of_2_rational_torsion,1>], [basis_2])[1];


field_extension_2 := ExtensionField<Fq, b | sparse_irred(2) : Check := false> ;
curve_extension_2 := E0;

id_plus_distfrob_half:=function(P);
  Q := DivisionPoint(P,2);
  return Q + distorsion_endomorphism(frobenius_endomorphism(Q));
end function;

dist_plus_frob_half:=function(P);
  Q := DivisionPoint(P,2);
  return distorsion_endomorphism(Q) + frobenius_endomorphism(Q);
end function;

action_id_plus_distfrob_half_2 := precomp_action(id_plus_distfrob_half, [<2,exponent_power_of_2_rational_torsion,1>], [basis_2])[1];
action_dist_plus_frob_half_2 := precomp_action(dist_plus_frob_half, [<2,exponent_power_of_2_rational_torsion,1>], [basis_2])[1];

action_distfrob_2 := action_dist_2*action_frob_2;



curve_extensions_twist := [Montgomery(a,twisters[i]) : i in [1..#curve_extensions]];




 frobenius_twisters := <t^((1-p) div 2) : t in twisters>;



 points_twist := <RandomPt(E) : E in curve_extensions_twist>;


root_order_in_extension_twist:=function(p,i);
  return p^i + (-1)^i;
end function;


SmoothPoint_twist:=function(P);
  degree := 1;
  //"smooth point", degree;
  a,b := smooth_part(root_order_in_extension_twist(p,degree),smoothness_bound);
  return b * P;
end function;

smooth_points_twist := <SmoothPoint_twist(P) : P in points_twist>;


torsion_points_twist:=function(t, smooth_points);
  //"torsion point", t;
  order := root_order_in_extension_twist(p,t[3]);
  a,b := smooth_part(order,smoothness_bound);

  i := 0;
  repeat
    i := i+1;
  until t[3] eq Degree(polynomials[i]);

  res := (a div (t[1]^t[2])) * smooth_points[i];
  return res;
end function;

 torsion_points_twist := <torsion_points_twist(t, smooth_points_twist) : t in torsion_data_twist>;

torsion_point_twist:=function(t,P);
  order := root_order_in_extension_twist(p,t[3]);
  a,b := smooth_part(order,smoothness_bound);

  i := 0;
  repeat
    i := i+1;
  until t[3] eq Degree(polynomials[i]);

  res := (a div (t[1]^t[2])) * P;
  return res;
end function;


for ctr in [1..#torsion_points_twist] do
  while IsIdentity((torsion_data_twist[ctr][1]^(torsion_data_twist[ctr][2]-1))*torsion_points_twist[ctr]) do
    point := RandomPt(torsion_points_twist[ctr]`curve);
    point := SmoothPoint_twist(point);
    torsion_points_twist[ctr] := torsion_point_twist(torsion_data_twist[ctr], point);
  end while;
end for;

torsion_points_twist := clean_basis(torsion_points_twist,torsion_data_twist);

precomp_basis_twist:=function(torsion_data,torsion_points)
  torsion_points_2 := torsion_points;
  for i in [1..#torsion_points] do
    factor := torsion_data[i][1]^(torsion_data[i][2] - 1);
    torsion_points_2[i] := distorsion_endomorphism(torsion_points_2[i]);
    // test if torsion_points[i] and torsion_points_2[i] form a basis
    if not(
      IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
      ) then

      // try again by applying frobenius
      //"SPECIAL:", torsion_data[i];
      torsion_points_2[i] := frobenius_endomorphism(torsion_points[i]);
      if not(
        IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
        ) then

        // Final try
        torsion_points_2[i] := distorsion_endomorphism(torsion_points_2[i]);
        if not(
          IsLinearlyIndependent(factor * torsion_points[i], factor * torsion_points_2[i], torsion_data[i][1])
          ) then
          "ERROR: NO BASIS FOUND";
        end if;
      end if;
    end if;
  end for;
  return torsion_points_2;
end function;



 torsion_points_twist_2 := precomp_basis_twist(torsion_data_twist, torsion_points_twist);
basis_twist := <<torsion_points_twist[i], torsion_points_twist_2[i]> : i in [1..#torsion_points_twist]>;

action_dist_twist := precomp_action(distorsion_endomorphism, torsion_data_twist, basis_twist);


 action_frob_twist := precomp_action(frobenius_endomorphism,
  torsion_data_twist, basis_twist);

// "action distfrob twists";
//time action_distfrob := precomp_action(distfrob);
action_distfrob_twist := [action_dist_twist[i]*action_frob_twist[i] : i in [1..#action_dist_twist]];

"data generation done";

test_precomputations := procedure();
  centered_reduction_vec := func<m,l | [centered_reduction(t,l) : t in Eltseq(m)]>;
  dist := distorsion_endomorphism;
  frob := frobenius_endomorphism;

  for i in [1..#torsion_data] do
      correct := true;

      ln := torsion_data[i][1]^torsion_data[i][2];

      P1 := torsion_points[i];
      P2 := torsion_points_2[i];

      correct := correct and IsLinearlyIndependent(P1, P2,ln);


      if (torsion_data[i][2] gt 1) then
        correct := correct and IsIdentity(torsion_data[i][1]*P1 - Parent(P1)!torsion_points[i-1]) and
          IsIdentity(torsion_data[i][1]*P2 - Parent(P2)!torsion_points_2[i-1]);
      end if;


      P1_dist := dist(P1);
      P2_dist := dist(P2);

      P1_frob := frob(P1);
      P2_frob := frob(P2);

      P1_distfrob := distfrob(P1);
      P2_distfrob := distfrob(P2);

      m_dist := action_dist[i];
      m_frob := action_frob[i];
      m_distfrob := action_distfrob[i];


      correct := correct and IsIdentity(m_dist[1][1]*P1 + m_dist[2][1]*P2 - P1_dist);
      correct := correct and IsIdentity(m_dist[1][2]*P1 + m_dist[2][2]*P2 - P2_dist);

      correct := correct and IsIdentity(m_frob[1][1]*P1 + m_frob[2][1]*P2 - P1_frob);
      correct := correct and IsIdentity(m_frob[1][2]*P1 + m_frob[2][2]*P2 - P2_frob);

      correct := correct and IsIdentity(m_distfrob[1][1]*P1 + m_distfrob[2][1]*P2 - P1_distfrob);
      correct := correct and IsIdentity(m_distfrob[1][2]*P1 + m_distfrob[2][2]*P2 - P2_distfrob);

      if not(correct) then
        "ERROR at iteration", torsion_data[i][1], torsion_data[i][2];
      end if;
  end for;
  "success";
end procedure;
test_precomputations_twist := procedure();
  centered_reduction_vec := func<m,l | [centered_reduction(t,l) : t in Eltseq(m)]>;
  dist := distorsion_endomorphism;
  frob := frobenius_endomorphism;

  for i in [1..#torsion_data_twist] do
      correct := true;
      // torsion_data_twist[i];
      ln := torsion_data_twist[i][1]^torsion_data_twist[i][2];

      P1 := torsion_points_twist[i];
      P2 := torsion_points_twist_2[i];
      correct := correct and IsLinearlyIndependent(P1, P2,ln);

      if (torsion_data_twist[i][2] gt 1) then
        correct := correct and IsIdentity(torsion_data_twist[i][1]*P1 - Parent(P1)!torsion_points_twist[i-1]) and
          IsIdentity(torsion_data_twist[i][1]*P2 - Parent(P2)!torsion_points_twist_2[i-1]);
      end if;


      P1_dist := dist(P1);
      P2_dist := dist(P2);

      // P1_frob := frob(P1, frobenius_twisters[torsion_data_twist[i][3]]);
      // P2_frob := frob(P2, frobenius_twisters[torsion_data_twist[i][3]]);
      P1_frob := frob(P1);
      P2_frob := frob(P2);

      P1_distfrob := distfrob_twist(P1);
      P2_distfrob := distfrob_twist(P2);

      m_dist := action_dist_twist[i];
      m_frob := action_frob_twist[i];
      m_distfrob := action_distfrob_twist[i];


      correct1 := correct and IsIdentity(m_dist[1][1]*P1 + m_dist[2][1]*P2 - P1_dist);
      correct2 := correct1 and IsIdentity(m_dist[1][2]*P1 + m_dist[2][2]*P2 - P2_dist);

      correct3 := correct2 and IsIdentity(m_frob[1][1]*P1 + m_frob[2][1]*P2 - P1_frob);
      correct4 := correct3 and IsIdentity(m_frob[1][2]*P1 + m_frob[2][2]*P2 - P2_frob);

      correct5 := correct4 and IsIdentity(m_distfrob[1][1]*P1 + m_distfrob[2][1]*P2 - P1_distfrob);
      correct6 := correct5 and IsIdentity(m_distfrob[1][2]*P1 + m_distfrob[2][2]*P2 - P2_distfrob);

      if not(correct6) then

        correct,correct1,correct2,correct3,correct4,correct5,correct6;
        if not correct then "is a good basis :", IsIdentity(torsion_data_twist[i][1]*P1 - Parent(P1)!torsion_points_twist[i-1]); end if;
        "ERROR at iteration", torsion_data_twist[i][1], torsion_data_twist[i][2];
      end if;
  end for;
  "success";
end procedure;

// "testing"; time
// test_precomputations();
// "testing"; time
// test_precomputations_twist();







torsion_prime := [t[1]: t in torsion_data];
torsion_prime_twist := [t[1]: t in torsion_data_twist];
torsion_orders := [t[1]^t[2] : t in torsion_data];
torsion_orders_twist := [t[1]^t[2] : t in torsion_data_twist];
// for odd l
GetTorsionPoint_index:=function(l);
  return Position(torsion_orders, l);
end function;

// for odd l
GetTorsionPoint_index_twist:=function(l);
  return Position(torsion_orders_twist, l);
end function;







get_twister :=function(l);
  index := Position(torsion_orders_twist, l);
  if not(IsZero(index)) then
    return twisters[torsion_data_twist[index][3]];
  end if;
  return 1;
end function;



// get the curve where the l-torsion lives
get_extension_degree :=function(l);
  index := Position(torsion_orders, l);
  if not(IsZero(index)) then
    return torsion_data[index][3];
  end if;
  index := Position(torsion_orders_twist, l);
  if not(IsZero(index)) then
    return torsion_data_twist[index][3];
  end if;
  print "ERROR in get_extension_degree: torsion is not available";
  return 0;
end function;




get_torsion_data :=function(ln);
  index := Position(torsion_orders, ln);
  if not(IsZero(index)) then
    i := 1;
    l := torsion_data[index][1];
    // search for largest m such that l^m*torsion is in a subfield
    while (index gt i) and (torsion_data[index-i][1] eq l) and (torsion_data[index-i][3] eq torsion_data[index][3]) do
      i +:= 1;
    end while;
    m := 0;
    if (index gt i) and (torsion_data[index-i][1] eq l) then // none of the torsion is in a subfield
      m := torsion_data[index-i][2];
    end if;

    return torsion_data[index], basis[index], action_dist[index], action_frob[index], action_distfrob[index],1,m;
  end if;
  index := Position(torsion_orders_twist, ln);
  if not(IsZero(index)) then

    return torsion_data_twist[index], basis_twist[index], action_dist_twist[index], action_frob_twist[index], action_distfrob_twist[index],frobenius_twisters[torsion_data_twist[index][3]],0;
  end if;
  return 0;
end function;
