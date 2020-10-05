

centered_reduction := func< x, l | ((x+((l-1) div 2)) mod l) - ((l-1) div 2) >;

//correct the bug when the generated strategy is not correct
correct_strategy:=function(s)
  strat:=s;
  e:=#s;
    ok:=true;
    index_s:=1;
  	index_pts:=0;
  	points:=[];
  	pts_index:=[];
  	index:=0;
  	for j in [1..(e-1)] do
      last_index_s:=index_s;
  		while index lt (e)-j do
  			if index_pts ge #pts_index then
  				Append(~pts_index,index);
  				index_pts+:=1;
  			else
  				pts_index[index_pts+1]:=index;
  				index_pts+:=1;
  			end if;
  			m:=s[index_s];index_s+:=1;
  			index+:=m;
  		end while;
      // "kernel_index",index;
      if ok and index eq e then
        // "error beginning !!!!!!";
        index_corr:=1;
        if strat[index_corr] mod 2 eq 1 then
          index_corr:=2;
        end if;
        strat[index_corr] := s[index_corr]-1;
      // end if;
      elif ok and index eq (e-j+1) then
        // "error above !!!!!";
        strat[index_s-1]:=strat[index_s-1]-1;
        // strat[]1
      end if;
  		pts_index:=[pts_index[i+1]:i in [0..index_pts-1] ];
  		index:=pts_index[index_pts];
  		index_pts-:=1;
  	end for;
    s:=strat;
  // until ok;
  assert s eq strat;
  return strat;
end function;

strategy:=function(n,p,q)
  S:=[ [] ];
  C:= [0];
  for i in [2..n+1] do
    b:=1;
    cost:=C[i-1]+C[1]+p+(i-1)*q;
    if i ne 2 then
      for j in [2..i-1] do
        cost_t:=C[j]+C[i-j]+j*p+(i-j)*q;
        if cost_t lt cost then
          cost:=cost_t;
          b:=j;
        end if;
      end for;
    end if;

    Append(~S,[b] cat S[i-b] cat S[b]);
    Append(~C,cost);
  end for;
  return correct_strategy(S[n+1]);
end function;


Bitsize:=function(l)
  return Floor(Log(l)/Log(2));
end function;

sort_insert:=function(list,val)
  if list eq [] then
    return [val];
  end if;
  low:=[];
  big:=list;
  A:=big[1];
  while A le val and big ne [] do
    Append(~low,A);
    Remove(~big,1);
    if big eq [] then
      break;
    else
      A:=big[1];
    end if;
  end while;
  Append(~low,val);
  l:=low cat big;
  return l;
end function;

FindTorsionBasis:=function(E0,l,f)
  P:=Random(E0);
  P1:=f*P;
  while l*P1 ne Id(E0) or P1 eq Id(E0) do
    P:=Random(E0);
    P1:=f*P;
  end while;
  repeat
    Q:=Random(E0);
    Q1:=f*Q;
    while l*Q1 ne Id(E0) or Q1 eq Id(E0) do
    Q:=Random(E0);
    Q1:=f*Q;
    end while;
  until IsLinearlyIndependent(Q1,P1,l);
  return P1,Q1;
end function;
FindPowerTorsionBasis:=function(E0,l,e,f)
  P:=Random(E0);
  P1:=f*P;
  while l^e*P1 ne Id(E0) or l^Floor(e-1)*P1 eq Id(E0) do
    P:=Random(E0);
    P1:=f*P;
  end while;
  repeat
    Q:=Random(E0);
    Q1:=f*Q;
    while l^e*Q1 ne Id(E0) or l^Floor(e-1)*Q1 eq Id(E0) do
    Q:=Random(E0);
    Q1:=f*Q;
    end while;
  until IsLinearlyIndependent(Q1,P1,l^e);
  return P1,Q1;
end function;
xDBL:=function(P,A)
  v1:=P[1]+P[2];
  v1:=v1^2;
  v2:=P[1]-P[2];
  v2:=v2^2;
  x2:=v1*v2;
  v1:=v1-v2;
  v3:=(A+2)*v1/4;
  v3:=v3+v2;
  v3*:=v1;
  if v3 eq 0 then
    return [0,0];
  end if;
  return [x2/(v3),1];
end function;
xADD:=function(P,Q,PmQ,A)
  if P eq [0,0] then
    return Q;
  elif Q eq [0,0] then
    return P;
  elif PmQ eq [0,0] then
    return xDBL(P,A);
  end if;
  v0:=P[1]+P[2];
  v1:=Q[1]-Q[2];
  v1:=v1*v0;
  v0:=P[1]-P[2];
  v2:=Q[1]+Q[2];
  v2:=v2*v0;
  v3:=v1+v2;
  v3:=v3^2;
  v4:=v1-v2;
  v4:=v4^2;
  v4*:=PmQ[1];
  if v4 eq 0 then
    return [0,0];
  end if;
  return [v3/(v4),1];
end function;




Ladder:=function(m,x,A)
  if m eq 0 then
    return [0,0];
  end if;
  k:=Floor(Log(m)/Log(2));
  mtemp:=m-2^k;
  x0:=x;
  x1:=xDBL(x,A);
  for i in [1..(k)] do
    bin:=2^(k-i);
    if mtemp ge bin then
      x0:=xADD(x0,x1,x,A);
      x1:=xDBL(x1,A);
      mtemp-:=bin;
    else
      x1:=xADD(x0,x1,x,A);
      x0:=xDBL(x0,A);
    end if;
  end for;
  return x0,x1;
end function;
TwoDimLadder:=function(m,P,n,Q,PmQ,A)
  s0:=m;
  s1:=n;
  x0:=P;
  x1:=Q;
  xm:=PmQ;
  while s0 ne 0 do
    if not s0 le s1 then
      st:=s0;xt:=x0;s0:=s1;x0:=x1;s1:=st;x1:=xt;
    end if;
    if s1 le 4*s0 then
      s1:=s1-s0;
      xt:=x0;x0:=xADD(x1,x0,xm,A);xm:=xt;
    elif s0 mod 2 eq s1 mod 2 then
      s1:=Integers()!((s1-s0)/2);
      x0:=xADD(x0,x1,xm,A);x1:=xDBL(x1,A);
    elif s1 mod 2 eq 0 then
      s1:=Integers()!(s1/2);
      xm:=xADD(x1,xm,x0,A);x1:=xDBL(x1,A);
    else
      s0:=Integers()!(s0/2);
      xm:=xADD(x0,xm,x1,A);
      x0:=xDBL(x0,A);
    end if;
  end while;
  while s1 mod 2 eq 0 do
      s1:=Integers()!(s1/2);
      x1:=xDBL(x1,A);
  end while;
  if s1 ge 2 then
      x1:=Ladder(s1,x1,A);
  end if;
  return x1;
end function;
LadderPoints:=function(l,P,A)
  if l eq 1 then
    return [P];
  end if;
  points:=[P,xDBL(P,A)];
  for i in [3..l] do
    Append(~points,xADD(P,points[i-1],points[i-2],A));
  end for;
  return points;
end function;
FullLadder:=function(m,P,E,A)
  if P eq Id(E) then return Id(E); end if;
  xP:=[P[1],P[3]];
  x0,x1:=Ladder(m,xP,A);
  return Recover(P,x0,x1,E,A);
end function;

TestLadder:=procedure(bitsize)
  l:=4099;
  f:=Random(1,2^(256-Floor(Log(l)/Log(2))));
  p:=4*f*l-1;
  while not IsPrime(p) do
    f:=Random(1,2^(256-Floor(Log(l)/Log(2))));
    p:=4*f*l-1;
  end while;
  K:=FiniteField(p);
  K2<z>:=FiniteField(p^2);
  _<x>:=PolynomialRing(K2);
  A0:=0;
  g:=x^3+A0*x^2+x;
  E0:=EllipticCurve(g);
  Pl,Ql:=FindTorsionBasis(E0,l,4*f);
  xP:=[Pl[1],1];
  xQ:=[Ql[1],1];
  xPmQ:=[(Pl-Ql)[1],1];
  xADD(xP,xQ,xPmQ,A0)[1] eq (Pl+Ql)[1];
  xDBL(xP,A0)[1] eq (2*Pl)[1];
  for i in [1..10] do
    m:=Random(1,l-1);
    FullLadder(m,Pl,E0,A0) eq m*Pl;
  end for;
  // [point[1]: point in LadderPoints(m,xP,A0)] eq [(i*Pl)[1]: i in [1..m]];
end procedure;

smooth_part:=function(n,B);
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


// compute the discrete logarithm of Q in base P, given that P is of order l
// returns -1 if DLP does not exist
discrete_logarithm_BSGS_montgomery:=function(Q,P,QmP,A,l);
    m := Ceiling(Sqrt(l));
    mP:=Ladder(m,P,A);
    table := AssociativeArray();
    e := Zero(Parent(P[1]));
    e:=[e,e];
    et:=mP;
    for i in [0..m-1] do
        table[e] := m*i;
        ett:=e;
        e := xADD(e,mP,et,A);
        et:=ett;
    end for;
    step := P;
    e := Q;
    et:=QmP;
    for i in [0..m-1] do
        if IsDefined(table,e) then
            return - i + table[e];
        end if;
        ett:=e;
        e := xADD(e,P,et,A);
        et:=ett;
    end for;
    //"ERROR in discrete_logarithm_BSGS: logarithm does not exist";
    return -1;
end function;
TestBSGS:=procedure(bitsize)
  l:=4099;
  f:=Random(1,2^(256-Floor(Log(l)/Log(2))));
  p:=4*f*l-1;
  while not IsPrime(p) do
    f:=Random(1,2^(256-Floor(Log(l)/Log(2))));
    p:=4*f*l-1;
  end while;
  K:=FiniteField(p);
  K2<z>:=FiniteField(p^2);
  _<x>:=PolynomialRing(K2);
  A0:=0;
  g:=x^3+A0*x^2+x;
  E0:=EllipticCurve(g);
  Pl,Ql:=FindTorsionBasis(E0,l,4*f);
  xP:=[Pl[1],1];
  xQ:=[Ql[1],1];

  r:=Random(1,l-1);
  R:=Ladder(r mod l,xP,A0);
  RmP:=Ladder(r-1 mod l,xP,A0);
  rt:=discrete_logarithm_BSGS_montgomery(R,xP,RmP,A0,l);
  R eq Ladder(rt mod l,xP,A0);
end procedure;
// TestBSGS(256);
// compute the discrete logarithm of Q in base P, given that P is of order l^n
// returns -1 if DLP does not exist
discrete_logarithm_power_montgomery:=function(Q,P,PmQ,l,n,A);
  log := 0;

  Ps := [P : i in [1..n]];
  // Ps[1] := P;
  for i in [2..n] do
    Ps[i] := Ladder(l,Ps[i-1],A);
  end for;

  h := Q;
  dif:=PmQ;
  for i in [0..n-1] do

    // hi := (l^(n-1-i))*h;
    // hi:=Ladder(l^(n-1-i),h,A);
    hi:=TwoDimLadder(l^(n-i-1),Q,(-l^(n-i-1)*log) mod l^n,P,PmQ,A);
    difi:=TwoDimLadder(l^(n-i-1),Q,(-l^(n-i-1)*log - l^(n-1)) mod l^n,P,PmQ,A);
    // difi:=TwoDimLadder(l^(n-1-i),h,(-l^(n-1)) mod l^n,P,dif,A);
    // difi:=Ladder(l^(n-1-i),dif,A);
    // hi;
    // difi;
    ai := discrete_logarithm_BSGS_montgomery(hi,Ps[n],difi,A,l);
    if ai ne -1 then
      // ai;
      Ladder(ai,Ps[n],A) eq hi;
    end if;
    if ai eq -1 then return -1; end if;
    log +:= (l^i)*ai;
    // h := h - ai*Ps[i+1];
    // ht:=h;
    h:=TwoDimLadder(1,Q,(-log) mod l^n,P,PmQ,A);
    // ai;
    if Ladder(l^(n-1-i),h,A) ne [0,0] then
      log -:= (l^i)*ai;
      ai:=(-ai) mod l;
      log +:= (l^i)*ai;
      h:=TwoDimLadder(1,Q,(-log) mod l^n,P,PmQ,A);
    end if;
    // h;
    // ht;
    // dif:=TwoDimLadder(1,ht,(-ai-l) mod l^n,Ps[i+1],dif,A);
    // Ladder(l^(n-1-i),dif,A) eq Ps[n];
  end for;
  return log;
end function;
TestDLPpower:=procedure(bitsize)
  l:=7;
  e:=15;
  f:=Random(1,2^(256-Floor(e*Log(l)/Log(2))));
  p:=4*f*l^e-1;
  while not IsPrime(p) do
    f:=Random(1,2^(256-Floor(e*Log(l)/Log(2))));
    p:=4*f*l^e-1;
  end while;
  K:=FiniteField(p);
  K2<z>:=FiniteField(p^2);
  _<x>:=PolynomialRing(K2);
  A0:=0;
  g:=x^3+A0*x^2+x;
  E0:=EllipticCurve(g);
  Pl,Ql:=FindPowerTorsionBasis(E0,l,e,4*f);
  l^e;
  xP:=[Pl[1],1];
  xQ:=[Ql[1],1];

  r:=Random(1,l^e-1);
  r mod l;
  R:=Ladder(r mod l^e,xP,A0);
  RmP:=Ladder((r-1) mod l^e,xP,A0);
  rt:=discrete_logarithm_power_montgomery(R,xP,RmP,l,e,A0);
  rt;
  R eq Ladder(rt mod l^e,xP,A0);
end procedure;
// TestDLPpower(256);

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
  b1:=Q eq log*P;
  // "DLP ok:",b1;
  if not b1 then
    IsLinearlyIndependent(Q,P,l^n);
  end if;
  return log;
end function;

// compute the discrete logarithm of Q in base P, given that P is of order l
// in a multiplicative group
// returns -1 if DLP does not exist
discrete_logarithm_BSGS_mult:=function(Q,P,l);
  m := Ceiling(Sqrt(l));
  table := AssociativeArray();
  e := One(Parent(P));
  for i in [0..m-1] do
      table[e] := i;
      e := e * P;
  end for;
  step := P^(-m);
  e := Q;
  for i in [0..m-1] do
      if IsDefined(table,e) then
          return i*m + table[e];
      end if;
      e := e * step;
  end for;
  //"ERROR in discrete_logarithm_BSGS: logarithm does not exist";
  return -1;
end function;

// compute the DLP of X in <P,Q>, in an elliptic curve
DLP_dimension_2_prime_elliptic:=function(X,P1,P2,l);
  g := WeilPairing(P1,P2,l);
  w1 := WeilPairing(X,P1,l);
  beta := l-discrete_logarithm_BSGS_mult(w1,g,l);
  w2 := WeilPairing(X,P2,l);
  alpha := discrete_logarithm_BSGS_mult(w2,g,l);
  return [alpha, beta];
end function;


// compute the DLP of X in <P,Q>
DLP_dimension_2_prime:=function(X,P1,P2,l);
  if l gt 150 then
    return DLP_dimension_2_prime_elliptic(X,P1,P2,l);
  end if;

  table := AssociativeArray();
  e := ZeroPt(Parent(P1));
  for i in [0..l-1] do
      table[e] := i;
      // table[e]*P1 eq e;
      e := e + P1;
  end for;
  step := P2;
  e := X;
  for i in [0..l-1] do
      if IsDefined(table,e) then
          return [table[e], -i mod l];
      end if;
      e := e + step;
  end for;

  "ERROR in DLP_dimension_2_prime: logarithm does not exist";
  return [];
end function;

DLP_dimension_2_prime_old:=function(X,P1,P2,l);

  b := discrete_logarithm_BSGS(X,P2,l);
  // X == b*Q;
  if (b ne -1) then
    return [0, b];
  end if;
  for a in [0..l-1] do
    b := discrete_logarithm_BSGS(X,P1+a*P2,l);
    // X == b*(P+a*Q);
    if (b ne -1) then
      return [b, b*a mod l];
    end if;
  end for;
  "ERROR in DLP_dimension_2_prime: logarithm does not exist";
  return [];
end function;

//useless (same complexity as DLP_dimension_2_prime) but differently
DLP_dimension_2_linear:=function(X,P1,P2,l)
  m := Ceiling(Sqrt(l));
    table := AssociativeArray();
    e := ZeroPt(Parent(P1));
    for i in [0..m-1] do
      et:=e;
      for j in [0..m-1] do
        table[et] := <i,j>;
        et := et + P2;
      end for;
      e:=e+P1;
    end for;
    stepi := (-m)*P1;
    stepj := (-m)*P2;
    e := X;
    for i in [0..m-1] do
      et:=e;
      for j in [0..m-1] do
        if IsDefined(table,et) then
            tab:=table[et];
            return [i*m + tab[1] mod l,j*m+tab[2] mod l];
        end if;
        et := et + stepj;
      end for;
      e:= e + stepi;
    end for;
    "ERROR in DLP_dimension_2_linear: logarithm does not exist";
    return [];
end function;

// compute the DLP of X in <P,Q>
DLP_dimension_2_power:=function(X,P1,P2,l,n)
  log := [0,0];
  // if not IsIsomorphic(Parent(X),Parent(P1)) or not IsIsomorphic(Parent(X),Parent(P2)) then
  //   Parent(X);
  //   Parent(P1);
  //   Parent(P2);
  // end if;
  // IsIsomorphic(Parent(X),Parent(P1));
  // Parent(X)`A eq -Parent(P2)`A;

  Ps1 := [P1];
  Ps2 := [P2];
  // Ps2[1] := P2;
  for i in [2..n] do
    // Ps1[i] := l*Ps1[i-1];
    // Ps2[i] := l*Ps2[i-1];
    Append(~Ps1,l*Ps1[#Ps1]);
    Append(~Ps2,l*Ps2[#Ps2]);
  end for;
  h := X;
  for i in [0..n-1] do
    hi := (l^(n-1-i))*h;
    ai := DLP_dimension_2_prime(hi,Ps1[n],Ps2[n],l);
    if ai eq [] then return []; end if;
    log[1] +:= (l^i)*ai[1];
    log[2] +:= (l^i)*ai[2];
    h := h - ai[1]*Ps1[i+1] - ai[2]*Ps2[i+1];
  end for;
  return log;
end function;

DLP_dimension_2_exponent_2:=function(R,P,Q,PplusQ)
  if R eq P then
    return 1,0;
  elif R eq Q then
    return 0,1;
  elif R eq PplusQ then
    return 1,1;
  elif R eq 2*P then
    return 0,0;
  end if;
  return -1,-1;
end function;


sort_insert_timewise:=function(list,val)
  if #list eq 0 then
    return [val];
  end if;
  low:=[];
  big:=list;
  A:=big[1];
  while A`Time le val`Time and #big ne 0 do
    Append(~low,A);
    Remove(~big,1);
    if #big eq 0 then
      break;
    else
      A:=big[1];
    end if;
  end while;
  Append(~low,val);
  l:=low cat big;
  return l;
end function;
