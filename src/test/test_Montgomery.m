/* Test SemiMontgomery curves */
load "src/tools.m";
k<i> := ExtensionField<GF(59), i | i^2+1>;
M := SemiMontgomery(i);
/* Testing group law */
P := RandomXZ(M);
Q := 11*P;
R := 14*P;
S := 25*P;

assert XAdd(S,R,Q) eq 39*P;
assert XAdd(P,P,ZeroXZ(M)) eq 2*P;
assert XAdd(P,ZeroXZ(M),P) eq P;


M:=Montgomery(i,k!1);
P := RandomPt(M);
n1:=Random(1,1000);
n2:=Random(1,1000);
R:=n1*P;
S:=n2*P;
assert R+S eq (n1+n2)*P;
assert n2*R eq n1*S;
Q :=RandomPt(M);
R:=P+Q;
assert Q eq Recover(P,Project(Q),Project(R));

order:=5;
cofactor:=12;
repeat
  P:=cofactor*RandomPt(M);
until IsIdentity(order*P) and not IsIdentity(P);
// order:=5;
assert not IsLinearlyIndependent(P,7*P,order);
repeat
  repeat
    Q:=cofactor*RandomPt(M);
  until  IsIdentity(order*Q) and not IsIdentity(Q);
  // P in [i*Q: i in [1..order-1]];
until IsLinearlyIndependent(P,Q,order);
assert not P in [i*Q: i in [1..order-1]];
assert [1,2] eq DLP_dimension_2_power(P+2*Q,P,Q,order,1);


assert 2*P eq P+P;
assert ZeroPt(M) eq P+(-P);
assert 1*P eq P;
assert IsIdentity(0*P);
assert IsIdentity(5*P);

P:=RandomPt(M);
Q:=WeierstrassForm(P);
assert (9*P+P) eq MontgomeryPt(M,10*Q);

print "All tests passed";
