174,0
T,Mnty,MntyPt,0
A,Mnty,4,alpha,A,B,A24
A,MntyPt,4,x,y,z,curve
S,Montgomery,Create By² = x (x - α) (x - 1/α),0,2,0,0,0,0,0,0,0,85,,0,0,85,,Mnty,-38,-38,-38,-38,-38
S,Montgomery,"convert the SmiMntyto a Mnty, with the twister of Mref",0,2,0,0,0,0,0,0,0,Mnty,,0,0,SmiMnty,,Mnty,-38,-38,-38,-38,-38
S,Montgomery,construct the curve from M and with twisting parameter B,0,2,0,0,0,0,0,0,0,85,,0,0,SmiMnty,,Mnty,-38,-38,-38,-38,-38
S,Montgomery,return M,0,2,0,0,0,0,0,0,0,85,,0,0,Mnty,,Mnty,-38,-38,-38,-38,-38
S,Montgomery,construct the curve from M on which P using potentially twister as twisting parameter,0,3,0,0,0,0,0,0,0,85,,0,0,SmiMntyXZ,,0,0,SmiMnty,,Mnty,-38,-38,-38,-38,-38
S,MontgomeryA,"Compute the montgomery curve from A, alpha is set to zero in this case",0,2,0,0,0,0,0,0,0,85,,0,0,85,,Mnty,-38,-38,-38,-38,-38
S,QuadraticTwist,construct the quadratic twist of M,0,2,0,0,0,0,0,0,0,85,,0,0,Mnty,,Mnty,-38,-38,-38,-38,-38
S,Print,Print M,0,1,0,0,1,0,0,0,0,Mnty,,-38,-38,-38,-38,-38,-38
S,jInvariant,The j-invariant of M,0,1,0,0,0,0,0,0,0,Mnty,,85,-38,-38,-38,-38,-38
S,IsIsomorphic,assert if the two curves are isomorphic,0,2,0,0,0,0,0,0,0,Mnty,,0,0,Mnty,,36,-38,-38,-38,-38,-38
S,EllipticCurve,Magma's native elliptic curve object from this curve,0,1,0,0,0,0,0,0,0,Mnty,,334,-38,-38,-38,-38,-38
S,Isomorphism,"compute the isomorphism between the two curves, the output is [r,s,t,u]",0,2,0,0,0,0,0,0,0,Mnty,,0,0,Mnty,,func,-38,-38,-38,-38,-38
S,ApplyIsom,"apply isom = [r,s,t,u] on the point P",1,0,1,82,0,85,3,0,0,0,0,0,0,0,MntyPt,,0,0,Mnty,,0,0,82,,MntyPt,-38,-38,-38,-38,-38
S,ApplyIsom,"apply isom = [r,s,t,u] on the point P",1,0,1,82,0,85,3,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,Mnty,,0,0,82,,SmiMntyXZ,-38,-38,-38,-38,-38
S,ApplyIsom,"apply isom = [r,s,t,u] on the point P",1,0,1,82,0,85,3,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,SmiMnty,,0,0,82,,SmiMntyXZ,-38,-38,-38,-38,-38
S,WeierstrassForm,Convert a point P to its equivalent on E the weierstrass curve equivalent to the curve of P,0,1,0,0,0,0,0,0,0,MntyPt,,372,-38,-38,-38,-38,-38
S,MontgomeryPt,Convert back P to the montgomery point,0,2,0,0,0,0,0,0,0,372,,0,0,Mnty,,MntyPt,-38,-38,-38,-38,-38
T,SmiMnty,SmiMntyXZ,0
A,SmiMnty,3,alpha,A,A24
A,SmiMntyXZ,3,X,Z,curve
S,SemiMontgomery,Create y² = x (x - α) (x - 1/α),0,1,0,0,0,0,0,0,0,85,,SmiMnty,-38,-38,-38,-38,-38
S,SemiMontgomery,return M,0,1,0,0,0,0,0,0,0,SmiMnty,,SmiMnty,-38,-38,-38,-38,-38
S,SemiMontgomeryA,"compute the montgomery curve By² =x(x²+Ax+1) without computing alpha, this is to avoid computing unnecessary square roots during two isogenies",0,1,0,0,0,0,0,0,0,85,,SmiMnty,-38,-38,-38,-38,-38
S,SemiMontgomery,Return the semi-montgomery curve associated with M,0,1,0,0,0,0,0,0,0,Mnty,,SmiMnty,-38,-38,-38,-38,-38
S,RecoverAlpha,Recover the coefficient alpha when it is set to 0,0,1,0,0,0,0,0,0,0,SmiMnty,,SmiMnty,-38,-38,-38,-38,-38
S,RecoverAlpha,add the knowledge of alpha to the curve,0,2,0,0,0,0,0,0,0,85,,0,0,SmiMnty,,SmiMnty,-38,-38,-38,-38,-38
S,RecoverAlphaSpecialCase,"this is when A2 is computed from A1 as the arrival curve of the isogeny of kernel (0:1), the formula allows efficient computation of alpha",0,2,0,0,0,0,0,0,0,85,,0,0,85,,SmiMnty,-38,-38,-38,-38,-38
S,Print,Print M,0,1,0,0,1,0,0,0,0,SmiMnty,,-38,-38,-38,-38,-38,-38
S,MontgomeryA,The Montgomery A coefficient,0,1,0,0,0,0,0,0,0,SmiMnty,,85,-38,-38,-38,-38,-38
S,jInvariant,The j-invariant of M,0,1,0,0,0,0,0,0,0,SmiMnty,,85,-38,-38,-38,-38,-38
S,IsIsomorphic,assert if the two curves are isomorphic,0,2,0,0,0,0,0,0,0,SmiMnty,,0,0,SmiMnty,,36,-38,-38,-38,-38,-38
S,EllipticCurve,Magma's native elliptic curve object from this curve,0,1,0,0,0,0,0,0,0,-1,,334,-38,-38,-38,-38,-38
S,Isomorphism,"compute the isomorphism between the two curves, the output is [r,s,t,u]",0,2,0,0,0,0,0,0,0,SmiMnty,,0,0,SmiMnty,,func,-38,-38,-38,-38,-38
S,SemiMontgomeryXZ,Create point on curve,0,3,0,0,0,0,0,0,0,SmiMnty,,0,0,85,,0,0,85,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Parent,Return parent curve,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,SmiMnty,-38,-38,-38,-38,-38
S,Print,Print point,0,1,0,0,1,0,0,0,0,SmiMntyXZ,,-38,-38,-38,-38,-38,-38
S,IsIdentity,says if the point is the identity,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,36,-38,-38,-38,-38,-38
S,Curve,return the curve of P,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,SmiMnty,-38,-38,-38,-38,-38
S,eq,Test equality of points,0,2,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,SmiMntyXZ,,36,-38,-38,-38,-38,-38
S,IsOnCurve,Test whether point is on curve,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,36,-38,-38,-38,-38,-38
S,IsOnTwist,Test whether point is on quadratic twist,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,36,-38,-38,-38,-38,-38
S,ZeroXZ,Point at infinity,0,1,0,0,0,0,0,0,0,SmiMnty,,SmiMntyXZ,-38,-38,-38,-38,-38
S,IsCoercible,Point of coordinates (x:1),0,2,0,0,0,0,0,0,0,-1,,0,0,SmiMnty,,36,-1,-38,-38,-38,-38
S,IsCoercible,Point of coordinates (x:1),0,2,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,SmiMnty,,36,-1,-38,-38,-38,-38
S,RandomXZ,"Random non-zero point on M if oncurve == true, on the twist otherwise",0,2,0,0,0,0,0,0,0,36,,0,0,SmiMnty,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Random,random non-zero point on M,0,1,0,0,0,0,0,0,0,SmiMnty,,SmiMntyXZ,-38,-38,-38,-38,-38
S,RandomXZ,Random non-zero point on M (or the twist),0,1,0,0,0,0,0,0,0,SmiMnty,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Normalized,Return normalized (X:1) copy of point,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Lift,"Lift the point in X,Z coordinates to the full x:y:z coordinates",0,2,0,0,0,0,0,0,0,Mnty,,0,0,SmiMntyXZ,,MntyPt,-38,-38,-38,-38,-38
S,Lift,"Lift the point P as a MntyPt on P`curve or its twist, the twisting param is twister",0,2,0,0,0,0,0,0,0,-1,,0,0,SmiMntyXZ,,MntyPt,-38,-38,-38,-38,-38
S,Lift,The two points (X:Y:1) in E above P,0,2,0,0,0,0,0,0,0,334,,0,0,SmiMntyXZ,,372,-38,-38,-38,-38,-38
S,Double,Double point,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,SmiMntyXZ,-38,-38,-38,-38,-38
S,XAdd,Differential addition P + Q,0,3,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,SmiMntyXZ,,0,0,SmiMntyXZ,,SmiMntyXZ,-38,-38,-38,-38,-38
S,*,Montgomery ladder,0,2,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,148,,SmiMntyXZ,-38,-38,-38,-38,-38
S,*,Montgomery ladder,0,2,0,0,0,0,0,0,0,148,,0,0,SmiMntyXZ,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Ladder,Montgomery ladder with both point in output,0,2,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,148,,SmiMntyXZ,SmiMntyXZ,-38,-38,-38,-38
S,MontgomeryPt,create a point on M,0,4,0,0,0,0,0,0,0,Mnty,,0,0,85,,0,0,85,,0,0,85,,MntyPt,-38,-38,-38,-38,-38
S,Parent,return the parent of the point,0,1,0,0,0,0,0,0,0,MntyPt,,Mnty,-38,-38,-38,-38,-38
S,Print,Print point,0,1,0,0,1,0,0,0,0,MntyPt,,-38,-38,-38,-38,-38,-38
S,IsOnCurve,confirm that the point is indeed on its curve,0,1,0,0,0,0,0,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,IsOnCurve,confirm that the point is on the given curve M,0,2,0,0,0,0,0,0,0,Mnty,,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,IsIdentity,says if the point is the identity,0,1,0,0,0,0,0,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,Curve,return the curve of P,0,1,0,0,0,0,0,0,0,MntyPt,,Mnty,-38,-38,-38,-38,-38
S,eq,Test equality of points,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,Normalized,Return normalized (x:y:1) copy of point,0,1,0,0,0,0,0,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,ZeroPt,Point at infinity,0,1,0,0,0,0,0,0,0,Mnty,,MntyPt,-38,-38,-38,-38,-38
S,IsCoercible,Point of coordinates (x:y:1),0,3,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,Mnty,,36,-1,-38,-38,-38,-38
S,IsCoercible,Coerce P in M,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,Mnty,,36,-1,-38,-38,-38,-38
S,IsTwistPoint,check if the point is on the twist of the curve,0,1,0,0,0,0,0,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,Project,return the projection of P on (X:Z) on the SmiMnty curve obtained from the curve of P,0,1,0,0,0,0,0,0,0,MntyPt,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Project,return P,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,SmiMntyXZ,-38,-38,-38,-38,-38
S,Recover,recover the full coordinates of Q given information on the P+Q for some P,0,3,0,0,0,0,0,0,0,SmiMntyXZ,,0,0,SmiMntyXZ,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,RandomPt,Random non-zero point on M,0,1,0,0,0,0,0,0,0,Mnty,,MntyPt,-38,-38,-38,-38,-38
S,Random,random non-zero point on M,0,1,0,0,0,0,0,0,0,Mnty,,MntyPt,-38,-38,-38,-38,-38
S,Lift,return P,0,2,0,0,0,0,0,0,0,-1,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,-,return -P,0,1,0,0,0,0,0,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,+,point addition,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,-,return P-Q,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,*,return n*P,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,148,,MntyPt,-38,-38,-38,-38,-38
S,*,return n*P,0,2,0,0,0,0,0,0,0,148,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,IsLinearlyIndependent,return true if P and Q of ln torsion are linearly independant,0,3,0,0,0,0,0,0,0,148,,0,0,MntyPt,,0,0,MntyPt,,36,-38,-38,-38,-38,-38
S,DivisionPoint,compute one division point Q of P such that P = n*Q,0,2,0,0,0,0,0,0,0,148,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,DivisionPoints,compute one division point Q of P such that P = n*Q,0,2,0,0,0,0,0,0,0,148,,0,0,MntyPt,,MntyPt,-38,-38,-38,-38,-38
S,WeilPairing,"compute the weil pairing of P,Q points of l torsion",0,3,0,0,0,0,0,0,0,148,,0,0,MntyPt,,0,0,MntyPt,,85,-38,-38,-38,-38,-38
S,Log,use magma type to compute DLP,0,2,0,0,0,0,0,0,0,MntyPt,,0,0,MntyPt,,148,-38,-38,-38,-38,-38
