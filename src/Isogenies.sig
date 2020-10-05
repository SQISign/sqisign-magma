174,0
T,Isog,-,0
A,Isog,4,domain,codomain,degree,isogeny
S,Isogeny,"generate a generic object isogeny, its concrete type will depend on the degree",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SmiMntyXZ,,Isog,-38,-38,-38,-38,-38
S,Isogeny,"generate a generic object isogeny, its concrete type will depend on the degree",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,MntyPt,,Isog,-38,-38,-38,-38,-38
S,Evaluate,Evaluate the isogeny on points,1,1,1,82,0,SmiMntyXZ,2,0,0,0,0,0,0,0,82,,0,0,Isog,,82,-38,-38,-38,-38,-38
S,Evaluate,evaluate on iso on points,1,1,1,82,0,MntyPt,2,0,0,0,0,0,0,0,82,,0,0,Isog,,82,-38,-38,-38,-38,-38
S,DualIsogeny,return the Dual Isogeny,0,1,0,0,0,0,0,0,0,Isog,,Isog,-38,-38,-38,-38,-38
S,codomain,return the codomain,0,1,0,0,0,0,0,0,0,Isog,,SmiMnty,-38,-38,-38,-38,-38
S,domain,return the domain,0,1,0,0,0,0,0,0,0,Isog,,SmiMnty,-38,-38,-38,-38,-38
S,Print,print iso,0,1,0,0,1,0,0,0,0,Isog,,-38,-38,-38,-38,-38,-38
T,TwoIsog,-,0
A,TwoIsog,4,domain,codomain,kernel,dual
S,TwoIsogeny,generate the two-isogeny of kernel ker,0,1,0,0,0,0,0,0,0,SmiMntyXZ,,TwoIsog,-38,-38,-38,-38,-38
S,AdjustingAlpha,"adjust the codomain of the 2-isog so that alpha is not zero, when alpha is not known",0,1,0,0,0,0,0,0,0,Isog,,Isog,-38,-38,-38,-38,-38
S,AdjustingAlpha,adjust the codomain of the isog of degree 2 so that alpha is not zero,0,2,0,0,0,0,0,0,0,85,,0,0,Isog,,Isog,-38,-38,-38,-38,-38
S,AdjustingAlpha,same as above but with domain specified dom,0,3,0,0,0,0,0,0,0,85,,0,0,SmiMnty,,0,0,Isog,,Isog,-38,-38,-38,-38,-38
S,Print,print iso,0,1,0,0,1,0,0,0,0,TwoIsog,,-38,-38,-38,-38,-38,-38
S,DualIsogeny,return the Dual Isogeny of the given two isogeny,0,1,0,0,0,0,0,0,0,TwoIsog,,Isog,-38,-38,-38,-38,-38
T,OddSmallIsog,-,0
A,OddSmallIsog,4,domain,codomain,degree,kernel_points
T,OddBigIsog,-,0
A,OddBigIsog,4,domain,codomain,degree,isogeny
S,SmallIsogeny,Create a small isogeny of degree ell with kernel generator ker,0,2,0,0,0,0,0,0,0,148,,0,0,SmiMntyXZ,,OddSmallIsog,-38,-38,-38,-38,-38
S,BigIsogeny,create a BigIsogeny with kernel generator ker,0,2,0,0,0,0,0,0,0,148,,0,0,SmiMntyXZ,,OddBigIsog,-38,-38,-38,-38,-38
S,Print,print iso,0,1,0,0,1,0,0,0,0,OddBigIsog,,-38,-38,-38,-38,-38,-38
S,Print,print iso,0,1,0,0,1,0,0,0,0,OddSmallIsog,,-38,-38,-38,-38,-38,-38
S,Evaluate,evaluate the isogeny on points using the naive method,1,1,1,82,0,SmiMntyXZ,2,0,0,0,0,0,0,0,82,,0,0,OddSmallIsog,,82,-38,-38,-38,-38,-38
S,Evaluate,evaluate the isogeny on points using the fast method,1,1,1,82,0,SmiMntyXZ,2,0,0,0,0,0,0,0,82,,0,0,OddBigIsog,,82,-38,-38,-38,-38,-38
S,Evaluate,evaluate the isogeny on points,1,1,1,82,0,SmiMntyXZ,2,0,0,0,0,0,0,0,82,,0,0,TwoIsog,,82,-38,-38,-38,-38,-38
