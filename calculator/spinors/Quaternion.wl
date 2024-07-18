(* ::Package:: *)

<<Quaternions`
MatrixProduct[{{a_,b_},{c_,d_}},{{e_,f_},{g_,h_}}]:={{a**e+b**g,a**f+b**h},{c**e+d**g,c**f+d**h}}
MatrixProduct[a_,b_,c__]:=MatrixProduct[MatrixProduct[a,b],c]
AntiCommute[x_,y_]:=MatrixProduct[x,y]+MatrixProduct[y,x]
Commute[x_,y_]:=MatrixProduct[x,y]-MatrixProduct[y,x]
FullSimplifyQ[a_]:=If[QuaternionQ[#],FromQuaternion[#],#]&/@FullSimplify[Flatten[a]]
To22[exp_]:=ArrayReshape[exp,{2,2}]
\[Sigma]0=PauliMatrix[0];
\[Sigma]1=PauliMatrix[1];
\[Sigma]2=PauliMatrix[2];
\[Sigma]3=PauliMatrix[3];
ToPauli[exp_]:=ArrayFlatten[exp//.Quaternion[a_Integer,b_Integer,c_Integer,d_Integer]:>a \[Sigma]0-I b \[Sigma]1-I c \[Sigma]2-I d \[Sigma]3]


(* ::Section:: *)
(*Geometric Algebra R(1,3)*)


II=Quaternion[0,1,0,0];
JJ=Quaternion[0,0,1,0];
KK=Quaternion[0,0,0,1];
II**JJ==KK
ToPauli[II] . ToPauli[II]
ToPauli[JJ] . ToPauli[JJ]
ToPauli[KK] . ToPauli[KK]
ToPauli[II] . ToPauli[JJ]==ToPauli[KK]
ToPauli[JJ] . ToPauli[KK]==ToPauli[II]
ToPauli[KK] . ToPauli[II]==ToPauli[JJ]


G0={{Quaternion[1,0,0,0],0},{0,-Quaternion[1,0,0,0]}};
G1={{0,II},{II,0}};
G2={{0,JJ},{JJ,0}};
G3={{0,KK},{KK,0}};
PS=MatrixProduct[G0,G1,G2,G3]
MatrixProduct[G0,G0]//FullSimplifyQ//To22
MatrixProduct[G1,G1]//FullSimplifyQ//To22
MatrixProduct[G2,G2]//FullSimplifyQ//To22
MatrixProduct[G3,G3]//FullSimplifyQ//To22
AntiCommute[G1,G0]//FullSimplifyQ//To22
AntiCommute[G1,G2]//FullSimplifyQ//To22
AntiCommute[G2,G0]//FullSimplifyQ//To22
AntiCommute[G3,G0]//FullSimplifyQ//To22
AntiCommute[G2,G3]//FullSimplifyQ//To22
AntiCommute[G3,G1]//FullSimplifyQ//To22


MatrixProduct[PS,PS]//FullSimplifyQ//To22
AntiCommute[PS,G0]//FullSimplifyQ//To22
AntiCommute[PS,G1]//FullSimplifyQ//To22
AntiCommute[PS,G2]//FullSimplifyQ//To22
AntiCommute[PS,G3]//FullSimplifyQ//To22


Commute[G0,G1]//FullSimplifyQ//To22
Commute[G0,G2]//FullSimplifyQ//To22
Commute[G0,G3]//FullSimplifyQ//To22
Commute[G2,G3]//FullSimplifyQ//To22
Commute[G3,G1]//FullSimplifyQ//To22
Commute[G1,G2]//FullSimplifyQ//To22
MatrixProduct[G0,PS]//FullSimplifyQ//To22
MatrixProduct[G1,PS]//FullSimplifyQ//To22
MatrixProduct[G2,PS]//FullSimplifyQ//To22
MatrixProduct[G3,PS]//FullSimplifyQ//To22
PS//FullSimplifyQ//To22


R=ArrayFlatten[{{\[Sigma]0,0},{0,I \[Sigma]0}}];
Inverse[R] . ToPauli[G0] . R
Inverse[R] . ToPauli[G1] . R
Inverse[R] . ToPauli[G2] . R
Inverse[R] . ToPauli[G3] . R
R=ArrayFlatten[{{\[Sigma]0,0},{0,I \[Sigma]0}}] . ArrayFlatten[{{\[Sigma]0,\[Sigma]0},{-\[Sigma]0, \[Sigma]0}}];
Inverse[R] . ToPauli[G0] . R
Inverse[R] . ToPauli[G1] . R
Inverse[R] . ToPauli[G2] . R
Inverse[R] . ToPauli[G3] . R


(* ::Section:: *)
(*Isomorphism between R(4,1) and C4*)


G0=I({{Quaternion[1,0,0,0],0},{0,-Quaternion[1,0,0,0]}}//ToPauli)
G1=I({{0,II},{II,0}}//ToPauli)
G2=I({{0,JJ},{JJ,0}}//ToPauli)
G3=I({{0,KK},{KK,0}}//ToPauli)
G4=I G0 . G1 . G2 . G3
PS=G0 . G1 . G2 . G3 . G4
AC[a_,b_]:=a . b+b . a
Table[AC[i,j]==Which[i==j==G0,-2,i==j,2,True,0]*IdentityMatrix[4],{i,{G0,G1,G2,G3,G4}},{j,{G0,G1,G2,G3,G4}}]
PS . PS


PS . #==# . PS&/@{G0,G1,G2,G3,G4}


basis=({#,# . PS}&/@{DiagonalMatrix[{1,1,1,1}],G0,G1,G2,G3,G4,
G0 . G1,G0 . G2,G0 . G3,G0 . G4,G1 . G2,G1 . G3,G1 . G4,G2 . G3,G2 . G4,G3 . G4})//Flatten[#,1]&
ip=MapThread[Times,{basis,Table[c[i],{i,32}]}]//Total
solution=Flatten[ComplexExpand[{Re[#]==0,Im[#]==0}&/@Flatten[ip-Table[x[i,j]+I y[i,j],{i,4},{j,4}]]]]//Solve[#,Table[c[i],{i,32}]]&
ip/.solution//FullSimplify


(* ::Section:: *)
(*R(1,4)*)


(* ::Text:: *)
(*For +--- signature, R(1,4) is not isomorphic to C4*)


G0=({{Quaternion[1,0,0,0],0},{0,-Quaternion[1,0,0,0]}}//ToPauli)
G1=({{0,II},{II,0}}//ToPauli)
G2=({{0,JJ},{JJ,0}}//ToPauli)
G3=({{0,KK},{KK,0}}//ToPauli)
G4= G0 . G1 . G2 . G3
PS=G0 . G1 . G2 . G3 . G4
AC[a_,b_]:=a . b+b . a
Table[AC[i,j]==Which[i==j==G0,2,i==j,-2,True,0]*IdentityMatrix[4],{i,{G0,G1,G2,G3,G4}},{j,{G0,G1,G2,G3,G4}}]
PS . PS


basis=({#,# . PS}&/@{DiagonalMatrix[{1,1,1,1}],G0,G1,G2,G3,G4,
G0 . G1,G0 . G2,G0 . G3,G0 . G4,G1 . G2,G1 . G3,G1 . G4,G2 . G3,G2 . G4,G3 . G4})//Flatten[#,1]&
ip=MapThread[Times,{basis,Table[c[i],{i,32}]}]//Total
solution=Flatten[ComplexExpand[{Re[#]==0,Im[#]==0}&/@Flatten[ip-Table[x[i,j]+I y[i,j],{i,4},{j,4}]]]]//Solve[#,Table[c[i],{i,32}]]&


(* ::Text:: *)
(*Therefore Cl(2,3) should be a better option.*)


G0=({{Quaternion[1,0,0,0],0},{0,-Quaternion[1,0,0,0]}}//ToPauli)
G1=({{0,II},{II,0}}//ToPauli)
G2=({{0,JJ},{JJ,0}}//ToPauli)
G3=({{0,KK},{KK,0}}//ToPauli)
G4= I G0 . G1 . G2 . G3
PS=G0 . G1 . G2 . G3 . G4
AC[a_,b_]:=a . b+b . a
Table[AC[i,j]==Which[i==j==G0,2,i==j==G4,2,i==j,-2,True,0]*IdentityMatrix[4],{i,{G0,G1,G2,G3,G4}},{j,{G0,G1,G2,G3,G4}}]
PS . PS
