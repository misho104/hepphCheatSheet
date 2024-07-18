(* ::Package:: *)

(* ::Section:: *)
(*Clifford Algebra for R(2, 3)*)


FirstSign[m_] :=  Select[Flatten[m], # != 0&] // First // If[Re[#] != 0, Sign[#], Sign[Im[#]]]&
CNormalize[m_] := m/FirstSign[m]
Q[a_] := a . a
IsScalar[exp_, r_] := exp == DiagonalMatrix[{r, r, r, r}]
IsScalar[exp_] := exp == exp[[1, 1]] * IdentityMatrix[4]
ToScalar[exp_] := If[IsScalar[exp], exp[[1, 1]], None]
AC[a_, b_] := a . b + b . a
Commute[a_, b_] := a . b - b . a


(* ::Subsubsection:: *)
(*Definitions motivated by Quaternions*)


EE = IdentityMatrix[4];
G[0] = G0 = {{1, 0, 0,  0}, {0, 1,  0, 0}, {0,  0, -1, 0}, { 0, 0, 0, -1}};
G[1] = G1 = {{0, 0, 0, -I}, {0, 0, -I, 0}, {0, -I,  0, 0}, {-I, 0, 0,  0}};
G[2] = G2 = {{0, 0, 0, -1}, {0, 0,  1, 0}, {0, -1,  0, 0}, { 1, 0, 0,  0}};
G[3] = G3 = {{0, 0, -I, 0}, {0, 0,  0, I}, {-I, 0,  0, 0}, { 0, I, 0,  0}};
G[4] = G4 = I G0 . G1 . G2 . G3;
PS = G0 . G1 . G2 . G3 . G4;
CL0 = {EE};
CL1 = {G0, G1, G2, G3, G4};
MatrixForm /@ {G0, G1, G2, G3, G4, PS}


(* ::Input:: *)
(**)


CL2 = (Dot@@#) &/@ Subsets[CL1, {2}]; 
CL3 = (Dot@@#) &/@ Subsets[CL1, {3}]; 
CL4 = (Dot@@#) &/@ Subsets[CL1, {4}]; 
CL5 = (Dot@@#) &/@ Subsets[CL1, {5}]; 
CL = Join[CL0, CL1, CL2, CL3, CL4, CL5]; 
CLE = (CNormalize /@ Join[CL0, CL2, CL4, I CL1, I CL3, I CL5]) // DeleteDuplicates; 
CLO = (CNormalize /@ Join[CL1, CL3, CL5, I CL0, I CL2, I CL4]) // DeleteDuplicates; 
Length /@ {CL0, CL1, CL2, CL3, CL4, CL5, CL, CLE, CLO} 


(* ::Subsubsection:: *)
(*Confirm it is Clifford Algebra with I^2 = -1*)


(* ::Input:: *)
(*Table[AC[i, j] == EE * Which[*)
(*	i == j == G0||i == j == G4, 2,*)
(*	i == j,  - 2,*)
(*	True, 0*)
(*], {i, {G0, G1, G2, G3, G4}}, {j, {G0, G1, G2, G3, G4}}]*)
(*PS . PS*)


(* ::Subsection:: *)
(*Verify they consist of a basis of 4x4 matrix*)


(* ::Input:: *)
(*InnerProduct = MapThread[Times, {CL, Table[c[i], {i, 32}]}] // Total*)
(*solution = Flatten[ComplexExpand[{Re[#] == 0, Im[#] == 0} &/@ Flatten[InnerProduct - Table[x[i, j] + I y[i, j], {i, 4}, {j, 4}]]]] // Solve[#, Table[c[i], {i, 32}]]&;*)
(*InnerProduct/.solution // FullSimplify*)


(* ::Subsection:: *)
(*Dirac Representation and Chiral Representation*)


RDirac  = DiagonalMatrix[{1, 1, I, I}]
RChiral = With[{\[Sigma]0 = IdentityMatrix[2]}, RDirac . ArrayFlatten[{{\[Sigma]0, \[Sigma]0}, {-\[Sigma]0, \[Sigma]0}}]]
ToDirac[exp_] := Inverse[RDirac] . exp . RDirac
ToChiral[exp_] := Inverse[RChiral] . exp . RChiral


Gd[i_] := ToDirac[G[i]]
Gc[i_] := ToChiral[G[i]]
{CLd0, CLd1, CLd2, CLd3, CLd4, CLd5, CLd, CLdE, CLdO} = Apply[ToDirac[{##}]&,{CL0, CL1, CL2, CL3, CL4, CL5, CL, CLE, CLO},{2}];
{CLc0, CLc1, CLc2, CLc3, CLc4, CLc5, CLc, CLcE, CLcO} = Apply[ToChiral[{##}]&,{CL0, CL1, CL2, CL3, CL4, CL5, CL, CLE, CLO},{2}];

MatrixForm /@ CLd1
MatrixForm /@ CLc1
Inverse[#]==ConjugateTranspose[#] &/@ Join[CLd, CLc]


(* ::Subsection:: *)
(*Reversions etc*)


GradeInvolution[x_] :=  - Gc[2] . Conjugate[x] . Gc[2]
Reversion[x_] := Gc[1] . Gc[3] . Transpose[x] . Gc[3] . Gc[1]
CConjugate[x_] := Gc[4] . Gc[0] . ConjugateTranspose[x] . Gc[0] . Gc[4]
tAd[x_] := Function@@Simplify[{x$, GradeInvolution[x] . x$ . Inverse[x]}]

GradeInvolutionD[x_] :=  - Gd[2] . Conjugate[x] . Gd[2]
ReversionD[x_] := Gd[1] . Gd[3] . Transpose[x] . Gd[3] . Gd[1]
CConjugateD[x_] := Gd[4] . Gd[0] . ConjugateTranspose[x] . Gd[0] . Gd[4]
tAdD[x_] := Function@@Simplify[{x$, GradeInvolutionD[x] . x$ . Inverse[x]}]


Tester[operation_,{matrices_, sign_}]:=(operation[#]==sign * #)& /@ matrices
Tester[GradeInvolution, #] &/@ Transpose[{{CLc0, CLc1, CLc2, CLc3, CLc4, CLc5}, {1, -1, 1, -1, 1, -1}}] // Flatten // (And@@#)&
Tester[Reversion, #]       &/@ Transpose[{{CLc0, CLc1, CLc2, CLc3, CLc4, CLc5}, {1, 1, -1, -1, 1,  1}}] // Flatten // (And@@#)&
Tester[CConjugate, #]      &/@ Transpose[{{CLc0, CLc1, CLc2, CLc3, CLc4, CLc5}, {1, -1, -1, 1, 1, -1}}] // Flatten // (And@@#)&
Tester[GradeInvolutionD, #] & /@ Transpose[{{CLd0, CLd1, CLd2, CLd3, CLd4, CLd5}, {1, -1, 1, -1, 1, -1}}] // Flatten // (And @@ #) &
Tester[ReversionD, #]       & /@ Transpose[{{CLd0, CLd1, CLd2, CLd3, CLd4, CLd5}, {1, 1, -1, -1, 1,  1}}] // Flatten // (And @@ #) &
Tester[CConjugateD, #]      & /@ Transpose[{{CLd0, CLd1, CLd2, CLd3, CLd4, CLd5}, {1, -1, -1, 1, 1, -1}}] // Flatten // (And @@ #) &


(* ::Subsection:: *)
(*Twisted Adjoint*)


(* ::Input:: *)
(*Table[tAd[i][j] == If[i == j, -j, j], {i, CLc1}, {j, CLc1}]*)
(*Table[MemberQ[CLc1,tAd[x][j]]||MemberQ[-CLc1,tAd[x][j]], {x, CL}, {j, CLc1}]*)


(* ::Subsection:: *)
(*Spinor*)


ToProject[exp_] := {1, -1, -1, -1, 1} * Simplify[ToScalar[exp . #+# . exp]/2 &/@ CLc1]
ToVector[{a_,b_,c_,d_,e_}] := {a, b, c, d, e} . CLc1
RepIP[v1_, v2_] := ToScalar[Simplify[AC[v1, v2]/2]]
RepN[v1_,v2_] := ToScalar[Simplify[ComplexExpand[CConjugate[v1] . v2+CConjugate[v2] . v1]/2]]


(* ::Input:: *)
(*ToProject[ToVector[{a,b,c,d,e}]]*)


Gc[3] . Gc[0]//MatrixForm


ToScalar[# . #]&/@CL1


even=ToVector[{a,b,c,d,e}]
even . even//Simplify


MatrixSqrt[x_] := Module[{p = Transpose[Normalize /@ Eigenvectors[x]]},
  p . SQ[Inverse[p] . x . p] . Inverse[p]]
SQ[{a_,b_,c_,d_}]:=SQ/@{a,b,c,d}
SQ[a_Integer/;a>=0] := Sqrt[a]
SQ /: SQ[x_]^2 := x
p0 = MatrixSqrt[Gc[0]];
p1 = MatrixSqrt[Gc[1]];
p2 = MatrixSqrt[Gc[2]];
p3 = MatrixSqrt[Gc[3]];
p5 = MatrixSqrt[Gc[4]];
p0 . p0==Gc[0]//FullSimplify
p1 . p1==Gc[1]//FullSimplify
p2 . p2==Gc[2]//FullSimplify
p3 . p3==Gc[3]//FullSimplify
p5 . p5==Gc[4]//FullSimplify


p1=Sum[k[i]CLc[[i]],{i,16}]/.k[1|6]->0;
pp=p1 . ConjugateTranspose[p1] . Gc[0]//ComplexExpand;
p2=Sum[A[i]CLc1[[i]],{i,4}];
tester=Tr[AC[pp-p2, #]]&/@ CLc[[1;;32]]/16//Simplify;
CExpand[exp_]:=ComplexExpand[{Re[exp], Im[exp]}]//Simplify;
ct = CExpand[tester]//Flatten//Simplify//DeleteDuplicates;
ct2 = ct /. First[Solve[#==0&/@ct[[{2,3,4,5}]], {k[2],k[3],k[4],k[5]}]]//.{k[10]->(A[1] k[13])/A[2],k[13]->(A[2] k[16])/A[4],k[15]->(A[3] k[16])/A[4],k[16]->0,k[7|8|9|11|12|14]->0}//Simplify
Table[k[i],{i,2,5}] /. First[Solve[#==0&/@ct[[{2,3,4,5}]], {k[2],k[3],k[4],k[5]}]]//.{k[10]->(A[1] k[13])/A[2],k[13]->(A[2] k[16])/A[4],k[15]->(A[3] k[16])/A[4],k[16]->0,k[7|8|9|11|12|14]->0}//FullSimplify;
%/.A[1]^2->e^2+A[2]^2+A[3]^2+A[4]^2//Simplify[#,e>0]&
Sqrt[-e+A[1]]*%


\[Psi] = 1/Sqrt[2(A[1]-e)] {A[1]-e,A[2],A[3],A[4]} . {Gc[0],Gc[1],Gc[2],Gc[3]} ;
\[Psi] . ConjugateTranspose[\[Psi]] . Gc[0] == p2 // ComplexExpand // Simplify[#, {e^2==A[1]^2-A[2]^2-A[3]^2-A[4]^2,e<=A[1]}]&


TeXForm[Sqrt[2(A[1]-e)]\[Psi]]


(* ::Input:: *)
(**)


p1


tester


pp


pp


p1 = Sqrt[e/2] (IdentityMatrix[4] + 1/e {A[1], A[2], A[3], A[4], 0} . CLc1)
p1 . p1 - Sum[A[i]CLc1[[i]],{i,4}]//FullSimplify//Together





vv=ToVector[{Sqrt[1+b^2+c^2+d^2],b,c,d,0}]


Gc[0] . vv . Gc[0]-ConjugateTranspose[vv]//ComplexExpand



vv=ToVector[{a,b,c,d,0}]
Conjugate[vv] == Gc[2] . vv . Gc[2] // ComplexExpand
Transpose[vv] == Gc[1] . Gc[3] . vv . Gc[3] . Gc[1] // ComplexExpand
ConjugateTranspose[vv] == Gc[0] . vv . Gc[0] // ComplexExpand



Gc[#[[1]]] . Gc[#[[2]]]&/@Subsets[{0,1,2,3},{2}]
MatrixForm/@%


MatrixForm[1/-I Gc[1] . Gc[2]]
