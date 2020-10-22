(* ::Package:: *)

(* ::Section:: *)
(*Non-matrix case*)


(* ::Text:: *)
(*We first consider non-matrix case, which can be used later as a validation.*)
(*The neutrino mass matrix can be given by {{0,\[Epsilon]},{\[Epsilon],1}}, with \[Epsilon]=m/M, and it is AT-factorized by some unitary matrix U.*)


U={{1-\[Epsilon]^2/2+11\[Epsilon]^4/8,\[Epsilon]-3\[Epsilon]^3/2+31\[Epsilon]^5/8},{-\[Epsilon]+3\[Epsilon]^3/2-31\[Epsilon]^5/8,1-\[Epsilon]^2/2+11\[Epsilon]^4/8}};
Print["U (up to \[Epsilon]^5)="];
U//MatrixForm
Print["Factorization: \!\(\*SuperscriptBox[\(U\), \(T\)]\)MU="];
Transpose[U].{{0,\[Epsilon]},{\[Epsilon],1}}.U//Expand//Series[#,{\[Epsilon],0,6}]& // MatrixForm
Print["Unitarity: \!\(\*SuperscriptBox[\(U\), \(\[Dagger]\)]\)U= (assuming real \[Epsilon])"];
Transpose[U].U//Expand//Series[#,{\[Epsilon],0,6}]& // MatrixForm


(* ::Text:: *)
(*U is close to MatrixExp of epsilons but only up to 2nd order:*)


MatrixExp[{{0,\[Epsilon]},{-\[Epsilon],0}}]//Series[#,{\[Epsilon],0,6}]&//MatrixForm


(* ::Section:: *)
(*Matrix case*)


(* ::Text:: *)
(*We need some machinery to treat submatrices:*)


SubmatrixProduct[a_,b_,c__]:=Module[{x=SubmatrixProduct[a,b]},SubmatrixProduct[x,c]];
SubmatrixProduct[a_,b_]:=Dot[Map[1,a,{2}], Map[2,b,{2}]]/.{1[x_]2[y_]:>x.y}


Unprotect[Dot,Trans,Dag,Inv];
Dot[x1___,Times[a_,b__],x2___]/;Length[{x1,x2}]>0:=Dot[x1,a,Times[b],x2]
Dot[x1___,Plus[a_,b__],x2___]:=Dot[x1,a,x2]+Dot[x1,Plus[b],x2]
Dot[x1___,a:(_Real|_Complex|_Integer|_Rational),x2___]/;Length[{x1,x2}]>0:=a Dot[x1,x2]

Trans[Trans[a_] ]:= a
Dag  [Dag  [a_]] := a

Trans[Dot[a_,b_]] := Trans[b].Trans[a]
Dag  [Dot[a_,b_]] := Dag[b].Dag[a]

Trans[a_+b_] := Trans[a]+Trans[b]
Dag  [a_+b_] := Dag[a]+Dag[b]

Dag[n_ a_]   /; NumericQ[n] := Conjugate[n] Dag[a]
Trans[n_ a_] /; NumericQ[n] := n Trans[a]

Trans[Inv[a_]] := Inv[Trans[a]]
Dag  [Inv[a_]] := Inv[Dag[a]]
Trans[Dag[a_]] := Dag[Trans[a]]

Inv/:Dot[a___,c_,Inv[c_],b___]:=Dot[a,1,b]
Inv/:Dot[a___,Inv[c_],c_,b___]:=Dot[a,1,b]

Trans[1]=1;
Dag[1]=1;

Protect[Dot,Trans,Dag,Inv];


(* ::Text:: *)
(*Evaluate in perturbation of MD. Up to second order,*)


Trans[MN]^:=MN
M0={{0,Trans[MD]},{MD,MN}};
U={{1-Dag[MD].Inv[Dag[MN]].Inv[MN].MD/2,Dag[MD].Inv[Dag[MN]]},{-Inv[MN].MD,1-Inv[MN].MD.Dag[MD].Inv[Dag[MN]]/2}};
UT=Map[Trans,Transpose[U],{2}];
UD=Map[Dag,Transpose[U],{2}];

Print["U ="];
MatrixForm[U]
Print["Factorization: \!\(\*SuperscriptBox[\(U\), \(T\)]\)MU="];
SubmatrixProduct[UT,M0,U]
%/.{Dot[a__]/;FreeQ[{a},Plus]&&Count[a,MD,-1]>2:>0}
Print["Unitarity: \!\(\*SuperscriptBox[\(U\), \(\[Dagger]\)]\)U="];
SubmatrixProduct[U,UD]
%/.{Dot[a__]/;FreeQ[{a},Plus]&&Count[a,MD,-1]>2:>0}


(* ::Text:: *)
(*Third order,*)


U={{1-Dag[MD].Inv[Dag[MN]].Inv[MN].MD/2,Dag[MD].Inv[Dag[MN]]+A3},{-Inv[MN].MD+B3,1-Inv[MN].MD.Dag[MD].Inv[Dag[MN]]/2}} /.{
  B3->1/2 Inv[MN].MD.Dag[MD].Inv[Dag[MN]].Inv[MN].MD+Inv[MN].Inv[Trans[Dag[MN]]].Trans[Dag[MD]].Trans[MD].Inv[MN].MD,
  A3->-Dag[MD].Inv[Dag[MN]].Dag[Trans[MD]].Dag[Trans[Dag[MD]]].Inv[Dag[Trans[Dag[MN]]]].Inv[Dag[MN]]-1/2 Dag[MD].Inv[Dag[MN]].Inv[MN].MD.Dag[MD].Inv[Dag[MN]]
};

UT=Map[Trans,Transpose[U],{2}];
UD=Map[Dag,Transpose[U],{2}];

Print["U ="];
MatrixForm[U]
Print["Factorization: \!\(\*SuperscriptBox[\(U\), \(T\)]\)MU="];
SubmatrixProduct[UT,M0,U]
Diag=%/.{a_Dot/;FreeQ[{a},Plus]&&Count[a,MD,-1]>3:>0}
Print["Unitarity: \!\(\*SuperscriptBox[\(U\), \(\[Dagger]\)]\)U="];
SubmatrixProduct[U,UD]
%/.{Dot[a__]/;FreeQ[{a},Plus]&&Count[a,MD,-1]>3:>0}


(* ::Input:: *)
(**)


(* ::Text:: *)
(*A nice expression with \[CapitalTheta]. The result is also compared with the non-matrix case:*)


U//.{Dag[MD]->SuperDagger[MD],Inv[MN]->\!\(\*SuperscriptBox[\(MN\), \("\<-1\>"\)]\),Inv[Dag[MN]]->\!\(\*SuperscriptBox[\(MN\), \("\<*-1\>"\)]\)}//MatrixForm
U//.{
  MD->-MN.\[CapitalTheta],
  Dag[\[CapitalTheta]]->SuperDagger[\[CapitalTheta]]
}//MatrixForm

Diag//.{Dag[MD]->SuperDagger[MD],Inv[MN]->\!\(\*SuperscriptBox[\(MN\), \("\<-1\>"\)]\),Inv[Dag[MN]]->\!\(\*SuperscriptBox[\(MN\), \("\<*-1\>"\)]\),Trans[MD]->\!\(\*SuperscriptBox[\(MD\), \("\<T\>"\)]\),Dag[Trans[MD]]->\!\(\*SuperscriptBox[\(MD\), \("\<*\>"\)]\)}//MatrixForm

U//.{MN->m,MD->\[Epsilon] m,(Dag|Trans)[x:m|\[Epsilon]|\[Epsilon] m]:>x, Inv[x:m|\[Epsilon]|\[Epsilon] m]:>1/x,Dot[a___, x:\[Epsilon]|m|1/m,b___]:>x Dot[a,b]}
Diag//.{MN->m,MD->\[Epsilon] m,(Dag|Trans)[x:m|\[Epsilon]|\[Epsilon] m]:>x, Inv[x:m|\[Epsilon]|\[Epsilon] m]:>1/x,Dot[a___, x:\[Epsilon]|m|1/m,b___]:>x Dot[a,b]}



