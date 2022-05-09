(* ::Package:: *)

(* :Time-Stamp: <2022-5-2 11:05:47> *)
(* :Package Version: 0.0.1 *)

(* :Title: Dirac Spinor Calculator *)
(* :Context: DiracAlgebra` *)
(* :Mathematica Version: "13+" *)

(* :Author: Sho Iwamoto / Misho *)
(* :Copyright: 2022 Sho Iwamoto / Misho *)

(* This file is licensed under the Apache License, Version 2.0.
   You may not use this file except in compliance with it.
   See the LICENSE file attached or the following URL for the full license information.
   https://www.apache.org/licenses/LICENSE-2.0
*)


(* :History:
   0.0.1 (2022 Apr.) initial version
*)


Unprotect["DiracAlgebra`*", "DiracAlgebra`Private`*"];
ClearAll["DiracAlgebra`*", "DiracAlgebra`Private`*"];

BeginPackage["DiracAlgebra`"];


(* Configuration *)
(*
$Notation = ChiralNotation;
*)


(* Usage messages *)
FMT = StringReplace[{
  RegularExpression["<(.+?)>"] -> "\!\(\*StyleBox[\"$1\", \"SO\"]\)",     (* arg *)
  RegularExpression["#(.+?)#"] -> "\!\(\*StyleBox[\"$1\", \"TI\"]\)",     (* options *)
  RegularExpression["\\*(.+?)\\*"] -> "\!\(\*StyleBox[\"$1\", \"SB\"]\)", (* emphasize *)
  RegularExpression["'(\\w+)'"] -> "\!\(\*StyleBox[\"\[OpenCurlyDoubleQuote]$1\[CloseCurlyDoubleQuote]\", \"MR\"]\)",  (* quoted fixed string *)
  RegularExpression["`(\\w+)`"] -> "\!\(\*StyleBox[\"$1\", \"MR\"]\)"     (* fixed string *)
}]@*StringTrim;

(*
$Notation::usage = FMT["*$Notation* specifies Dirac-spinor notation, which must be `ChiralNotation` or `DiracNotation`."];
ChiralNotation::usage = FMT["*ChiralNotation* is a choice for `ChooseNotation`."];
DiracNotation::usage = FMT["*DiracNotation* is a choice for `ChooseNotation`."];
*)

SigmaMatrix::usage = FMT["*SigmaMatrix*[<\[Mu]>, None] and *SigmaMatrix*[None, <\[Mu]>] respectively represent the 2x2 matrices \!\(\*SuperscriptBox[\(\[Sigma]\), \(\(<\)\(\[Mu]\)\(>\)\)]\) and \!\(\*SubscriptBox[\(\[Sigma]\), \(\(<\)\(\[Mu]\)\(>\)\)]\)."];
SigmaBarMatrix::usage = FMT["*SigmaBarMatrix*[<\[Mu]>, None] and *SigmaBarMatrix*[None, <\[Mu]>] respectively represent the 2x2 matrices \!\(\*SuperscriptBox[OverscriptBox[\(\[Sigma]\), \(_\)], \(\(<\)\(\[Mu]\)\(>\)\)]\) and \!\(\*SubscriptBox[OverscriptBox[\(\[Sigma]\), \(_\)], \(\(<\)\(\[Mu]\)\(>\)\)]\)."];
GammaMatrix::usage = FMT["*GammaMatrix*[<\[Mu]>, None] and *GammaMatrix*[None, <\[Mu]>] respectively represent the 4x4 matrices \!\(\*SuperscriptBox[\(\[Gamma]\), \(\(<\)\(\[Mu]\)\(>\)\)]\) and \!\(\*SubscriptBox[\(\[Gamma]\), \(\(<\)\(\[Mu]\)\(>\)\)]\)."];
GammaFive::usage = FMT["*GammaFive* is the 4x4 matrices \!\(\*SubscriptBox[\(\[Gamma]\), \(5\)]\)."];
SqrtSigmaDot::usage = FMT["*SqrtSigmaDot*[<p>] gives \!\(\*SqrtBox[\(\[Sigma]\[CenterDot]p\)]\) for representing spinors."];
SqrtSigmaBarDot::usage = FMT["*SqrtSigmaBarDot*[<p>] gives \!\(\*SqrtBox[\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\[CenterDot]p\)]\) for representing spinors."];

SpinorU::usage = FMT["*SpinorU*[<p>, <\[Xi]>] gives u(<p>) for the spinor basis <\[Xi]>."];
SpinorV::usage = FMT["*SpinorV*[<p>, <\[Xi]>] gives v(<p>) for the spinor basis <\[Xi]>."];
SpinorUBar::usage = FMT["*SpinorUBar*[<p>, <\[Xi]>] gives \!\(\*OverscriptBox[\(u\), \(_\)]\)(<p>) for the spinor basis <\[Xi]>."];
SpinorVBar::usage = FMT["*SpinorVBar*[<p>, <\[Xi]>] gives \!\(\*OverscriptBox[\(v\), \(_\)]\)(<p>) for the spinor basis <\[Xi]>."];

Mass::usage = FMT["*Mass*[<p>] is an abstract symbol."];

Remove[FMT];


(* ::InheritFromParent:: *)
(**)


(* messages *)
hoge::invalid = "The name \"`1`\" is invalid.";


Begin["`Private`"];
$Debug = False;


SigmaMatrix   [i:0|1|2|3, None]    := PauliMatrix[i]
SigmaBarMatrix[i:0|1|2|3, None] := If[i==0, +1, -1] * PauliMatrix[i]
SigmaMatrix   [None, i:0|1|2|3] := Eta[i, i] * SigmaMatrix[i, None]
SigmaBarMatrix[None, i:0|1|2|3] := Eta[i, i] * SigmaBarMatrix[i, None]
ZeroMatrix[n_] := Table[0, n, n];

(* Chiral notation with (+,-,-,-) only *)
Eta[i:0|1|2|3, j:0|1|2|3] := Which[i==j==0, +1, i==j, -1, True, 0]
GammaMatrix[i:0|1|2|3, None] := ArrayFlatten[{{ZeroMatrix[2], SigmaMatrix[i, None]}, {SigmaBarMatrix[i, None], ZeroMatrix[2]}}]
GammaMatrix[None, i:0|1|2|3] := ArrayFlatten[{{ZeroMatrix[2], SigmaMatrix[None, i]}, {SigmaBarMatrix[None, i], ZeroMatrix[2]}}]
GammaFive = I GammaMatrix[0, None] . GammaMatrix[1, None] . GammaMatrix[2, None] . GammaMatrix[3, None]
MatrixC = -I GammaMatrix[2, None] . GammaMatrix[0, None];
SqrtSigmaDot[p_] := (Mass[p] IdentityMatrix[2] + Sum[p[i] SigmaMatrix[None, i], {i, 0, 3}])/Sqrt[2(Mass[p]+p[0])]
SqrtSigmaBarDot[p_] := (Mass[p] IdentityMatrix[2] + Sum[p[i] SigmaBarMatrix[None, i], {i, 0, 3}])/Sqrt[2(Mass[p]+p[0])]

SpinorU[p_, \[Xi]_] := With[{x = {{\[Xi][1]}, {\[Xi][2]}}}, ArrayFlatten[{{SqrtSigmaDot[p] . x}, {+SqrtSigmaBarDot[p] . x}}]]
SpinorV[p_, \[Xi]_] := With[{x = {{-Conjugate[\[Xi][2]]}, {Conjugate[\[Xi][1]]}}}, ArrayFlatten[{{SqrtSigmaDot[p] . x}, {-SqrtSigmaBarDot[p] . x}}]]
SpinorUBar[p_, \[Xi]_] := With[{x = Conjugate[{{\[Xi][1], \[Xi][2]}}]}, ArrayFlatten[{{x . SqrtSigmaDot[p], +x . SqrtSigmaBarDot[p]}}] . GammaMatrix[0, None]]
SpinorVBar[p_, \[Xi]_] := With[{x = {{-\[Xi][2],\[Xi][1]}}}, ArrayFlatten[{{x . SqrtSigmaDot[p], -x . SqrtSigmaBarDot[p]}}] . GammaMatrix[0, None]]


Conjugate[{-Conjugate[\[Xi][2]], Conjugate[\[Xi][1]]}]


End[];
Protect[ChiralNotation, DiracNotation,
SigmaMatrix,
SigmaBarMatrix,
GammaMatrix,
GammaFive,
SqrtSigmaDot,
SqrtSigmaBarDot,
SpinorU,
SpinorV,
SpinorUBar,
SpinorVBar,
Mass,
Eta
];
EndPackage[];
