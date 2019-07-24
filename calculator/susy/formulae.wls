#!/usr/bin/env wolframscript
(* ::Package:: *)

SetDirectory[NotebookDirectory[]];
<<WeylAlgebra`

TeXConvert[exp_] := Module[{tmp},
      tmp = exp //. {a | "a" -> \[Alpha], b | "b" -> \[Beta], c | "c" -> \[Gamma], d | "d" -> \[Delta], Complex[a_, b_] :> a+b "ii"} // TeXForm // ToString;
      tmp = FixedPoint[StringReplace[{
           " }" -> "}", " ^" -> "^", " _" -> "_", " )" -> ")",
           "\\dot{\\alpha}" -> "\\dalpha", "\\dot{\\beta}" -> "\\dbeta", "\\dot{\\gamma}" -> "\\dgamma", "\\dot{\\delta}" -> "\\ddelta",
           "\\bar{\\theta}" -> "\\btheta",
           "\\bar{\\sigma}" -> "\\bsigma",
           "\\Sigma"->"\\sigma",
           "\\frac"->"\\tfrac",
           "\\overline{" -> "\\bar{",
           "\\text{Tr}"->"\\Tr",
           "\\text{ii}"->"\\ii",
           "\\text{}"->"{}",
           ".\\sigma"->"\\sigma",
           ".\\bsigma"->"\\bsigma",
           a:("\\delta^{\\"~~Repeated[LetterCharacter])~~"}{}_{\\"~~s:Repeated[LetterCharacter]~~"}":>a<>"}_{\\"<>s<>"}",
           a:("\\sigma^{\\"~~Repeated[LetterCharacter]~~"}") ~~ "{}_" :> a<>"_"
     }], tmp];
     tmp = StringReplace[tmp, {"["->"\\bigl(", "]"->"\\bigr)"}];
     tmp = StringReplace[tmp, {"\\left\\bigl"->"\\left", "\\right\\bigr"->"\\right"}];
     tmp]
ToTable::multiple = "Multiple appearance of `1`.";
ToTable::none = "No appearance of `1`.";
ToTable[exp_, indices_] := Module[{tmp = exp, guessedtype, iterlist, iter},
     iterlist = Function[i, 
          guessedtype = Cases[tmp, (UI | LI)[i, _], All] /. _[_, "any"] -> Nothing // DeleteDuplicates;
          Switch[Length[guessedtype],
             0, Message[ToTable::none, i]; guessedtype = None,
             1, guessedtype = guessedtype[[1, 2]],
             _, Message[ToTable::multiple, i]; Abort[]];
          {i, guessedtype}
        ] /@ indices;
     iterlist = Sequence @@ Select[iterlist, #[[2]] =!= None &];
     Tablize[tmp, iterlist // Evaluate]
   ];

Test::usage = "";
Attributes[Test] = {HoldAll};
Test[exp1_Equal] := Test[exp1, {}]
Test[exp1_Equal, indices_List] := Module[{parts, diff, result},
    parts = List@@exp1;
    parts = FillIndices[#, {"spinor", "lorentz"}] & /@ parts;
    If[Length[indices] > 0,  parts = ToTable[#, indices]& /@ parts; parts = FillIndices[#, {"spinor", "lorentz"}]& /@ parts];
    result = (Equal@@parts) // ExpandAll;
    If[result===True, AppendTo[ToTeX, exp1]];
    {exp1, result}]    
Test[exp1_, exp2_] := Test[exp1, exp2, {}]
Test[exp1_, exp2_, indices_List] := Module[{diff, result},
    diff = exp1 - exp2 // FillIndices[#, {"spinor", "lorentz"}] & // ReleaseHoldAll;
    If[Length[indices] > 0, diff = ToTable[diff, indices] // FillIndices[#, {"spinor", "lorentz"}]& // ReleaseHoldAll];
    result = AllTrue[Flatten[{diff}], #==0&] // ExpandAll;
    If[result == True, AppendTo[ToTeX, exp1 == exp2]];
    {exp1 == exp2, result}]

\[Psi][a_]  := GT["\[Psi]", UI[a, "spinor"]]
\[Psi][,a_] := GT["\[Psi]", LI[a, "spinor"]]
\[Theta][a_]  := GT["\[Theta]", UI[a, "spinor"]]
\[Theta][,a_] := GT["\[Theta]", LI[a, "spinor"]]
\[Xi][a_]  := GT["\[Xi]", UI[a, "spinor"]]
\[Xi][,a_] := GT["\[Xi]", LI[a, "spinor"]]
\[Chi][a_]  := GT["\[Chi]", UI[a, "spinor"]]
\[Chi][,a_] := GT["\[Chi]", LI[a, "spinor"]]
\[Psi]b[a_]  := GT[OverBar["\[Psi]"], UI[PutOverDot[a], "spinor"]]
\[Psi]b[,a_] := GT[OverBar["\[Psi]"], LI[PutOverDot[a], "spinor"]]
\[Theta]b[a_]  := GT[OverBar["\[Theta]"], UI[PutOverDot[a], "spinor"]]
\[Theta]b[,a_] := GT[OverBar["\[Theta]"], LI[PutOverDot[a], "spinor"]]
\[Xi]b[a_]  := GT[OverBar["\[Xi]"], UI[PutOverDot[a], "spinor"]]
\[Xi]b[,a_] := GT[OverBar["\[Xi]"], LI[PutOverDot[a], "spinor"]]
\[Chi]b[a_]  := GT[OverBar["\[Chi]"], UI[PutOverDot[a], "spinor"]]
\[Chi]b[,a_] := GT[OverBar["\[Chi]"], LI[PutOverDot[a], "spinor"]]
\[Theta]\[Theta] = Module[{i=Unique[]}, TDot[\[Theta][i], \[Theta][,i]]];
\[Theta]\[Theta]b = Module[{i=Unique[]}, TDot[\[Theta]b[,i], \[Theta]b[i]]];

\[Sigma]M[\[Mu]_]     := NT[HoldForm[\[Sigma]], UI[\[Mu], "lorentz"]]
\[Sigma]M[,\[Mu]_]    := NT[HoldForm[\[Sigma]], LI[\[Mu], "lorentz"]]
\[Sigma]M[\[Mu]_, \[Nu]_] := NT[HoldForm[\[Sigma]], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"]]
\[Sigma]M[,\[Mu]_, \[Nu]_] := NT[HoldForm[\[Sigma]], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"]]
\[Sigma]bM[\[Mu]_]     := NT[HoldForm[OverBar[\[Sigma]]], UI[\[Mu], "lorentz"]]
\[Sigma]bM[,\[Mu]_]    := NT[HoldForm[OverBar[\[Sigma]]], LI[\[Mu], "lorentz"]]
\[Sigma]bM[\[Mu]_, \[Nu]_] := NT[HoldForm[OverBar[\[Sigma]]], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"]]
\[Sigma]bM[,\[Mu]_, \[Nu]_] := NT[HoldForm[OverBar[\[Sigma]]], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"]]

\[Sigma]ToMatrix[exp_] := exp //. {
  NT[\[Sigma], UI[\[Mu]_, "lorentz"]] :> Table[\[Sigma][\[Mu], a, b], {a,2}, {b,2}],
  NT[\[Sigma], LI[\[Mu]_, "lorentz"]] :> Table[\[Sigma][,\[Mu], a, b], {a,2}, {b,2}],
  NT[OverBar[\[Sigma]], UI[\[Mu]_, "lorentz"]] :> Table[\[Sigma]b[\[Mu], a, b], {a,2}, {b,2}],
  NT[OverBar[\[Sigma]], LI[\[Mu]_, "lorentz"]] :> Table[\[Sigma]b[,\[Mu], a, b], {a,2}, {b,2}],
  NT[\[Sigma], UI[\[Mu]_, "lorentz"], UI[\[Nu]_, "lorentz"]] :> Table[\[Sigma][\[Mu], \[Nu], a, b], {a,2}, {b,2}],
  NT[\[Sigma], LI[\[Mu]_, "lorentz"], LI[\[Nu]_, "lorentz"]] :> Table[\[Sigma][,\[Mu], \[Nu], a, b], {a,2}, {b,2}],
  NT[OverBar[\[Sigma]], UI[\[Mu]_, "lorentz"], UI[\[Nu]_, "lorentz"]] :> Table[\[Sigma]b[\[Mu], \[Nu], a, b], {a,2}, {b,2}],
  NT[OverBar[\[Sigma]], LI[\[Mu]_, "lorentz"], LI[\[Nu]_, "lorentz"]] :> Table[\[Sigma]b[,\[Mu], \[Nu], a, b], {a,2}, {b,2}],
  HiddenOne -> {{1, 0}, {0, 1}}
}
TestForMatrix[exp1_, exp2_, indices_List] := Module[{e1, e2, result},
  e1 = {exp1 // ReleaseHoldAll // \[Sigma]ToMatrix} // Flatten;
  e2 = {exp2 // ReleaseHoldAll // \[Sigma]ToMatrix} // Flatten;
  result = Test[#[[1]], #[[2]], indices]& /@ Transpose[{e1, e2}];
  result = AllTrue[result, #[[2]]&];
  If[result == True, ToTeX = Drop[ToTeX, -Length[e1]]; AppendTo[ToTeX, (exp1 == exp2) //. HiddenOne->1]];
  {exp1 == exp2, result} //. HiddenOne -> 1]

TestConjugate::usage = "";
Attributes[TestConjugate] = {HoldAll};
TestConjugate[exp1_, exp2_, spinorindices_List, indices_List] := Module[{diff, result, e1, e2, i1, i2},
    e1 = exp1  // FillIndices[#, {"spinor", "lorentz"}] &;
    e2 = exp2  // FillIndices[#, {"spinor", "lorentz"}] &;
    If[Length[indices] > 0,
      i1 = Join[spinorindices, indices];
      i2 = Join[SwitchOverDot/@spinorindices, indices];
      e1 = ToTable[e1, i1] // FillIndices[#, {"spinor", "lorentz"}]&;
      e2 = ToTable[e2, i2] // FillIndices[#, {"spinor", "lorentz"}]&;
    ];
    result = AllTrue[Flatten[{Conjugate[e1]-e2}], #==0&] // ExpandAll;
    If[result == True, AppendTo[ToTeX, Superscript[Row[{"[", exp1, "]"}], "*"] == exp2]];
    {Conj[exp1] == exp2, result}]


(* ::Section:: *)
(*Definitions*)


(* ::Code:: *)
(*ToTeX = {};*)
(**)
(*Test[\[Epsilon]U[0,1,2,3]==-\[Epsilon]L[0,1,2,3]==1]*)
(*Test[\[Epsilon]U[1,2] == \[Epsilon]L[2,1] == \[Epsilon]Ud[1,2] == \[Epsilon]Ld[2,1] == 1]*)
(*Test[\[Epsilon]U[2,1] == \[Epsilon]L[1,2] == \[Epsilon]Ud[2,1] == \[Epsilon]Ld[1,2] == -1]*)
(*Test[\[Epsilon]L[a,b]\[Epsilon]U[b,c] == \[Epsilon]U[a,b]\[Epsilon]L[b,c]==\[Delta][a,c,"spinor"], {a,c}]*)
(*Test[\[Psi][a]==\[Epsilon]U[a,b]\[Psi][,b], {a}]*)
(*Test[\[Psi][,a]==\[Epsilon]L[a,b]\[Psi][b], {a}]*)
(*Test[\[Psi]b[a]==\[Epsilon]Ud[a,b]\[Psi]b[,b], {OverDot[a]}]*)
(*Test[\[Psi]b[,a]==\[Epsilon]Ld[a,b]\[Psi]b[b], {OverDot[a]}]*)
(*Test[\[Sigma][\[Mu], a, b], \[Epsilon]L[a,d]\[Epsilon]Ld[b,c] \[Sigma]b[\[Mu], c, d], {a, OverDot[b], \[Mu]}]*)
(*Test[\[Sigma]b[\[Mu], a, b], \[Epsilon]Ud[a,d]\[Epsilon]U[b,c] \[Sigma][\[Mu], c, d], {OverDot[a], b, \[Mu]}]*)


(* ::Code:: *)
(*TestConjugate[\[Psi][a], \[Psi]b[a],{a},{}]*)
(*TestConjugate[\[Psi][,a], \[Psi]b[,a],{a},{}]*)
(*TestConjugate[TDot[\[Psi][a],\[Chi][,a]], TDot[\[Psi]b[,a],\[Chi]b[a]], {}, {}]*)
(**)
(*TestConjugate[\[Sigma][\[Mu],a,b],\[Sigma]bLower[\[Mu],a,b],{a,OverDot[b]}, {\[Mu]}]*)
(*Test[\[Sigma]bLower[\[Mu],a,b], TDot[\[Epsilon]Ld[a,c],\[Epsilon]L[b,d],\[Sigma]b[\[Mu],c,d]], {}]*)
(**)
(*TestConjugate[\[Sigma][\[Mu],\[Nu],a,b],\[Sigma]b[\[Mu],\[Nu],b,a],{a,b}, {\[Mu], \[Nu]}]*)
(*Test[\[Sigma]b[\[Mu],\[Nu],b,a],\[Epsilon]Ld[a,c]\[Epsilon]Ud[b,d]\[Sigma]b[\[Mu],\[Nu],c,d],{OverDot[a], OverDot[b], \[Mu], \[Nu]}]*)
(**)
(*TestConjugate[\[Sigma]b[\[Mu],a,b],\[Sigma]Upper[\[Mu],a,b],{b,OverDot[a]}, {\[Mu]}]*)
(*Test[\[Sigma]Upper[\[Mu],a,b], TDot[\[Epsilon]U[a,c],\[Epsilon]Ud[b,d],\[Sigma][\[Mu],c,d]], {\[Mu],a, OverDot[b]}]*)
(**)
(*TestConjugate[\[Sigma]b[\[Mu],\[Nu],a,b],\[Sigma][\[Mu],\[Nu],b,a],{OverDot[b],OverDot[a]}, {\[Mu], \[Nu]}]*)
(*Test[\[Sigma][\[Mu],\[Nu],b,a], \[Epsilon]U[a,c]\[Epsilon]L[b,d]\[Sigma][\[Mu],\[Nu],c,d],{a, b, \[Mu], \[Nu]}]*)
(**)


(* ::Section:: *)
(*Contraction formulae*)


(* ::Code:: *)
(*Test[TDot[\[Theta][a],\[Theta][b]], (-1/2)\[Epsilon]U[a,b]\[Theta]\[Theta], {a, b}]*)
(*Test[TDot[\[Theta]b[a],\[Theta]b[b]], (+1/2)\[Epsilon]Ud[a,b]\[Theta]\[Theta]b, {OverDot[a], OverDot[b]}]*)
(*Test[TDot[\[Theta][a], \[Xi][,a], \[Theta][b],\[Chi][,b]], (-1/2)TDot[\[Xi][c], \[Chi][,c]]\[Theta]\[Theta]] // ExpandAll*)
(*Test[TDot[\[Theta][c],\[Sigma][\[Nu],c,b],\[Theta]b[b], \[Theta][a]], (1/2)\[Theta]\[Theta] TDot[\[Theta]b[,c], \[Sigma]b[\[Nu],c,a]], {\[Nu], a}]*)
(**)
(*Test[TDot[\[Theta][,a],\[Theta][,b]], (1/2)\[Epsilon]L[a,b]\[Theta]\[Theta], {a, b}]*)
(*Test[TDot[\[Theta]b[,a],\[Theta]b[,b]], (-1/2)\[Epsilon]Ld[a,b]\[Theta]\[Theta]b, {OverDot[a], OverDot[b]}]*)
(*Test[TDot[\[Theta]b[,a], \[Xi]b[a], \[Theta]b[,b], \[Chi]b[b]], (-1/2)TDot[\[Xi]b[,c], \[Chi]b[c]]\[Theta]\[Theta]b]*)
(*Test[TDot[\[Theta][c],\[Sigma][\[Nu],c,b],\[Theta]b[b], \[Theta]b[,a]], -(1/2)\[Theta]\[Theta]b TDot[\[Theta][c], \[Sigma][\[Nu],c,a]], {\[Nu], OverDot[a]}]*)
(**)
(*Test[TDot[\[Theta][a],\[Theta][,b]], (1/2)\[Delta][a,b]\[Theta]\[Theta], {a, b}]*)
(*Test[TDot[\[Theta]b[,a],\[Theta]b[b]], (1/2)\[Delta][OverDot[a],OverDot[b]]\[Theta]\[Theta]b, {OverDot[a], OverDot[b]}]*)
(*Test[TDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b]]TDot[\[Theta][c],\[Sigma][\[Nu],c,d],\[Theta]b[d]], (1/2)\[Theta]\[Theta] \[Theta]\[Theta]b \[Eta]U[\[Mu],\[Nu]], {\[Mu], \[Nu]}]*)
(**)
(*Test[TDot[\[Theta][a] ,\[Sigma][\[Mu], a, b], \[Sigma]b[\[Nu], b, c], \[Theta][,c]], \[Eta]U[\[Mu],\[Nu]] \[Theta]\[Theta], {\[Mu], \[Nu]}]*)
(*Test[TDot[\[Theta]b[,a], \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c], \[Theta]b[c]], \[Eta]U[\[Mu],\[Nu]] \[Theta]\[Theta]b, {\[Mu], \[Nu]}]*)
(*Test[TDot[\[Sigma][\[Mu],a,b], \[Theta]b[b], \[Theta][c], \[Sigma][\[Nu],c,d], \[Theta]b[d]], (1/2)\[Theta]\[Theta]b TDot[\[Sigma][\[Mu],a,b],\[Sigma]b[\[Nu],b,c],\[Theta][,c]], {\[Mu], \[Nu], a}]*)


(* ::Code:: *)
(*TestForMatrix[\[Sigma]M[\[Mu]].\[Sigma]bM[\[Nu]], \[Eta]U[\[Mu],\[Nu]]HiddenOne - 2I \[Sigma]M[\[Mu],\[Nu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[\[Sigma]M[\[Mu]].\[Sigma]bM[\[Rho]].\[Sigma]M[\[Nu]] + \[Sigma]M[\[Nu]].\[Sigma]bM[\[Rho]].\[Sigma]M[\[Mu]], 2(\[Eta]U[\[Mu],\[Rho]]\[Sigma]M[\[Nu]]+\[Eta]U[\[Nu],\[Rho]]\[Sigma]M[\[Mu]]-\[Eta]U[\[Mu],\[Nu]]\[Sigma]M[\[Rho]]), {\[Mu], \[Nu], \[Rho]}]*)
(**)
(*TestForMatrix[\[Sigma]bM[\[Mu]].\[Sigma]M[\[Nu]], \[Eta]U[\[Mu],\[Nu]]HiddenOne - 2I \[Sigma]bM[\[Mu],\[Nu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[\[Sigma]M[\[Mu]].\[Sigma]bM[\[Nu]].\[Sigma]M[\[Rho]] - \[Sigma]M[\[Rho]].\[Sigma]bM[\[Nu]].\[Sigma]M[\[Mu]], 2I \[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]]\[Sigma]M[,\[CapitalSigma]], {\[Mu], \[Nu], \[Rho]}]*)
(**)
(*TestForMatrix[Tr[\[Sigma]M[\[Mu]].\[Sigma]bM[\[Nu]]], 2\[Eta]U[\[Mu],\[Nu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[Tr[\[Sigma]bM[\[Mu]].\[Sigma]M[\[Nu]]], 2\[Eta]U[\[Mu],\[Nu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[\[Sigma]bM[\[Mu]].\[Sigma]M[\[Rho]].\[Sigma]bM[\[Nu]] + \[Sigma]bM[\[Nu]].\[Sigma]M[\[Rho]].\[Sigma]bM[\[Mu]], 2(\[Eta]U[\[Mu],\[Rho]]\[Sigma]bM[\[Nu]]+\[Eta]U[\[Nu],\[Rho]] \[Sigma]bM[\[Mu]]-\[Eta]U[\[Mu],\[Nu]]\[Sigma]bM[\[Rho]]), {\[Mu], \[Nu], \[Rho]}]*)
(**)
(*Test[\[Sigma][\[Mu],a,a]\[Sigma]b[,\[Mu],b,b],  2\[Delta][a,b]\[Delta]d[b,a], {a,OverDot[a],b,OverDot[b]}]*)
(*TestForMatrix[\[Sigma]bM[\[Mu]].\[Sigma]M[\[Nu]].\[Sigma]bM[\[Rho]] - \[Sigma]bM[\[Rho]].\[Sigma]M[\[Nu]].\[Sigma]bM[\[Mu]], -2I \[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]] \[Sigma]bM[,\[CapitalSigma]],{\[Mu], \[Nu], \[Rho]}]*)
(**)
(*Test[\[Sigma][,\[Mu],a,a]\[Sigma][\[Mu],b,b],   2\[Epsilon]L[a,b]\[Epsilon]Ld[a,b], {a,OverDot[a],b,OverDot[b]}]*)
(*Test[TDot[\[Epsilon]Ld[b,a], \[Sigma]b[\[Mu],a,a]] == TDot[\[Epsilon]Ld[b,a], \[Epsilon]U[a,c], \[Epsilon]Ud[a,c], \[Sigma][\[Mu],c,c]] == TDot[\[Epsilon]U[a,c], \[Sigma][\[Mu],c,b]], {\[Mu], a, OverDot[b]}]*)
(**)
(*Test[\[Sigma]b[,\[Mu],a,a]\[Sigma]b[\[Mu],b,b],  2\[Epsilon]Ud[a,b]\[Epsilon]U[a,b],  {a,OverDot[a],b,OverDot[b]}]*)
(*Test[TDot[\[Epsilon]L[b,a], \[Sigma]b[\[Mu],a,a]] == TDot[\[Epsilon]L[b,a], \[Epsilon]U[a,c], \[Epsilon]Ud[a,c], \[Sigma][\[Mu],c,c]] == TDot[\[Epsilon]Ud[a,c], \[Sigma][\[Mu],b,c]], {\[Mu], OverDot[a], b}]*)
(**)
(*TestForMatrix[Tr[\[Sigma]M[\[Mu], \[Nu]]], 0, {\[Mu],\[Nu]}]*)
(*TestForMatrix[Tr[\[Sigma]bM[\[Mu], \[Nu]]], 0, {\[Mu],\[Nu]}]*)
(*TestForMatrix[Tr[\[Sigma]M[\[Mu],\[Nu]].\[Sigma]M[\[Rho],\[CapitalSigma]]], ((1/2)(\[Eta]U[\[Mu],\[Rho]]\[Eta]U[\[Nu],\[CapitalSigma]] - \[Eta]U[\[Mu],\[CapitalSigma]]\[Eta]U[\[Nu],\[Rho]])+(-I/2)\[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]]) , {\[Mu], \[Nu], \[Rho], \[CapitalSigma]}]*)
(**)
(*TestForMatrix[\[Sigma]bM[\[Mu],\[Nu]], -\[Sigma]bM[\[Nu],\[Mu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[\[Sigma]M[\[Mu],\[Nu]], -\[Sigma]M[\[Nu],\[Mu]], {\[Mu],\[Nu]}]*)
(*TestForMatrix[Tr[\[Sigma]bM[\[Mu],\[Nu]].\[Sigma]bM[\[Rho],\[CapitalSigma]]], ((1/2)(\[Eta]U[\[Mu],\[Rho]]\[Eta]U[\[Nu],\[CapitalSigma]] - \[Eta]U[\[Mu],\[CapitalSigma]]\[Eta]U[\[Nu],\[Rho]])+(I/2)\[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]]) , {\[Mu], \[Nu], \[Rho], \[CapitalSigma]}]*)


(* ::Code:: *)
(*Test[TDot[\[Sigma][\[Mu],\[Nu],a,b], \[Epsilon]L[b,c]], TDot[\[Sigma][\[Mu],\[Nu],c,b], \[Epsilon]L[b,a]], {a,c,\[Mu],\[Nu]}]*)
(**)
(*Test[*)
(*  TDot[\[Sigma][\[Mu],a,a], \[Sigma][\[Nu],b,b]] - TDot[\[Sigma][\[Nu],a,a], \[Sigma][\[Mu],b,b]],*)
(*  -2I TDot[\[Sigma][\[Mu],\[Nu],a,c], \[Epsilon]L[c,b], \[Epsilon]Ld[a,b]]-2I TDot[\[Epsilon]Ld[a,c], \[Sigma]b[\[Mu],\[Nu],c,b], \[Epsilon]L[a,b]], {a,OverDot[b],b,OverDot[a],\[Mu],\[Nu]}]*)
(**)
(*Test[TDot[\[Sigma]b[\[Mu],\[Nu],a,b], \[Epsilon]Ud[b,c]], TDot[\[Sigma]b[\[Mu],\[Nu],c,b], \[Epsilon]Ud[b,a]], {OverDot[a],OverDot[c],\[Mu],\[Nu]}]*)
(**)
(*Test[*)
(*  TDot[\[Sigma][\[Mu],a,a], \[Sigma][\[Nu],b,b]] + TDot[\[Sigma][\[Nu],a,a], \[Sigma][\[Mu],b,b]],*)
(* \[Eta]U[\[Mu],\[Nu]]\[Epsilon]L[a,b]\[Epsilon]Ld[a,b] + 4 \[Eta]L[\[Rho],\[CapitalSigma]]\[Sigma][\[Rho],\[Mu],a,c]\[Epsilon]L[c,b]\[Epsilon]Ld[a,c]\[Sigma]b[\[CapitalSigma],\[Nu],c,b],   {a,OverDot[b],b,OverDot[a],\[Mu],\[Nu]}]*)
(**)
(*TestForMatrix[\[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]]\[Sigma]bM[,\[Rho],\[CapitalSigma]], -2I \[Sigma]bM[\[Mu],\[Nu]], {\[Mu], \[Nu]}]*)
(*Test[*)
(*  TDot[\[Sigma]b[\[Mu],a,a], \[Sigma]b[\[Nu],b,b]] - TDot[\[Sigma]b[\[Nu],a,a], \[Sigma]b[\[Mu],b,b]],*)
(*  -2I TDot[\[Sigma]b[\[Mu],\[Nu],a,c], \[Epsilon]Ud[c,b], \[Epsilon]U[a,b]]-2I TDot[\[Epsilon]U[a,c], \[Sigma][\[Mu],\[Nu],c,b], \[Epsilon]Ud[a,b]],  {a,OverDot[b],b,OverDot[a],\[Mu],\[Nu]}]*)
(**)
(*TestForMatrix[\[Epsilon]U[\[Mu],\[Nu],\[Rho],\[CapitalSigma]]\[Sigma]M[,\[Rho],\[CapitalSigma]], 2 I \[Sigma]M[\[Mu],\[Nu]], {\[Mu], \[Nu]}]*)
(*Test[*)
(*  TDot[\[Sigma]b[\[Mu],a,a], \[Sigma]b[\[Nu],b,b]] + TDot[\[Sigma]b[\[Nu],a,a], \[Sigma]b[\[Mu],b,b]],*)
(*  \[Eta]U[\[Mu],\[Nu]]\[Epsilon]Ud[a,b]\[Epsilon]U[a,b] + 4 \[Eta]L[\[Rho],\[CapitalSigma]]\[Sigma]b[\[Rho],\[Mu],a,c]\[Epsilon]Ud[c,b]\[Epsilon]U[a,c]\[Sigma][\[CapitalSigma],\[Nu],c,b],   {a,OverDot[b],b,OverDot[a],\[Mu],\[Nu]}]*)


(* ::Code:: *)
(*TestConjugate[TDot[\[Chi]b[,a],\[Sigma]b[\[Mu],a,b],\[Xi][,b]],TDot[\[Xi]b[,a],\[Sigma]b[\[Mu],a,b],\[Chi][,b]],{}, {\[Mu]}]*)
(*TestConjugate[TDot[\[Chi]b[,a],\[Sigma]b[\[Mu],a,b],\[Sigma][\[Nu],b,c],\[Xi]b[c]],TDot[\[Xi][a],\[Sigma][\[Nu],a,b],\[Sigma]b[\[Mu],b,c],\[Chi][,c]],{}, {\[Mu],\[Nu]}]*)


filehandle = OpenWrite["formulae.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];  
