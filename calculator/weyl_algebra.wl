(* ::Package:: *)

System`Convert`CommonDump`templateBoxToDisplay = BoxForm`TemplateBoxToDisplayBoxes;
SubsuperscriptBoxSub[z_, {},         {},       f_] := z;
SubsuperscriptBoxSub[z_, super_List, {},       f_] := Row[super] // SuperscriptBox[z, MakeBoxes[#, f]]&;
SubsuperscriptBoxSub[z_, {},         sub_List, f_] := Row[sub] // SubscriptBox[z, MakeBoxes[#,f]] &;
SubsuperscriptBoxSub[z_, super_List, sub_List, f_] := Sequence[Row[sub], Row[super]] // SubsuperscriptBox[z, MakeBoxes[#1,f], MakeBoxes[#2,f]] &
Tensor /: MakeBoxes[obj: Tensor[z_[mainsuper_List, mainsub_List], super_List, sub_List], f:StandardForm|TraditionalForm] := SubsuperscriptBoxSub[MakeBoxes[z, f], mainsuper, mainsub, f] // SubsuperscriptBoxSub[#, super, sub, f]& // InterpretationBox[#,obj] &
Tensor /: MakeBoxes[obj: Tensor[z_, super_List, sub_List], f:StandardForm|TraditionalForm] := InterpretationBox[#,obj] &@ SubsuperscriptBoxSub[MakeBoxes[z,f], super, sub, f]
GrassmannTensor /: MakeBoxes[obj: GrassmannTensor[z_, super_List, sub_List], f:StandardForm|TraditionalForm] := InterpretationBox[#,obj] &@ StyleBox[SubsuperscriptBoxSub[MakeBoxes[z,f], super, sub, f], Red]
GrassmannDot /: MakeBoxes[obj: GrassmannDot[a__], f:StandardForm] := Dot[a] // ToBoxes // InterpretationBox[#,obj] &
GrassmannDot /: MakeBoxes[obj: GrassmannDot[a__], f:TraditionalForm] := Row[{a}] // ToBoxes // InterpretationBox[#,obj] &
GrassmannPair /: MakeBoxes[obj: GrassmannPair[a_, b_], f:StandardForm|TraditionalForm] := RowBox[{"(", StyleBox[MakeBoxes[a, f], Red], StyleBox[MakeBoxes[b, f], Red], ")"}] // InterpretationBox[#, obj]&
\[Eta] /: MakeBoxes[obj: \[Eta][a_List, b_List], f:StandardForm|TraditionalForm] := InterpretationBox[#,obj] &@ SubsuperscriptBoxSub[MakeBoxes["\[Eta]",f], a, b, f]
\[Delta] /: MakeBoxes[obj: \[Delta][a_, b_], f:StandardForm|TraditionalForm] := InterpretationBox[#,obj] &@ SubsuperscriptBoxSub[MakeBoxes["\[Delta]",f], {}, {a,b}, f]


PutOverDot[a_] := If[Head[a] === OverDot || a === "", a, OverDot[a]]
SwitchOverDot[a: ""] := ""
SwitchOverDot[OverDot[x_]] := x
SwitchOverDot[x_] := OverDot[x]

GrassmannTensor /: Conjugate[GrassmannTensor[OverBar[a_], b_, c_]] := GrassmannTensor[a, SwitchOverDot/@b, SwitchOverDot/@c]
GrassmannTensor /: Conjugate[GrassmannTensor[a_, b_, c_]] := GrassmannTensor[OverBar[a], SwitchOverDot/@b, SwitchOverDot/@c]

GrassmannDot[x1___, Times[a_, b__], x2___] := GrassmannDot[x1, a, Times[b], x2]
GrassmannDot[x1___, Plus[a_, b__], x2___] := GrassmannDot[x1, a, x2] + GrassmannDot[x1, Plus[b], x2]
GrassmannDot[x1___, a_, x2___] /; NumericQ[a] := a GrassmannDot[x1, x2]
(*GrassmannDot[x1___, a_Tensor, x2___] := a GrassmannDot[x1, x2]*)
GrassmannDot[x1___, a_Symbol, x2___] := a GrassmannDot[x1, x2]
GrassmannDot[] := 1

GrassmannDot /: GrassmannDot[a__]GrassmannDot[b__] := Module[{bnew, overlap},
  overlap = Intersection[FindIndices[GrassmannDot[a]], FindIndices[GrassmannDot[b]]];
  bnew = If[Length[overlap] > 0, RenewIndices[GrassmannDot[b]], GrassmannDot[b]];
  GrassmannDot[a, Sequence@@bnew]]
GrassmannDot /: Conjugate[GrassmannDot[a__]] := GrassmannDot @@ Reverse[Conjugate/@{a}]

(* make dot contraction *)
GrassmannDot[x1___, f1_GrassmannTensor, x2___, f1_, x3___] := 0 /; FreeQ[f1, ""]
GrassmannDot[x1___, f1: GrassmannTensor[_, {a_}, {}], mid:Repeated[_GrassmannTensor], f2: GrassmannTensor[_, {}, {a_}], x2___] := (-1)^Length[{mid}] GrassmannDot[x1,f1,f2,mid,x2]
GrassmannDot[x1___, f1: GrassmannTensor[_, {}, {a_}], mid:Repeated[_GrassmannTensor], f2: GrassmannTensor[_, {a_}, {}], x2___] := (-1)^(Length[{mid}]+1) GrassmannDot[x1,f2,f1,mid,x2]
GrassmannDot[x1___, GrassmannTensor[s_OverBar, {OverDot[a_]}, {}], GrassmannTensor[t_OverBar, {}, {OverDot[a_]}], x2___] := (-GrassmannPair[s, t]) GrassmannDot[x1, x2]
GrassmannDot[x1___, GrassmannTensor[s_, {a_}, {}], GrassmannTensor[t_, {}, {a_}], x2___] /; FreeQ[a, OverDot] && FreeQ[{s,t}, OverBar] := GrassmannPair[s, t] GrassmannDot[x1, x2]

GrassmannContraction[exp_] := exp //. {
  GrassmannDot[x1___, (f1:Tensor|GrassmannTensor)[x2_, {x3___, a_}, x4_], (f2:Tensor|GrassmannTensor)[x5_, x6_, {a_, x7___}], x8___] :> GrassmannDot[x1, f1[x2, {x3, ""}, x4], f2[x5, x6, {"", x7}], x8] /; FreeQ[a, OverDot] && a=!="",
  GrassmannDot[x1___, (f1:Tensor|GrassmannTensor)[x2_, x3_, {x4___, a:OverDot[_]}], (f2:Tensor|GrassmannTensor)[x5_, {a_, x6___}, x7_], x8___] :> GrassmannDot[x1, f1[x2, x3, {x4, ""}], f2[x5, {"", x6}, x7], x8]
};
GrassmannContractionRevert[exp_] := exp //. {
  GrassmannDot[x1___, (f1:Tensor|GrassmannTensor)[x2_, {x3___, ""}, x4_], (f2:Tensor|GrassmannTensor)[x5_, x6_, {"", x7___}], x8___] :> Module[{a=Unique[]}, GrassmannDot[x1, f1[x2, {x3, a}, x4], f2[x5, x6, {a, x7}], x8]],
  GrassmannDot[x1___, (f1:Tensor|GrassmannTensor)[x2_, x3_, {x4___, ""}], (f2:Tensor|GrassmannTensor)[x5_, {"", x6___}, x7_], x8___] :> Module[{a=Unique[]}, GrassmannDot[x1, f1[x2, x3, {x4, OverDot[a]}], f2[x5, {OverDot[a], x6}, x7], x8]]
}



ToUpper[exp_] := exp //. {
  GrassmannTensor[f_OverBar, {}, {a_OverDot}] :> Module[{b=OverDot[Unique[]]}, \[Epsilon]L[a, b] GrassmannTensor[f, {b}, {}]], 
  GrassmannTensor[f_, {}, {a_}] /; FreeQ[f, OverBar] && FreeQ[a, OverDot] :> Module[{b=Unique[]}, \[Epsilon]L[a, b] GrassmannTensor[f, {b}, {}]]
}

GrassmannExpand[exp_] := Module[{tmp = exp},
  tmp = tmp //. {
    GrassmannPair[a_OverBar, b_OverBar] :> Module[{i=OverDot[Unique[]]}, GrassmannDot[(GrassmannTensor[a, {}, {i}] // ToUpper), GrassmannTensor[b, {i}, {}]]],
    GrassmannPair[a_, b_] /; FreeQ[{a,b}, OverBar] :> Module[{i=Unique[]}, GrassmannDot[GrassmannTensor[a, {i}, {}], (GrassmannTensor[b, {}, {i}] // ToUpper)]]
  }]

SortGrassmannDotSub[GrassmannDot[a___]] := Module[{elements = {a}, order, sign},
  order = OrderingBy[elements, #[[1]]&];
  sign = Signature[order];
  (sign)*GrassmannDot@@(elements[[order]])
]  
SortGrassmannDot[exp_] := FixedPoint[# /. (g_GrassmannDot :> SortGrassmannDotSub[g])&, exp]

SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];
FindIndices[exp_] := Cases[exp, (Tensor|GrassmannTensor)[_, a_List, b_List] :> {a,b}, All] // Flatten // Select[#, FreeQ[#, _Integer]&]&;
FindDoublyAppearingLetters[exp_] := Cases[Counts[FindIndices[exp]] /. {Association -> List}, (p_ -> 2) :> p]

RewriteIndicesSub[exp_] := Module[{
    allindices = FindIndices[exp] // DeleteDuplicates,
    toreplace = FindDoublyAppearingLetters[exp],
    nottoreplace,
    newindices,
    rule
  },
  nottoreplace = Complement[allindices, toreplace];
  newindices = Complement[CharacterRange["a", "z"], TextString/@nottoreplace];
  If[Length[newindices] < Length[toreplace], Print["indices shortage."]; Abort[]];
  rule = (#[[1]]->#[[2]]) &/@ Transpose[{toreplace, newindices[[1;;Length[toreplace]]]}];
  exp /. rule
];
RewriteIndices[exp_] := Total[RewriteIndicesSub /@ SumToList[exp]]

RenewIndicesSub[exp_] := Module[{
    allindices = FindIndices[exp] // DeleteDuplicates,
    newindices, rule
  },
  newindices = Unique[] /@ allindices;
  rule = (#[[1]]->#[[2]]) &/@ Transpose[{allindices, newindices}];
  exp /. rule
];
RenewIndices[exp_] := Total[RenewIndicesSub /@ SumToList[GrassmannContractionRevert[exp]]]

FillGrassmannIndicesSub[exp_] := Module[{indices = FindDoublyAppearingLetters[exp], tmp = exp},
  indices = indices //. {OverDot[a_]:>a};
  Do[tmp = Sum@@{tmp, {i, 2}}, {i, indices}]; tmp]
  
FillGrassmannIndices[exp_] := Total[FillGrassmannIndicesSub /@ SumToList[exp]]


\[Theta][a_] := GrassmannTensor[\[Theta], {a}, {}]
\[Theta][,a_] := GrassmannTensor[\[Theta], {}, {a}]
\[Theta]b[a_] := GrassmannTensor[OverBar[\[Theta]], {PutOverDot[a]}, {}]
\[Theta]b[,a_] := GrassmannTensor[OverBar[\[Theta]], {}, {PutOverDot[a]}]

\[Epsilon]U[a_, b_] := Tensor[\[Epsilon], {a, b}, {}]
\[Epsilon]L[a_, b_] := Tensor[\[Epsilon], {}, {a, b}]
\[Epsilon]Ud[a_, b_] := Tensor[\[Epsilon], {PutOverDot[a], PutOverDot[b]}, {}]
\[Epsilon]Ld[a_, b_] := Tensor[\[Epsilon], {}, {PutOverDot[a], PutOverDot[b]}]
\[Epsilon]4U[a_, b_, c_, d_] := Tensor[\[CurlyEpsilon], {a, b, c, d}, {}] 
\[Epsilon]4L[a_, b_, c_, d_] := Tensor[\[CurlyEpsilon], {},  {a, b, c, d}] 

Tensor[\[Epsilon], {a_, a_}, {}] := 0
Tensor[\[Epsilon], {}, {a_, a_}] := 0
Tensor[\[Epsilon], {1, 2}, {}] := +1
Tensor[\[Epsilon], {2, 1}, {}] := -1
Tensor[\[Epsilon], {}, {1, 2}] := -1 (* beware! *)
Tensor[\[Epsilon], {}, {2, 1}] := +1 (* beware! *)
Tensor[\[Epsilon], {OverDot[1], OverDot[2]}, {}] := +1
Tensor[\[Epsilon], {OverDot[2], OverDot[1]}, {}] := -1
Tensor[\[Epsilon], {}, {OverDot[1], OverDot[2]}] := -1 (* beware! *)
Tensor[\[Epsilon], {}, {OverDot[2], OverDot[1]}] := +1 (* beware! *)
Tensor[\[CurlyEpsilon], {0, 1, 2, 3}, {}] := +1
Tensor[\[CurlyEpsilon], {}, {0, 1, 2, 3}] := -1
Tensor[\[CurlyEpsilon], ___, {___, a_, ___, a_, ___}, ___] := 0
Tensor[\[CurlyEpsilon], x1___, {x2___, a_, x3___, b_, x4___}, x5___] /; a > b := (-1)^(Length[{x3}]+1) Tensor[\[CurlyEpsilon], x1, {x2, b, a, x3, x4}, x5]

\[Eta]U[\[Mu]_, \[Nu]_] := \[Eta][{\[Mu], \[Nu]}, {}]
\[Eta]L[\[Mu]_, \[Nu]_] := \[Eta][{}, {\[Mu], \[Nu]}]
\[Sigma][\[Mu]_, a_, b_]   /; FreeQ[\[Mu], List] := Tensor[\[Sigma][{\[Mu]}, {}], {}, {a, PutOverDot[b]}]
\[Sigma][,\[Mu]_, a_, b_]  /; FreeQ[\[Mu], List] := Tensor[\[Sigma][{}, {\[Mu]}], {}, {a, PutOverDot[b]}]
\[Sigma]b[\[Mu]_, a_, b_]  /; FreeQ[\[Mu], List] := Tensor[OverBar[\[Sigma]][{\[Mu]}, {}], {PutOverDot[a], b}, {}]
\[Sigma]b[,\[Mu]_, a_, b_] /; FreeQ[\[Mu], List] := Tensor[OverBar[\[Sigma]][{}, {\[Mu]}], {PutOverDot[a], b}, {}]

\[Sigma][{\[Mu]_,\[Nu]_}, a_, b_] := Tensor[\[Sigma][{\[Mu], \[Nu]}, {}], {" ", b}, {a}]
\[Sigma][,{\[Mu]_, \[Nu]_}, a_, b_] := Tensor[\[Sigma][{}, {\[Mu], \[Nu]}], {" ", b}, {a}]
\[Sigma]b[{\[Mu]_, \[Nu]_}, a_, b_] := Tensor[OverBar[\[Sigma]][{\[Mu], \[Nu]}, {}], {PutOverDot[a]}, {" ", PutOverDot[b]}]
\[Sigma]b[,{\[Mu]_, \[Nu]_}, a_, b_] := Tensor[OverBar[\[Sigma]][{}, {\[Mu], \[Nu]}], {PutOverDot[a]}, {" ", PutOverDot[b]}]

EvaluateDoublySigma[exp_] := exp //.{
  Tensor[\[Sigma][{\[Mu]_, \[Nu]_}, {}], {" ", b_}, {a_}] :> Module[{c=Unique[]},
    (I/4)(GrassmannDot[\[Sigma][\[Mu], a, c], \[Sigma]b[\[Nu], c, b]]-GrassmannDot[\[Sigma][\[Nu], a, c], \[Sigma]b[\[Mu], c, b]])],
  Tensor[\[Sigma][{}, {\[Mu]_, \[Nu]_}], {" ", b_}, {a_}] :> Module[{c=Unique[]},
    (I/4)(GrassmannDot[\[Sigma][,\[Mu], a, c], \[Sigma]b[,\[Nu], c, b]]-GrassmannDot[\[Sigma][,\[Nu], a, c], \[Sigma]b[,\[Mu], c, b]])],
  Tensor[OverBar[\[Sigma]][{\[Mu]_, \[Nu]_}, {}], {a_}, {" ", b_}] :> Module[{c=Unique[]},
    (I/4)(GrassmannDot[\[Sigma]b[\[Mu], a, c], \[Sigma][\[Nu], c, b]]-GrassmannDot[\[Sigma]b[\[Nu], a, c], \[Sigma][\[Mu], c, b]])],
  Tensor[\[Sigma][{}, {\[Mu]_, \[Nu]_}], {" ", b_}, {a_}] :> Module[{c=Unique[]},
    (I/4)(GrassmannDot[\[Sigma]b[,\[Mu], a, c], \[Sigma][,\[Nu], c, b]]-GrassmannDot[\[Sigma]b[,\[Nu], a, c], \[Sigma][,\[Mu], c, b]])]
}

\[Eta][{\[Mu]_, \[Nu]_}, {}] /; \[Mu]!=\[Nu] := 0
\[Eta][{}, {\[Mu]_, \[Nu]_}] /; \[Mu]!=\[Nu] := 0
\[Eta][{a:0|1|2|3, a_}, {}] := If[a==0, 1, -1]
\[Eta][{}, {a:0|1|2|3, a_}] := If[a==0, 1, -1]

Tensor[\[Sigma]         [{i:0|1|2|3}, {}], {}, {a:1|2, OverDot[b:1|2]}] := PauliMatrix[i][[a,b]]
Tensor[OverBar[\[Sigma]][{i:0|1|2|3}, {}], {OverDot[a:1|2], b:1|2}, {}] := If[i==0, +1, -1] * PauliMatrix[i][[a,b]]
Tensor[\[Sigma][{}, {\[Mu]_}], {}, x1_] := Module[{\[Nu]=Unique[]}, Tensor[\[Eta][{}, {\[Mu], \[Nu]}], {}, {}]Tensor[\[Sigma][{\[Nu]}, {}], {}, x1]]
Tensor[OverBar[\[Sigma]][{}, {\[Mu]_}], x1_, {}] := Module[{\[Nu]=Unique[]}, Tensor[\[Eta][{}, {\[Mu], \[Nu]}], {}, {}]Tensor[OverBar[\[Sigma]][{\[Nu]}, {}], x1, {}]]
\[Delta][a_, a_] := 1
\[Delta][a_, b_] /; a!=b := 0
\[Delta][OverDot[a_], OverDot[b_]] /; a!=b := 0


Attributes[TestByFill] = {HoldAll};
TestByFill[exp1_, exp2_, freeindices___] := Module[{diff, result, indices=Sequence@@(ReleaseHold/@{freeindices})},
  diff = ReleaseHold[exp1-exp2] /. {SUM->Sum, TR->Tr} // GrassmannContractionRevert // EvaluateDoublySigma // ToUpper;
  indices = {indices} // ReleaseHold;
  diff = diff // GrassmannExpand // FillGrassmannIndices;
  diff = SortGrassmannDot[Table[diff, Evaluate[Sequence@@indices]]];
  result = AllTrue[Flatten[{diff}], #==0&];
  If[result==True, AppendTo[ToTeX, exp1==exp2]];
  {exp1==exp2, result}]

TeXOutput := Do[Module[{tmp},
  tmp = t //. {a|"a"->\[Alpha], b|"b"->\[Beta], c|"c"->\[Gamma], d|"d"->\[Delta]} // TeXForm // ToString;
  FixedPoint[StringReplace[{
    " }"->"}", " ^"->"^", " _"->"_", " )"->")",
    "\\dot{\\alpha}"->"\\dalpha", "\\dot{\\beta}"->"\\dbeta", "\\dot{\\gamma}"->"\\dgamma", "\\dot{\\delta}"->"\\ddelta"
        }], tmp]] // Print,
  {t, ToTeX}]


(* ::Text:: *)
(*Sigma-matrices basic rules*)


ToTeX = {};
  
TestByFill[GrassmannDot[\[Epsilon]U[a,b], \[Epsilon]L[b,c]], \[Delta][a,c], {a,2}, {c,2}]
TestByFill[GrassmannDot[\[Epsilon]L[a,b], \[Epsilon]U[b,c]], \[Delta][a,c], {a,2}, {c,2}]

TestByFill[\[Sigma][\[Mu], a, b], \[Epsilon]L[a,d]\[Epsilon]Ld[b,c] \[Sigma]b[\[Mu], c, d], {\[Mu], 0, 3}, {a,2}, {b,2}]
TestByFill[\[Sigma]b[\[Mu], a, b], \[Epsilon]Ud[a,d]\[Epsilon]U[b,c] \[Sigma][\[Mu], c, d], {\[Mu], 0, 3}, {a,2}, {b,2}]

TestByFill[Conjugate[\[Sigma][\[Mu], a, b]], \[Epsilon]Ld[a,c]\[Epsilon]L[b,d]\[Sigma]b[\[Mu], c, d], {a,2}, {b,2}, {\[Mu],0,3}]
TestByFill[Conjugate[\[Sigma]b[\[Mu], a, b]], \[Epsilon]U[a,c]\[Epsilon]Ud[b,d]\[Sigma][\[Mu], c, d], {a,2}, {b,2}, {\[Mu],0,3}]

Conjugate[\[Sigma][{\[Mu], \[Nu]}, a, b]] - \[Epsilon]Ld[a,c]\[Epsilon]Ud[b,d]\[Sigma]b[{\[Mu], \[Nu]}, c,d]
(EvaluateDoublySigma[%])//. {
  Conjugate[a_ + b_] :> Conjugate[a] + Conjugate[b],
  Conjugate[\[Sigma][\[Mu]_, a_, b_]] :> Module[{c=Unique[], d=Unique[]}, \[Epsilon]Ld[a,c]\[Epsilon]L[b,d]\[Sigma]b[\[Mu], c, d]],
  Conjugate[\[Sigma]b[\[Mu]_, a_, b_]] :> Module[{c=Unique[], d=Unique[]}, \[Epsilon]U[a,c]\[Epsilon]Ud[b,d]\[Sigma][\[Mu], c, d]]
} // ExpandAll // FillGrassmannIndices // Table[#, {\[Mu], 0, 3}, {\[Nu],0,3}, {a, 2}, {b, 2}]&

Conjugate[\[Sigma]b[{\[Mu], \[Nu]}, a, b]] - \[Epsilon]U[a,c]\[Epsilon]L[b,d]\[Sigma][{\[Mu], \[Nu]}, c,d]
(EvaluateDoublySigma[%])//. {
  Conjugate[a_ + b_] :> Conjugate[a] + Conjugate[b],
  Conjugate[\[Sigma][\[Mu]_, a_, b_]] :> Module[{c=Unique[], d=Unique[]}, \[Epsilon]Ld[a,c]\[Epsilon]L[b,d]\[Sigma]b[\[Mu], c, d]],
  Conjugate[\[Sigma]b[\[Mu]_, a_, b_]] :> Module[{c=Unique[], d=Unique[]}, \[Epsilon]U[a,c]\[Epsilon]Ud[b,d]\[Sigma][\[Mu], c, d]]
} // ExpandAll // FillGrassmannIndices // Table[#, {\[Mu], 0, 3}, {\[Nu],0,3}, {a, 2}, {b, 2}]&



{\[Sigma][{\[Mu], \[Nu]}, a, b],\[Sigma]b[{\[Mu], \[Nu]}, a, b]}
Table[#, {a,2},{b,2}] &/@ %
ConjugateTranspose[%[[1]]] - %[[2]] // EvaluateDoublySigma // ExpandAll
Table[%/. {a_GrassmannDot :> FillGrassmannIndices[a]}, {\[Mu],0,3},{\[Nu],0,3}]


TestByFill[GrassmannDot[\[Theta][a],\[Theta][b]], (-1/2)\[Epsilon]U[a,b]GrassmannPair[\[Theta],\[Theta]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta][,a],\[Theta][,b]], (1/2)\[Epsilon]L[a,b]GrassmannPair[\[Theta],\[Theta]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta][a],\[Theta][,b]], (1/2)\[Delta][a,b]GrassmannPair[\[Theta],\[Theta]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta][a] ,\[Sigma][\[Mu], a, b], \[Sigma]b[\[Nu], b, c], \[Theta][,c]] // GrassmannContraction, \[Eta]U[\[Mu],\[Nu]] GrassmannPair[\[Theta], \[Theta]], {\[Mu], 0, 3}, {\[Nu], 0, 3}]

TestByFill[GrassmannDot[\[Theta]b[a],\[Theta]b[b]], (+1/2)\[Epsilon]Ud[a,b]GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta]b[,a],\[Theta]b[,b]], (-1/2)\[Epsilon]Ld[a,b]GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta]b[,a],\[Theta]b[b]], (1/2)\[Delta][OverDot[a],OverDot[b]]GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]], {a,2}, {b,2}]
TestByFill[GrassmannDot[\[Theta]b[,a], \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c], \[Theta]b[c]] // GrassmannContraction, \[Eta]U[\[Mu],\[Nu]] GrassmannPair[OverBar[\[Theta]], OverBar[\[Theta]]], {\[Mu], 0, 3}, {\[Nu], 0, 3}]

TestByFill[GrassmannPair[\[Theta],\[Phi]]GrassmannPair[\[Theta],\[Psi]], (-1/2)GrassmannPair[\[Psi],\[Phi]]GrassmannPair[\[Theta],\[Theta]]]
TestByFill[GrassmannPair[OverBar[\[Theta]],OverBar[\[Phi]]]GrassmannPair[OverBar[\[Theta]],OverBar[\[Psi]]], (-1/2)GrassmannPair[OverBar[\[Psi]],OverBar[\[Phi]]]GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]]]
TestByFill[GrassmannDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b]]GrassmannDot[\[Theta][c],\[Sigma][\[Nu],c,d],\[Theta]b[d]] // GrassmannContraction, (1/2)GrassmannPair[\[Theta],\[Theta]] GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]]\[Eta]U[\[Mu],\[Nu]], {\[Mu],0,3}, {\[Nu],0,3}]

TestByFill[GrassmannDot[\[Theta][a],\[Sigma][\[Nu],a,b],\[Theta]b[b], \[Theta][c]]// GrassmannContraction, (1/2)GrassmannPair[\[Theta],\[Theta]] GrassmannDot[\[Theta]b[,a],\[Sigma]b[\[Nu],a,c]], {\[Nu],0,3}, {c,2}]
TestByFill[GrassmannDot[\[Theta][a],\[Sigma][\[Nu],a,b],\[Theta]b[b], \[Theta]b[,c]]// GrassmannContraction, -(1/2)GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]] GrassmannDot[\[Theta][a],\[Sigma][\[Nu],a,c]], {\[Nu],0,3}, {c,2}]
TestByFill[GrassmannDot[\[Sigma][\[Mu],a,b], \[Theta]b[b], \[Theta][c], \[Sigma][\[Nu],c,d], \[Theta]b[d]]// GrassmannContraction, (1/2)GrassmannPair[OverBar[\[Theta]],OverBar[\[Theta]]] GrassmannDot[\[Sigma][\[Mu],a,b],\[Sigma]b[\[Nu],b,c],\[Theta][,c]], {\[Mu],0,3}, {\[Nu],0,3}, {a,2}]



ToMatrix[input_] := input /. {
  \[Sigma][a_]:>Table[\[Sigma][a,x,y],{x,2},{y,2}],
  \[Sigma]b[a_]:>Table[\[Sigma]b[a,x,y],{x,2},{y,2}],
  \[Eta][any__] :> \[Eta][any]{{1,0},{0,1}}
}
TestMatricesByFill[exp1_, exp2_, freeindices___] := Module[{diff, result, e1, e2, indices=Sequence@@(ReleaseHold/@{freeindices})},
  diff = ReleaseHold[ToMatrix[exp1]-ToMatrix[exp2]] // Flatten;
  result = AllTrue[TestByFill[#, 0, freeindices][[2]] &/@ diff, #&];
  If[result==True, AppendTo[ToTeX, exp1==exp2]];
  {exp1==exp2, result}]


TestMatricesByFill[\[Sigma][\[Mu]].\[Sigma]b[\[Nu]], \[Eta][{\[Mu],\[Nu]}, {}] - 2I \[Sigma][{\[Mu],\[Nu]}], {\[Mu],0,3}, {\[Nu],0,3}]
TestMatricesByFill[\[Sigma]b[\[Mu]].\[Sigma][\[Nu]], \[Eta][{\[Mu],\[Nu]}, {}] - 2I \[Sigma]b[{\[Mu],\[Nu]}], {\[Mu],0,3}, {\[Nu],0,3}]
TestMatricesByFill[\[Sigma][{\[Mu],\[Nu]}], -\[Sigma][{\[Nu],\[Mu]}], {\[Mu],0,3}, {\[Nu],0,3}]
TestMatricesByFill[\[Sigma]b[{\[Mu],\[Nu]}], -\[Sigma]b[{\[Nu],\[Mu]}], {\[Mu],0,3}, {\[Nu],0,3}]
TestByFill[TR[ToMatrix[\[Sigma]b[\[Mu]].\[Sigma][\[Nu]]]], TR[ToMatrix[\[Sigma][\[Mu]].\[Sigma]b[\[Nu]]]], {\[Mu],0,3},{\[Nu],0,3}]
TestByFill[TR[ToMatrix[\[Sigma]b[\[Mu]].\[Sigma][\[Nu]]]], 2\[Eta][{\[Mu],\[Nu]},{}], {\[Mu],0,3},{\[Nu],0,3}]
TestByFill[TR[ToMatrix[\[Sigma][{\[Mu], \[Nu]}]]], 0, {\[Mu],0,3},{\[Nu],0,3}]
TestByFill[TR[ToMatrix[\[Sigma]b[{\[Mu], \[Nu]}]]], 0, {\[Mu],0,3},{\[Nu],0,3}]


TestMatricesByFill[\[Sigma][\[Mu]].\[Sigma]b[\[Rho]].\[Sigma][\[Nu]] + \[Sigma][\[Nu]].\[Sigma]b[\[Rho]].\[Sigma][\[Mu]], 2(\[Eta][{\[Mu],\[Rho]}, {}].\[Sigma][\[Nu]]+\[Eta][{\[Nu],\[Rho]}, {}].\[Sigma][\[Mu]]-\[Eta][{\[Mu],\[Nu]}, {}].\[Sigma][\[Rho]]), {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}]
TestMatricesByFill[\[Sigma]b[\[Mu]].\[Sigma][\[Rho]].\[Sigma]b[\[Nu]] + \[Sigma]b[\[Nu]].\[Sigma][\[Rho]].\[Sigma]b[\[Mu]], 2(\[Eta][{\[Mu],\[Rho]}, {}].\[Sigma]b[\[Nu]]+\[Eta][{\[Nu],\[Rho]}, {}].\[Sigma]b[\[Mu]]-\[Eta][{\[Mu],\[Nu]}, {}].\[Sigma]b[\[Rho]]), {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}]
TestMatricesByFill[\[Sigma][\[Mu]].\[Sigma]b[\[Nu]].\[Sigma][\[Rho]] - \[Sigma][\[Rho]].\[Sigma]b[\[Nu]].\[Sigma][\[Mu]], SUM[2I \[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]] \[Eta][{}, {\[Xi],\[Alpha]}] \[Sigma][\[Alpha]], {\[Xi],0,3}, {\[Alpha],0,3}], {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}]
TestMatricesByFill[\[Sigma]b[\[Mu]].\[Sigma][\[Nu]].\[Sigma]b[\[Rho]] - \[Sigma]b[\[Rho]].\[Sigma][\[Nu]].\[Sigma]b[\[Mu]], SUM[-2I \[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]] \[Eta][{}, {\[Xi],\[Alpha]}] \[Sigma]b[\[Alpha]], {\[Xi],0,3}, {\[Alpha],0,3}], {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}]
TestByFill[TR[ToMatrix[\[Sigma][{\[Mu],\[Nu]}].\[Sigma][{\[Rho],\[Xi]}]]], ((1/2)(\[Eta][{\[Mu],\[Rho]},{}]\[Eta][{\[Nu],\[Xi]},{}] - \[Eta][{\[Mu],\[Xi]},{}]\[Eta][{\[Nu],\[Rho]},{}])+(-I/2)\[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]]) , {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}, {\[Xi],0,3}]
TestByFill[TR[ToMatrix[\[Sigma]b[{\[Mu],\[Nu]}].\[Sigma]b[{\[Rho],\[Xi]}]]], ((1/2)(\[Eta][{\[Mu],\[Rho]},{}]\[Eta][{\[Nu],\[Xi]},{}] - \[Eta][{\[Mu],\[Xi]},{}]\[Eta][{\[Nu],\[Rho]},{}])+(I/2)\[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]]) , {\[Mu],0,3}, {\[Nu],0,3}, {\[Rho],0,3}, {\[Xi],0,3}]


TestByFill[GrassmannDot[GrassmannTensor[OverBar[\[Xi]], {}, {""}], \[Sigma]b[\[Mu],"",""], GrassmannTensor[\[Chi], {}, {""}]], -GrassmannDot[GrassmannTensor[\[Chi], {""}, {}], \[Sigma][\[Mu],"",""], GrassmannTensor[OverBar[\[Xi]], {""}, {}]], {\[Mu],0,3}]


TestByFill[SUM[\[Eta][{},{\[Mu],\[Nu]}]\[Sigma][\[Mu],a,b]\[Sigma]b[\[Nu],c,d],{\[Mu],0,3},{\[Nu],0,3}],  2\[Delta][a,d]\[Delta][b,c], {a,2},{b,2},{c,2},{d,2}]
TestByFill[SUM[\[Eta][{},{\[Mu],\[Nu]}]\[Sigma][\[Mu],a,b]\[Sigma][\[Nu],c,d],{\[Mu],0,3},{\[Nu],0,3}],  2\[Epsilon]L[a,c]\[Epsilon]L[b,d], {a,2},{b,2},{c,2},{d,2}]
TestByFill[SUM[\[Eta][{},{\[Mu],\[Nu]}]\[Sigma]b[\[Mu],a,b]\[Sigma]b[\[Nu],c,d],{\[Mu],0,3},{\[Nu],0,3}],  2\[Epsilon]U[a,c]\[Epsilon]U[b,d], {a,2},{b,2},{c,2},{d,2}]
TestByFill[GrassmannDot[\[Sigma][{\[Mu],\[Nu]},a,b], \[Epsilon]L[b,c]], GrassmannDot[\[Sigma][{\[Mu],\[Nu]},c,b], \[Epsilon]L[b,a]], {a,2}, {c,2}, {\[Mu],0,3},{\[Nu],0,3}]
TestByFill[GrassmannDot[\[Sigma]b[{\[Mu],\[Nu]},a,b], \[Epsilon]Ud[b,c]], GrassmannDot[\[Sigma]b[{\[Mu],\[Nu]},c,b], \[Epsilon]Ud[b,a]], {a,2}, {c,2}, {\[Mu],0,3},{\[Nu],0,3}]


TestByFill[
  GrassmannDot[\[Sigma][\[Mu],a,b], \[Sigma][\[Nu],c,d]] - GrassmannDot[\[Sigma][\[Nu],a,b], \[Sigma][\[Mu],c,d]],
  -2I GrassmannDot[\[Sigma][{\[Mu],\[Nu]},a,""], \[Epsilon]L["",c], \[Epsilon]Ld[b,d]]-2I GrassmannDot[\[Epsilon]Ld[b,""], \[Sigma]b[{\[Mu],\[Nu]},"",d], \[Epsilon]L[a,c]], {a,2},{b,2},{c,2},{d,2},{\[Mu],0,3},{\[Nu],0,3}]
TestByFill[
  GrassmannDot[\[Sigma][\[Mu],a,b], \[Sigma][\[Nu],c,d]] + GrassmannDot[\[Sigma][\[Nu],a,b], \[Sigma][\[Mu],c,d]],
  \[Eta][{\[Mu],\[Nu]}, {}]\[Epsilon]L[a,c]\[Epsilon]Ld[b,d]+4SUM[\[Eta][{}, {\[Rho],\[Xi]}] GrassmannDot[\[Sigma][{\[Rho],\[Mu]},a,""], \[Epsilon]L["",c],\[Epsilon]Ld[b,""]\[Sigma]b[{\[Xi],\[Nu]},"",d]], {\[Rho],0,3},{\[Xi],0,3}],
   {a,2},{b,2},{c,2},{d,2},{\[Mu],0,3},{\[Nu],0,3}]


ToTeX={}
TestByFill[
  GrassmannDot[\[Sigma]b[\[Mu],a,b], \[Sigma]b[\[Nu],c,d]] - GrassmannDot[\[Sigma]b[\[Nu],a,b], \[Sigma]b[\[Mu],c,d]],
  -2I GrassmannDot[\[Sigma]b[{\[Mu],\[Nu]},a,""], \[Epsilon]Ud["",c], \[Epsilon]U[b,d]]-2I GrassmannDot[\[Epsilon]U[b,""], \[Sigma][{\[Mu],\[Nu]},"",d], \[Epsilon]Ud[a,c]], {a,2},{b,2},{c,2},{d,2},{\[Mu],0,3},{\[Nu],0,3}]
TestByFill[
  GrassmannDot[\[Sigma]b[\[Mu],a,b], \[Sigma]b[\[Nu],c,d]] + GrassmannDot[\[Sigma]b[\[Nu],a,b], \[Sigma]b[\[Mu],c,d]],
  \[Eta][{\[Mu],\[Nu]}, {}]\[Epsilon]Ud[a,c]\[Epsilon]U[b,d]+4SUM[\[Eta][{}, {\[Rho],\[Xi]}] GrassmannDot[\[Sigma]b[{\[Rho],\[Mu]},a,y], \[Epsilon]Ud[y,c],\[Epsilon]U[b,x]\[Sigma][{\[Xi],\[Nu]},x,d]], {\[Rho],0,3},{\[Xi],0,3}],
   {a,2},{b,2},{c,2},{d,2},{\[Mu],0,3},{\[Nu],0,3}]


TestByFill[Sum[\[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]]\[Sigma][{\[Alpha],\[Beta]}, a,b]\[Eta]L[\[Alpha],\[Rho]]\[Eta]L[\[Beta],\[Xi]], {\[Alpha],0,3}, {\[Beta],0,3}, {\[Rho],0,3},{\[Xi],0,3}], 2I \[Sigma][{\[Mu],\[Nu]}, a,b], {\[Mu],0,3},{\[Nu],0,3},{a,2},{b,2}]
TestByFill[Sum[\[Epsilon]4U[\[Mu],\[Nu],\[Rho],\[Xi]]\[Sigma]b[{\[Alpha],\[Beta]}, a,b]\[Eta]L[\[Alpha],\[Rho]]\[Eta]L[\[Beta],\[Xi]], {\[Alpha],0,3}, {\[Beta],0,3}, {\[Rho],0,3},{\[Xi],0,3}], -2I \[Sigma]b[{\[Mu],\[Nu]}, a,b], {\[Mu],0,3},{\[Nu],0,3},{a,2},{b,2}]



