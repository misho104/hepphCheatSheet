#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Subsection:: *)
(*Common tools*)


$ExtraNameType = _P|_PC|_P2|_P4|_S|_SC|_S2|_F|_FC|_V;

SetDirectory[NotebookDirectory[]];
<<WeylAlgebra`
 
SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];

TDotOrder$Fields = <|"Hu"->1, "HuP"->2, "HuZ"->3, "Hd"->4, "HdZ"->5, "HdM"->6, "bU"->11, "bD"->12, "bE"->13, "Q"->21, "UL"->23, "DL"->24, "L"->25, "NUL"->27, "EL"->28, "Bi"->51, "Wi"->52, "WiP"->53, "WiM"->54, "Wi3"->55, "Gi"->57, "B"->101, "W"->102, "WP"->103, "WM"->104, "W3"->105, "g"->106|>;
TDotOrder$Indices = <|"Gen"->0, "SU2I"->1, "SU3I"->3, "SU2F"->2, "SU3F"->4|>;
TDotOrder$Params = <|"\[Mu]"->10, "yu"->11, "yd"->12, "ye"->13, "\[Kappa]"->101, "\[Lambda]"->102, "\[Lambda]p"->103, "\[Lambda]pp"->104|>;
TDotOrder[exp_] := Switch[exp,
  _?NumericQ, {-100, 0, exp},
  NT[P["\[Sigma]bmu"]], {35, 0, exp},
  NT["\[Epsilon]", ___],  {-2, TDotOrder$Indices[exp[[-1,2]]], exp},
  NT["f", ___],  {-2, TDotOrder$Indices[exp[[-1,2]]], exp},
  NT[(P|PC|P2|P4)["gY"]],   {-10, 1, exp},
  NT[(P|PC|P2|P4)["g2"]],   {-10, 2, exp},
  NT[(P|PC|P2|P4)["g3"]],   {-10, 3, exp},
  NT[(P|PC|P2|P4)[_], ___], {-1, TDotOrder$Params[exp[[1,1]]], exp},
  NT[_[dx[_]], ___], Module[{tmp=TDotOrder[exp/.dx:>(#&)]}, {tmp[[1]]+10, tmp[[2]], exp}],
  NT[S[_], ___],  {32, TDotOrder$Fields[exp[[1,1]]], exp},
  NT[SC[_], ___], {31, TDotOrder$Fields[exp[[1,1]]], exp},
  NT[F[_], ___],  {36, TDotOrder$Fields[exp[[1,1]]], exp},
  NT[FC[_], ___], {33, TDotOrder$Fields[exp[[1,1]]], exp},
  NT[V[_], ___],  {39, TDotOrder$Fields[exp[[1,1]]], exp},
  _,    {0, 0, exp}]
SortTDot[TDot[exp__]] := TDot @@ SortBy[{exp}, TDotOrder]
SortTDot[exp_] := exp /. {f_TDot :> SortTDot[f]}

RewriteIndicesOrder[exp_] := Module[{f = TDotOrder[exp]}, {-f[[1]], f[[2;;]]}]
RewriteIndices[exp_, format_, indices_:Null] :=
  Module[{rep, old, nottoreplace, toreplace, new, rule},
    rep = exp //. TDot[a__]:>TDotList@@SortBy[{a}, RewriteIndicesOrder];
    old = Cases[rep,  format :> index, All] // Select[#, FreeQ[#, _Integer]&]&;
    nottoreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 1) :> p] &;
    toreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 2) :> p] &;
    new = If[indices===Null, If[Head[#]===OverDot, OverDot[Unique[]], Unique[]]& /@ toreplace, Select[indices, FreeQ[nottoreplace, #] &]];
    If[Length[toreplace] > Length[new], Return[exp]];
    rule = (#[[1]] -> #[[2]]) & /@ Transpose[{toreplace, new[[1 ;; Length[toreplace]]]}];
    exp /. rule];

RewriteIndices[exp_] := Module[{result},
  result = SumToList[exp];
  result = RewriteIndices[#, (UI|LI)[index_, "lorentz"], {"\[Mu]", "\[Nu]", "\[Rho]", "\[CapitalSigma]", "\[Alpha]", "\[Beta]", "\[Gamma]"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "Gen"],  {"i", "j", "k", "l", "m", "n"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU2I"], {"a", "b", "c", "d", "e", "f"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU2F"], {"A", "B", "C", "D", "E", "F"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU3I"], {"x", "y", "z", "w", "v"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU3F"], {"X", "Y", "Z", "W", "V"}] & /@ result;
  Total[result]
];

RenewIndices[exp_] := Module[{result},
  result = SumToList[exp];
  result = RewriteIndices[#, (UI|LI)[index_, "lorentz"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "Gen"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU2I"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU2F"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU3I"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "SU3F"]] & /@ result;
  Total[result]
];

SymmetrizeIndices[exp_, {a_, b_}] := (exp + (exp /. {a->b, b->a}))/2

LorentzSort[exp_] := (exp//.{
  (p:NT|GT)[x1__, LI[\[Mu]_,"lorentz"], x2___]/; FreeQ[{x1}, "\[Eta]"] :> Module[{\[Nu]=Unique[]}, \[Eta]L[\[Mu], \[Nu]] p[x1, UI[\[Nu],"lorentz"], x2]]
}//SortTDot//RewriteIndices)//.NT[HoldForm["\[Eta]"], a_, b_] /; Not[OrderedQ[{a,b}]] :> NT[HoldForm["\[Eta]"], b, a]//ReleaseHoldAll;


ToTeX = {};
Express::usage = "";
Attributes[Express] = {HoldFirst};
Express[exphold_, apply_:(#&), hold_:True] := If[hold=!=True, Express[exphold//Evaluate, apply, True], Module[{exp},
  exp = ReleaseHoldAll[exphold] // RewriteIndices // OrderTheta[#,apply]&;
  AppendTo[ToTeX, HoldForm[exphold] == exp];
  exp]]


(* ::Subsection:: *)
(*Definitions*)


Delete[MakeBoxesNT$fields];
Sequence[NT, _SF|_F|_S|_V|_P|_SFC|_FC|_SC|_PC|_P2|_S2|_P4, RepeatedNull[WeylAlgebra`Private`IndexType]] // (#1 /: MakeBoxes[obj: #1[n:#2|HoldForm[#2], i:#3], f:StandardForm|TraditionalForm] := MakeBoxesNT$fields[f, #&, n, i] // ToBoxes // InterpretationBox[#,obj] &) &;
MakeBoxesNT$fields[f_, c_, SF[n_], any___] := MakeBoxesNT$fields[f, Style[#, Blue]&, n, any]
MakeBoxesNT$fields[f_, c_, P[n_], any___] := MakeBoxesNT$fields[f, #&, n, any]
MakeBoxesNT$fields[f_, c_, (S|V)[n_], any___] := MakeBoxesNT$fields[f, Style[#, Black]&, n, any]
MakeBoxesNT$fields[f_, c_, F[n_], any___] := MakeBoxesNT$fields[f, Style[#, Red]&, n, any]

MakeBoxesNT$fields[f_, c_, SFC[n_], any___] := MakeBoxesNT$fields[f, Superscript[Style[#, Blue], "*"]&, n, any]
MakeBoxesNT$fields[f_, c_, PC[n_], any___] := MakeBoxesNT$fields[f, Superscript[#, "*"]&, n, any]
MakeBoxesNT$fields[f_, c_, P2[n_], any___] := MakeBoxesNT$fields[f, Superscript[#, "2"]&, n, any]
MakeBoxesNT$fields[f_, c_, P4[n_], any___] := MakeBoxesNT$fields[f, Superscript[#, "4"]&, n, any]
MakeBoxesNT$fields[f_, c_, SC[n_], any___] := MakeBoxesNT$fields[f, Superscript[Style[#, Black], "*"]&, n, any]
MakeBoxesNT$fields[f_, c_, S2[n_], any___] := MakeBoxesNT$fields[f, Superscript[Style[#, Black], "2"]&, n, any]
MakeBoxesNT$fields[f_, c_, FC[n_], any___] := MakeBoxesNT$fields[f, Superscript[Style[#, Red], "*"]&, n, any]

MakeBoxesNT$fields[f_, c_, dx[n_], UI[\[Mu]_, "lorentz"], any___] := Row[{Superscript["\[PartialD]", \[Mu]], MakeBoxesNT$fields[f, c, n, any]}]
MakeBoxesNT$fields[f_, c_, dx[n_], LI[\[Mu]_, "lorentz"], any___] := Row[{Subscript["\[PartialD]", \[Mu]], MakeBoxesNT$fields[f, c, n, any]}]
MakeBoxesNT$fields[f_, c_, dx2[n_], any___] := Row[{Superscript["\[PartialD]", 2], MakeBoxesNT$fields[f, c, n, any]}]

MakeBoxesNT$fields[exp___] := WeylAlgebra`Private`MakeBoxesNT$[exp]

WeylAlgebra`MakeBoxesNT = MakeBoxesNT$fields;


(* Because spinor indices appear only in kinetic terms and no 4-fermion interactions at this level,
   we do not have to treat spinor indices; all fields are now non-grassmannian. *)

tQQ[i_, a_, x_] := NT[S["Q"], NI[i, "Gen"], NI[a, "SU2I"], NI[x, "SU3I"]]
tbU[i_,     x_] := NT[S["bU"], NI[i, "Gen"], NI[x, "SU3I"]]
tbD[i_,     x_] := NT[S["bD"], NI[i, "Gen"], NI[x, "SU3I"]]
tLL[i_, a_] := NT[S["L"], NI[i, "Gen"], NI[a, "SU2I"]]
tbE[i_] := NT[S["bE"], NI[i, "Gen"]]
Hu[a_] := NT[S["Hu"], NI[a, "SU2I"]]
Hd[a_] := NT[S["Hd"], NI[a, "SU2I"]]

QQ[i_, a_, x_] := NT[F["Q"], NI[i, "Gen"], NI[a, "SU2I"], NI[x, "SU3I"]]
bU[i_,     x_] := NT[F["bU"], NI[i, "Gen"], NI[x, "SU3I"]]
bD[i_,     x_] := NT[F["bD"], NI[i, "Gen"], NI[x, "SU3I"]]
LL[i_, a_] := NT[F["L"], NI[i, "Gen"], NI[a, "SU2I"]]
bE[i_] := NT[F["bE"], NI[i, "Gen"]]
tHu[a_] := NT[F["Hu"], NI[a, "SU2I"]]
tHd[a_] := NT[F["Hd"], NI[a, "SU2I"]]

NT[(t:S|SC|F|FC)["Q"],x1___, NI[1,"SU2I"], x2___] := NT[t["UL"],x1,x2]
NT[(t:S|SC|F|FC)["Q"],x1___, NI[2,"SU2I"], x2___] := NT[t["DL"],x1,x2]
NT[(t:S|SC|F|FC)["L"],x1___, NI[1,"SU2I"], x2___] := NT[t["NUL"],x1,x2]
NT[(t:S|SC|F|FC)["L"],x1___, NI[2,"SU2I"], x2___] := NT[t["EL"],x1,x2]
NT[(t:S|SC|F|FC)["Hu"],x1___, NI[1,"SU2I"], x2___] := NT[t["HuP"],x1,x2]
NT[(t:S|SC|F|FC)["Hu"],x1___, NI[2,"SU2I"], x2___] := NT[t["HuZ"],x1,x2]
NT[(t:S|SC|F|FC)["Hd"],x1___, NI[1,"SU2I"], x2___] := NT[t["HdZ"],x1,x2]
NT[(t:S|SC|F|FC)["Hd"],x1___, NI[2,"SU2I"], x2___] := NT[t["HdM"],x1,x2]
NT[(t:S|SC|F|FC)[dx["Q"]],x1___, NI[1,"SU2I"], x2___] := NT[t[dx["UL"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["Q"]],x1___, NI[2,"SU2I"], x2___] := NT[t[dx["DL"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["L"]],x1___, NI[1,"SU2I"], x2___] := NT[t[dx["NUL"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["L"]],x1___, NI[2,"SU2I"], x2___] := NT[t[dx["EL"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["Hu"]],x1___, NI[1,"SU2I"], x2___] := NT[t[dx["HuP"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["Hu"]],x1___, NI[2,"SU2I"], x2___] := NT[t[dx["HuZ"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["Hd"]],x1___, NI[1,"SU2I"], x2___] := NT[t[dx["HdZ"]],x1,x2]
NT[(t:S|SC|F|FC)[dx["Hd"]],x1___, NI[2,"SU2I"], x2___] := NT[t[dx["HdM"]],x1,x2]

BB[\[Mu]_]  := NT[V["B"], UI[\[Mu], "lorentz"]]
BB[,\[Mu]_] := NT[V["B"], LI[\[Mu], "lorentz"]]
WW[\[Mu]_, A_] := NT[V["W"], UI[\[Mu], "lorentz"], NI[A, "SU2F"]]
WW[,\[Mu]_,A_] := NT[V["W"], LI[\[Mu], "lorentz"], NI[A, "SU2F"]]
GG[\[Mu]_, X_] := NT[V["g"], UI[\[Mu], "lorentz"], NI[X, "SU3F"]]
GG[,\[Mu]_,X_] := NT[V["g"], LI[\[Mu], "lorentz"], NI[X, "SU3F"]]
Bi[] := NT[F["Bi"]]
Wi[A_] := NT[F["Wi"], NI[A, "SU2F"]]
Gi[X_] := NT[F["Gi"], NI[X, "SU3F"]]

MatterFields = {"Q", "bU", "bD", "L", "bE", "Hu", "Hd"};
U1Charges = <|"Q"->1/6, "bU"->-2/3, "bD"->1/3, "L"->-1/2, "bE"->1, "Hu"->1/2, "Hd"->-1/2|>;
SU2Charges = <|"Q"->T, "bU"->0, "bD"->0, "L"->T, "bE"->0, "Hu"->T, "Hd"->T|>;
SU3Charges = <|"Q"->\[Tau], "bU"->\[Tau]C, "bD"->\[Tau]C, "L"->0, "bE"->0, "Hu"->0, "Hd"->0|>;
T [A_,a_,b_] := NT["T", NI[A, "SU2F"], NI[a,"SU2I"], NI[b,"SU2I"]]
\[Tau] [X_,x_,y_] := NT["\[Tau]", NI[X, "SU3F"], NI[x,"SU3I"], NI[y,"SU3I"]]

NT["T", NI[A_Integer, "SU2F"], NI[a_Integer,"SU2I"], NI[b_Integer,"SU2I"]] := PauliMatrix[A][[a,b]]/2

\[Epsilon][a_, b_] := NT["\[Epsilon]", NI[a, "SU2I"], NI[b, "SU2I"]]
\[Epsilon][x_, y_, z_] := NT["\[Epsilon]", NI[x, "SU3I"],  NI[y, "SU3I"],  NI[z, "SU3I"]]

NT["\[Epsilon]", NI[1, "SU2F"], NI[2, "SU2F"], NI[3, "SU2F"]] := 1
NT["\[Epsilon]", NI[1, "SU2I"], NI[2, "SU2I"]] := 1

fieldType = S | F | V | SC | FC;

Dx[\[Mu]_,  obj:NT[(ft:fieldType)[field_], any___]] := NT[ft[dx[field]], UI[\[Mu], "lorentz"], any]
Dx[,\[Mu]_, obj:NT[(ft:fieldType)[field_], any___]] := NT[ft[dx[field]], LI[\[Mu], "lorentz"], any]
NT[(ft:fieldType)[dx[dx[field_]]], x1___, UI[\[Mu]_, "lorentz"], x2___, LI[\[Mu]_, "lorentz"], x3___] /; FreeQ[{x2}, "lorentz"] := NT[ft[dx2[field]], x1, x2, x3]
NT[(ft:fieldType)[dx[dx[field_]]], x1___, LI[\[Mu]_, "lorentz"], x2___, UI[\[Mu]_, "lorentz"], x3___] /; FreeQ[{x2}, "lorentz"] := NT[ft[dx2[field]], x1, x2, x3]

ProdT[NT[f_, x1___, NI[a_, "SU2I"], x2___], A_] /; FreeQ[{x1, x2}, "SU2I"] := Module[{b=Unique["a"]}, T[A, a, b] NT[f, x1, NI[b, "SU2I"], x2]]
Prod\[Tau][NT[f_, x1___, NI[a_, "SU3I"], x2___], A_] /; FreeQ[{x1, x2}, "SU3I"] := Module[{b=Unique["x"]}, \[Tau][A, a, b] NT[f, x1, NI[b, "SU3I"], x2]]
Prod\[Tau]C[NT[f_, x1___, NI[a_, "SU3I"], x2___], A_] /; FreeQ[{x1, x2}, "SU3I"] := Module[{b=Unique["x"]}, -Conjugate[\[Tau][A, a, b]] NT[f, x1, NI[b, "SU3I"], x2]]
DDx[\[Mu]__, obj:NT[(ft:fieldType)[field_], any___]] /; MemberQ[MatterFields, field] := Module[{
  u1 = U1Charges[field], su2 = SU2Charges[field], su3 = SU3Charges[field]},
  Total[{
    Dx[\[Mu], obj],
    - I NT[P["gY"]] BB[\[Mu]] u1 obj,
    If[su2===T, Module[{A=Unique["A"]}, - I NT[P["g2"]] WW[\[Mu], A] ProdT[obj, A]], 0],
    If[su3===\[Tau], Module[{X=Unique["X"]}, - I NT[P["g3"]] GG[\[Mu], X] Prod\[Tau][obj, X]], 0],
    If[su3===\[Tau]C, Module[{X=Unique["X"]}, - I NT[P["g3"]] GG[\[Mu], X] Prod\[Tau]C[obj, X]], 0]
  }]]

FFB[\[Mu]_, \[Nu]_] := Dx[\[Mu], BB[\[Nu]]] - Dx[\[Nu], BB[\[Mu]]]
FFB[,\[Mu]_, \[Nu]_] := Dx[,\[Mu], BB[,\[Nu]]] - Dx[,\[Nu], BB[,\[Mu]]]
FFW[\[Mu]_, \[Nu]_, A_] := Dx[\[Mu], WW[\[Nu], A]] - Dx[\[Nu], WW[\[Mu], A]] + Module[{B=Unique["A"], C=Unique["A"]}, NT[P["g2"]] NT["\[Epsilon]", NI[A, "SU2F"],  NI[B, "SU2F"], NI[C, "SU2F"]] WW[\[Mu],B]WW[\[Nu],C]]
FFW[,\[Mu]_, \[Nu]_, A_] := Dx[,\[Mu], WW[,\[Nu], A]] - Dx[,\[Nu], WW[,\[Mu], A]] + Module[{B=Unique["A"], C=Unique["A"]}, NT[P["g2"]] NT["\[Epsilon]", NI[A, "SU2F"],  NI[B, "SU2F"], NI[C, "SU2F"]] WW[,\[Mu],B]WW[,\[Nu],C]]
FFG[\[Mu]_, \[Nu]_, A_] := Dx[\[Mu], GG[\[Nu], A]] - Dx[\[Nu], GG[\[Mu], A]] + Module[{B=Unique["A"], C=Unique["A"]}, NT[P["g3"]] NT["f", NI[A, "SU3F"],  NI[B, "SU3F"], NI[C, "SU3F"]] GG[\[Mu],B]GG[\[Nu],C]]
FFG[,\[Mu]_, \[Nu]_, A_] := Dx[,\[Mu], GG[,\[Nu], A]] - Dx[,\[Nu], GG[,\[Mu], A]] + Module[{B=Unique["A"], C=Unique["A"]}, NT[P["g3"]] NT["f", NI[A, "SU3F"],  NI[B, "SU3F"], NI[C, "SU3F"]] GG[,\[Mu],B]GG[,\[Nu],C]]

Dx[var__, Plus[a_, b__]] := Dx[var, a] + Dx[var, Plus[b]]
Dx[var__, Times[a:(_String|_?NumericQ), b__]] := a Dx[var, Times[b]]
Dx[var__, (_String|_?NumericQ)] := 0
Dx[var__, NT[P[_]|"\[Tau]"|"T"|"\[Epsilon]"|"f", ___]] := 0
Dx[var__, TDot[exp__]] := TDot[Dx$operator[var], exp]
TDot[x1___, Dx$operator[var__], x2_, x3___] := TDot[x1, Dx[var, x2], x3] + TDot[x1, x2, Dx$operator[var], x3]
TDot[x1___, Dx$operator[var__]] := 0

SU2Replace[exp_] := exp //. {
  NT[V[dx["W"]],a:_[_,"lorentz"],b:_[_,"lorentz"],NI[1,"SU2F"]] :> (NT[V[dx["WP"]], a, b]+NT[V[dx["WM"]], a, b])/Sqrt[2],
  NT[V[dx["W"]],a:_[_,"lorentz"],b:_[_,"lorentz"],NI[2,"SU2F"]] :> (NT[V[dx["WM"]], a, b]-NT[V[dx["WP"]], a, b])/(Sqrt[2]I),
  NT[V[dx["W"]],a:_[_,"lorentz"],b:_[_,"lorentz"],NI[3,"SU2F"]] :> NT[V[dx["W3"]], a, b],
  NT[V["W"],a:_[_,"lorentz"],NI[1,"SU2F"]] :> (NT[V["WP"], a]+NT[V["WM"], a])/Sqrt[2],
  NT[V["W"],a:_[_,"lorentz"],NI[2,"SU2F"]] :> (NT[V["WM"], a]-NT[V["WP"], a])/(Sqrt[2]I),
  NT[V["W"],a:_[_,"lorentz"],NI[3,"SU2F"]] :> NT[V["W3"], a],
  NT[F["Wi"],NI[1,"SU2F"]] :> (NT[F["WiP"]]+NT[F["WiM"]])/Sqrt[2],
  NT[F["Wi"],NI[2,"SU2F"]] :> (NT[F["WiM"]]-NT[F["WiP"]])/(Sqrt[2]I),
  NT[F["Wi"],NI[3,"SU2F"]] :> NT[F["Wi3"]],
  NT[FC["Wi"],NI[1,"SU2F"]] :> (NT[FC["WiP"]]+NT[FC["WiM"]])/Sqrt[2],
  NT[FC["Wi"],NI[2,"SU2F"]] :> (NT[FC["WiM"]]-NT[FC["WiP"]])/(-Sqrt[2]I),
  NT[FC["Wi"],NI[3,"SU2F"]] :> NT[FC["Wi3"]],
  NT[V["W3"], any___] :> TDot[NT[P["cw"]], NT[V["Z"], any]] + TDot[NT[P["sw"]], NT[V["A"], any]],
  NT[V["B"], any___] :> TDot[-NT[P["sw"]], NT[V["Z"], any]] + TDot[NT[P["cw"]], NT[V["A"], any]],
  NT[V[dx["W3"]], any___] :> TDot[NT[P["cw"]], NT[V[dx["Z"]], any]] + TDot[NT[P["sw"]], NT[V[dx["A"]], any]],
  NT[V[dx["B"]], any___] :> TDot[-NT[P["sw"]], NT[V[dx["Z"]], any]] + TDot[NT[P["cw"]], NT[V[dx["A"]], any]]
}

SuperPotential = Module[{param=Function[{x, y}, NT[P[x], Sequence@@(NI[#, "Gen"] &/@ y)]]}, Total[{ 
  +param["\[Mu]", {}]      * \[Epsilon][a,b] * Hu[a]   * Hd[b],
  -param["yu", {i, j}] * \[Epsilon][a,b] * bU[i,x] * Hu[a] * QQ[j,b,x],
  +param["yd", {i, j}] * \[Epsilon][a,b] * bD[i,x] * Hd[a] * QQ[j,b,x],
  +param["ye", {i, j}] * \[Epsilon][a,b] * bE[i]   * Hd[a] * LL[j,b],
  -param["\[Kappa]", {i}]     * \[Epsilon][a,b] * LL[i,a] * Hu[b],
  (1/2)param["\[Lambda]",   {i,j,k}] * \[Epsilon][a,b] * LL[i,a] * LL[j,b]   * bE[k],
       param["\[Lambda]p",  {i,j,k}] * \[Epsilon][a,b] * LL[i,a] * QQ[j,b,x] * bD[k,x],
  (1/2)param["\[Lambda]pp", {i,j,k}] * \[Epsilon][x,y,z] * bU[i,x] * bD[j,y] * bD[k,z]
}]] //. {S|F->SF};

NT[P["\[Lambda]"],   i_, j_, k_] /; Not[OrderedQ[{i,j}]] := (-1)NT[P["\[Lambda]"],   j, i, k]
NT[P["\[Lambda]pp"], i_, j_, k_] /; Not[OrderedQ[{j,k}]] := (-1)NT[P["\[Lambda]pp"], i, k, j]
NT["f", a___, b_, c_, d___] /; Not[OrderedQ[{b,c}]] := (-1)NT["f", a,c,b,d]
NT["\[Epsilon]", a___, b_, c_, d___] /; Not[OrderedQ[{b,c}]] := (-1)NT["\[Epsilon]", a,c,b,d]

DWD\[CapitalPhi][field_] := Module[{delta, result = SuperPotential /. SF->S},
  result = result /. NT[S[field], any___] :> NT[S[field], any] + delta (Times@@(\[Delta][#[[1]], Null, #[[2]]]&/@{any})) // Coefficient[#, delta, 1]&;
  ReleaseHoldAll[result] /. {NI[Null, "Gen"]->NI["i", "Gen"], NI[Null, "SU2I"]->NI["a", "SU2I"], NI[Null, "SU3I"]->NI["x", "SU3I"]}]

NT /: Conjugate[f:NT["\[Epsilon]", ___]] := f
NT /: Conjugate[NT[f:(fieldType|P|P2|SF|SFC)[__], x___]] := NT[Conj[f], x]
NT /: Conjugate[NT["T", NI[a_, "SU2F"], NI[i_, "SU2I"], NI[j_, "SU2I"]]] := T[a,j,i]
NT /: Conjugate[NT["\[Tau]", NI[a_, "SU3F"], NI[i_, "SU3I"], NI[j_, "SU3I"]]] := \[Tau][a,j,i]
Conj[S[a__]] := SC[a]
Conj[SC[a__]] := S[a]
Conj[F[a__]] := FC[a]
Conj[FC[a__]] := F[a]
Conj[V[a__]] := V[a]
Conj[P[a__]] := PC[a]
Conj[PC[a__]] := P[a]
Conj[SF[a__]] := SFC[a]
Conj[SFC[a__]] := SF[a]
RealParameters = "gY"|"g2"|"g3"|"cw"|"sw";
PC[real:RealParameters] := P[real]
TDot/: TDot[x:OrderlessPatternSequence[any___,
           NT[P[name_], indices___],
           NT[PC[name_], indices___]]] := TDot[any, NT[P2[name]]]
(*
TDot /: TDot[x:OrderlessPatternSequence[any___,
           NT[S[name_], indices___],
           NT[SC[name_], indices___]]] := TDot[any, NT[S2[name]]]
*)
TDot /: TDot[x:OrderlessPatternSequence[any___,
           NT[P[name_], indices___],
           NT[P[name_], indices___]]] /; MatchQ[name, RealParameters] := TDot[any, NT[P2[name]]]
NT[P2["cw"]] := 1-NT[P2["sw"]]


Lvector = Total[{
  (-1/4)FFB[\[Mu],\[Nu]]FFB[,\[Mu],\[Nu]],
  (-1/4)FFW[\[Mu],\[Nu],a]FFW[,\[Mu],\[Nu],a],
  (-1/4)FFG[\[Mu],\[Nu],a]FFG[,\[Mu],\[Nu],a],
  NT[P["g3"]]^2*NT[P["\[CapitalTheta]G"]]/(64\[Pi]^2)*NT["\[Epsilon]", LI[\[Mu],"lorentz"], LI[\[Nu],"lorentz"], LI[\[Rho],"lorentz"],  LI[\[CapitalSigma],"lorentz"]] FFG[\[Mu],\[Nu],a]FFG[\[Rho],\[CapitalSigma],\[Alpha]]
  }] // ReleaseHoldAll // ExpandAll // SortTDot // LorentzSort // RewriteIndices // SortTDot// RewriteIndices
LvectorSU2expanded = Lvector // FillIndices[#, {"SU2F"}]& // SU2Replace // ExpandAll // SortTDot // LorentzSort // RewriteIndices // SortTDot // LorentzSort// RewriteIndices;


ToTeXString[TDot[exp___]] := StringJoin[ToTeXString/@{exp}]
ToTeXString[NT["\[Epsilon]", indices___]] := ToTeXString$["\\epsilon", indices]
ToTeXString[NT["f", indices___]] := ToTeXString$["f", indices]
ToTeXString[NT["\[Tau]", indices___]] := ToTeXString$["P:\\tau", indices]
ToTeXString[NT[(tag:S|SC|F|FC|V|P|PC|P2|P4|S2)[f_String], indices___]] := ToTeXString$[TextString[tag]<>":"<>f, indices]
ToTeXString[NT[(tag:S|SC|F|FC|V)[dx[f_String]], lor:(UI|LI)[_, "lorentz"], indices___]] := ToTeXString$["P:partial", lor] <> ToTeXString[NT[tag[f], indices]]

ToTeXString$[name_, indices___] := StringJoin[{
  "@", name,
  ":",
  StringJoin[Cases[{indices}, LI[x_, "lorentz"] :> x]],
  StringJoin[Cases[{indices}, NI[x_, "Gen"] :> x]],
  ":",
  StringJoin[Cases[{indices}, NI[x_, "SU2I"] :> TextString[x]]] // ToTeXString$ReplaceIndices,
  StringJoin[Cases[{indices}, NI[x_, "SU2F"] :> TextString[x]]] // ToTeXString$ReplaceIndices,
  StringJoin[Cases[{indices}, NI[x_, "SU3I"] :> TextString[x]]] // ToTeXString$ReplaceIndices,
  StringJoin[Cases[{indices}, NI[x_, "SU3F"] :> TextString[x]]] // ToTeXString$ReplaceIndices,
  StringJoin[Cases[{indices}, UI[x_, "lorentz"] :> x]],
  "@"}]
ToTeXString$ReplaceIndices[exp_] := StringReplace[exp, {"A"|"X"->"a", "B"|"Y"->"b", "C"|"Z"->"c", "D"|"V"->"d", "E"|"W"->"e"}]
ToTeXString[exp_] := SumToList[exp] //. Times -> TIMES //. {
    Complex[a_, b_] :> ToString[TeXForm[a+b "ii"]],
    Power[2,Rational[-1,2]] :> "\\frac{1}{\\sqrt2}",
    Power[2,Rational[1,2]] :> "{\\sqrt2}",
    a_Rational :> ToString[TeXForm[a]],
    a_Integer :> "("<>ToString[TeXForm[a]]<>")",
    a_TDot:>ToTeXString[a]
} //. TIMES[a___] :> StringRiffle[{a}] // StringJoin[Riffle[#, "\n + "]]&

ToFile[filename_String, exp_String] := Module[{filehandle, path},
  filehandle = OpenWrite[];
  WriteString[filehandle, exp];
  path = Close[filehandle];
  Print[path];
  Run["! cat " <> path <> " | ./convert_to_tex.pl | tee " <> filename];
  filehandle = OpenRead[filename];
  ReadString[filehandle]
]
StringRiffle[{
  ToTeXString[Lvector],
  "\\\\&=",
  ToTeXString[LvectorSU2expanded]
}, "\n"];
ToFile["lag_vector.raw", %]


Lwino = TDot[I Conjugate[Wi[a]], NT[P["\[Sigma]bmu"]], NT[P["g2"]], NT["\[Epsilon]", NI[a,"SU2F"], NI[b,"SU2F"], NI[c,"SU2F"]],WW[,"\[Mu]",b],Wi[c]]
FillIndices[Lwino, "SU2F"] // SU2Replace // Expand // SortTDot
ToTeXString[%]
ToFile["lag_wino.raw", %]


Lfermionkinetic = Total[TDot[I, Conjugate[#], NT[P["\[Sigma]bmu"]], DDx[,"\[Mu]",#]] &/@ {
  QQ[i,a,x], bU[i,x], bD[i,x], LL[i,a], bE[i], tHu[a], tHd[a]
}] // ExpandAll // RewriteIndices
% // FillIndices[#, {"SU2F", "SU2I"}]&;
% // SU2Replace//ExpandAll//SortTDot // RewriteIndices
ToTeXString[%]
ToFile["lag_fermion_kinetic.raw", %]


LfermionSuper = SortTDot[SuperPotential]//. {
  TDot[any__, a:NT[SF[_], __], b:NT[SF[_], __], c:NT[SF[_], __]] /;FreeQ[{any}, SF]:> (-1)(TDot[any, a/.SF->S, b/.SF->F, c/.SF->F] + TDot[any, a/.SF->F, b/.SF->S, c/.SF->F] + TDot[any, a/.SF->F, b/.SF->F, c/.SF->S]),
  TDot[any__, a:NT[SF[_], __], b:NT[SF[_], __]] /;FreeQ[{any}, SF]:> (-1)(TDot[any, a/.SF->F, b/.SF->F])
} // ExpandAll // FillIndices[#, "SU2I"]& // SU2Replace // Expand // SortTDot // RewriteIndices
ToFile["lag_fermion_super.raw", ToTeXString[%]]


SFG[obj:NT[S[scalar_],any___]] := Module[{u1 = U1Charges[scalar], su2 = SU2Charges[scalar], su3 = SU3Charges[scalar], tmp},
  tmp = Total[{
    -Sqrt[2] u1 NT[P["gY"]] Bi[] Conjugate[obj](obj/.S->F),
    If[su2===T,  Module[{A=Unique["A"]}, -Sqrt[2]NT[P["g2"]]Conjugate[obj] Wi[A]ProdT[obj/.S->F, A]], 0],
    If[su3===\[Tau],  Module[{X=Unique["X"]}, -Sqrt[2]NT[P["g3"]]Conjugate[obj] Gi[X]Prod\[Tau][obj/.S->F, X]], 0],
    If[su3===\[Tau]C, Module[{X=Unique["X"]}, -Sqrt[2]NT[P["g3"]]Conjugate[obj] Gi[X]Prod\[Tau]C[obj/.S->F, X]], 0]
  }];
  tmp + Conjugate[tmp]]
LSFG = SFG /@ {tQQ[i,a,x], tbU[i,x], tbD[i,x], tLL[i,a], tbE[i], Hu[a], Hd[a]} // Total // SortTDot // RewriteIndices


LSFG // FillIndices[#, {"SU2I", "SU2F"}]& // Expand // SU2Replace // ExpandAll
ToFile["lag_sfg.raw", ToTeXString[%]]


Lscalarkin = Total[DDx[\[Mu], #]*Conjugate[DDx[,\[Mu],#]] &/@ {
  tQQ[i,a,x], tbU[i,x], tbD[i,x], tLL[i,a], tbE[i], Hu[a], Hd[a]
}] // ExpandAll // FillIndices[#, {"SU2F", "SU2I"}]& // ExpandAll // SU2Replace // ExpandAll // SortTDot // LorentzSort // RewriteIndices;


Lscalarkin //. {
  TDot[a1___, NT[P[t:"gY"|"g2"|"sw"|"cw"]], a2___] :> t TDot[a1, a2],
  TDot[a1___, NT[P2[t:"gY"|"g2"|"sw"|"cw"]], a2___] :> t^2 TDot[a1, a2],
  "g2"->"cw" "gZ",
  "gY"->"sw" "gZ"
} // Collect[#, TDot[__], (Simplify[#]//."cw"^2->1-"sw"^2 // Simplify)&]&;
%//. {
  -1+"sw"^2->-"cw"^2,
  "gZ" -> "ee" / "cw" / "sw",
  Power["sw",n_]/;n<0 :> ("ee"/"g2")^n,
  Power["cw",n_]/;n<0 :> ("ee"/"gY")^n
} //. {
  Power["ee",n_]/;n<0 :> ("g2" "sw")^n,
  Power["sw",n_]/;n<0 :> ("gY"/"gZ")^n,
    "gY" "cw" -> "ee"
} // SortTDot // LorentzSort// Collect[#, TDot[__], (Simplify[#] /.{ "gY" "cw"->"ee", "gY"^2 "cw"^2->"ee"^2})&]&
(List@@%) /. Plus[a_,b__]:>"("<>ToString[TeXForm[Plus[a,b]]]<>")" /.{
 (t:"g2"|"gY"|"gZ"|"ee"|"sw"|"cw")^2:>NT[P2[t]],
 t:"g2"|"gY"|"gZ"|"ee"|"sw"|"cw":>NT[P[t]]} // SortTDot // LorentzSort // RewriteIndices;
ToFile["lag_scalar_kin.raw", ToTeXString[Plus@@%]]


(* ::Input:: *)
(*%111 //. {*)
(*  TDot[x:OrderlessPatternSequence[any___,*)
(*       NT[y:(P|PC)["yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]],*)
(*       NT[f:_S|_F, f1___, NI[b_,"Gen"], f2___]*)
(*  ]] /; FreeQ[{f1, f2}, "Gen"] :> TDot[any, NT[FieldProduct[{y, {f, f1, f2}}], a]],*)
(*  TDot[x:OrderlessPatternSequence[any___,*)
(*       NT[y:(P|PC)["yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]],*)
(*       NT[f:_S|_F, f1___, NI[a_,"Gen"], f2___]*)
(*  ]] /; FreeQ[{f1, f2}, "Gen"] :> TDot[any, NT[FieldProduct[{Trans[y], {f, f1, f2}}], b]],*)
(*  TDot[x:OrderlessPatternSequence[any___,*)
(*       NT[y:(P|PC)["yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]],*)
(*       NT[f:_S|_F, f1___, NI[a_,"Gen"], f2___]*)
(*  ]] /; FreeQ[{f1, f2}, "Gen"] :> TDot[any, NT[FieldProduct[{Trans[y], {f, f1, f2}}], b]]*)
(*}*)


(* ::Input:: *)
(*(* %//. {*)
(*  TDot[x:OrderlessPatternSequence[\[Epsilon][a_,b_], \[Epsilon][c_,d_]], any___] \[RuleDelayed] TDot[\[Delta][a,c,"SU2I"]\[Delta][b,d,"SU2I"]-\[Delta][a,d,"SU2I"]\[Delta][b,c,"SU2I"], any],*)
(*  TDot[x:OrderlessPatternSequence[NT[P[f1:"yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]], NT[PC[f2:"yu"|"yd"|"ye"], c:NI[_,"Gen"], NI[b_,"Gen"]], any___]] \[RuleDelayed] TDot[NT[P[f1<>f2<>"D"], a, c], any],*)
(*  TDot[x:OrderlessPatternSequence[NT[P[f1:"yu"|"yd"|"ye"], NI[b_,"Gen"], a:NI[_,"Gen"]], NT[PC[f2:"yu"|"yd"|"ye"], NI[b_,"Gen"], c:NI[_,"Gen"]], any___]] \[RuleDelayed] TDot[NT[P[f2<>"D"<>f1], a, c], any],*)
(*  TDot[x:OrderlessPatternSequence[NT[P[f1:"yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]], NT[PC[f2:"yu"|"yd"|"ye"], c:NI[_,"Gen"], NI[b_,"Gen"]], any___]] \[RuleDelayed] TDot[NT[P[f1<>f2<>"D"], a, c], any],*)
(*  TDot[x:OrderlessPatternSequence[NT[P[f1:"yu"|"yd"|"ye"], a:NI[_,"Gen"], NI[b_,"Gen"]], NT[PC[f2:"yu"|"yd"|"ye"], c:NI[_,"Gen"], NI[b_,"Gen"]], any___]] \[RuleDelayed] TDot[NT[P[f1<>f2<>"D"], a, c], any]*)
(*} *)*)


VSUSYF = Total[(DWD\[CapitalPhi][#]RenewIndices[Conjugate[DWD\[CapitalPhi][#]]] // RewriteIndices)& /@ {
  "Q", "bU", "bD", "L", "bE", "Hu", "Hd"
}];

D3\[Alpha] = -NT[P["g3"]]*Total[
  (SU3Charges[#[[1,1]]][A,x,y] (#/.x->y) Conjugate[#]) &/@{tQQ[i,a,x], tbU[i,x], tbD[i,x], tLL[i,a], tbE[i], Hu[a], Hd[a]} /. {0[__]:>0, \[Tau]C[a_,x_,y_]:>-\[Tau][a,y,x]}
];
D2\[Alpha] = -NT[P["g2"]]*Total[
(If[SU2Charges[#[[1,1]]]===T, T[A,a,b], 0] (#/.a->b) Conjugate[#]) &/@{tQQ[i,a,x], tbU[i,x], tbD[i,x], tLL[i,a], tbE[i], Hu[a], Hd[a]}
];
D1\[Alpha] = -NT[P["gY"]] * Total[
  (U1Charges[#[[1,1]]] # Conjugate[#]) &/@{tQQ[i,a,x], tbU[i,x], tbD[i,x], tLL[i,a], tbE[i], Hu[a], Hd[a]}
];
VSUSYD = (1/2)D3\[Alpha] RenewIndices[D3\[Alpha]] + (1/2)D2\[Alpha] RenewIndices[D2\[Alpha]] + (1/2)D1\[Alpha] RenewIndices[D1\[Alpha]];


SU2ExpandedSUSYPotential = VSUSYF + VSUSYD // ExpandAll // FillIndices[#, {"SU2I", "SU2F"}]& // SU2Replace // ExpandAll // SortTDot // LorentzSort // RewriteIndices;


CountScalar[exp_] := Module[{p1, p2},
  p1 = Length[Cases[exp,(S|SC|F|FC|V)[_],All]];
  p2 = Length[Cases[exp,S2[_],All]];
  p1+2p2]  
CountNonVEVScalar[exp_] := CountScalar[exp/.{(S|SC|S2)["HdZ"|"HuZ"]:>Null}]


Lgaugino =  Total[{
  TDot[I, Conjugate[Gi[x]], NT[P["\[Sigma]bmu"]], Dx[,"\[Mu]",Gi[x]]],
  TDot[I Conjugate[Gi[x]], NT[P["\[Sigma]bmu"]], NT[P["g3"]], NT["f", NI[x,"SU3F"], NI[y,"SU3F"], NI[z,"SU3F"]],GG[,"\[Mu]",y],Gi[z]],
  TDot[I, Conjugate[Wi[a]], NT[P["\[Sigma]bmu"]], Dx[,"\[Mu]",Wi[a]]],
  TDot[I Conjugate[Wi[a]], NT[P["\[Sigma]bmu"]], NT[P["g2"]], NT["\[Epsilon]", NI[a,"SU2F"], NI[b,"SU2F"], NI[c,"SU2F"]],WW[,"\[Mu]",b],Wi[c]],
  TDot[I, Conjugate[Bi[]], NT[P["\[Sigma]bmu"]], Dx[,"\[Mu]",Bi[]]],
  TDot[(-1/2)NT[P["M1"]], Bi[], Bi[]] // (#+Conjugate[#])&,
  TDot[(-1/2)NT[P["M2"]], Wi[a], Wi[a]] // (#+Conjugate[#])&,
  TDot[(-1/2)NT[P["M3"]], Gi[x], Gi[x]] // (#+Conjugate[#])&
}];


VscalarNonSUSYRPC = Total[{
  Conjugate[tQQ[i,a,x]] NT[P["mQ2"], NI[i,"Gen"], NI[j,"Gen"]] tQQ[j,a,x],
  Conjugate[tLL[i,a]]   NT[P["mL2"], NI[i,"Gen"], NI[j,"Gen"]] tLL[j,a],
  tbU[i,x] NT[P["mUc2"], NI[i,"Gen"], NI[j,"Gen"]] Conjugate[tbU[j,x]],
  tbD[i,x] NT[P["mDc2"], NI[i,"Gen"], NI[j,"Gen"]] Conjugate[tbD[j,x]],
  tbE[i] NT[P["mEc2"], NI[i,"Gen"], NI[j,"Gen"]] Conjugate[tbE[j]],
  NT[P["mHu2"]] Hu[a]Conjugate[Hu[a]],
  NT[P["mHd2"]] Hd[a]Conjugate[Hd[a]]
}] + Total[{
  -tbU[i,x]Hu[a]NT[P["au"], NI[i,"Gen"], NI[j,"Gen"]] tQQ[b,j,x] \[Epsilon][a,b],
  +tbD[i,x]Hd[a]NT[P["ad"], NI[i,"Gen"], NI[j,"Gen"]] tQQ[b,j,x] \[Epsilon][a,b],
  +tbE[i]Hd[a]NT[P["ae"], NI[i,"Gen"], NI[j,"Gen"]] tLL[b,j] \[Epsilon][a,b],
  NT[P["b"]] \[Epsilon][a,b]Hu[a]Hd[b],
  +tbU[i,x]Conjugate[Hd[a]]NT[P["cu"], NI[i,"Gen"], NI[j,"Gen"]] tQQ[b,j,x],
  +tbD[i,x]Conjugate[Hu[a]]NT[P["cd"], NI[i,"Gen"], NI[j,"Gen"]] tQQ[b,j,x],
  +tbE[i]Conjugate[Hu[a]]NT[P["ce"], NI[i,"Gen"], NI[j,"Gen"]] tLL[b,j]
}//(#+Conjugate[#])&]


LALL = Total[{
  LvectorSU2expanded,
  LfermionSuper + Conjugate[LfermionSuper],
  Lfermionkinetic,
  Lgaugino,
  LSFG,
  Lscalarkin - VSUSYF - VSUSYD - VscalarNonSUSYRPC}] //ExpandAll// FillIndices[#, {"SU2F", "SU2I"}]& // SU2Replace//ExpandAll//SortTDot // RewriteIndices


MassTerms = Select[List@@(LALL//ExpandAll),CountNonVEVScalar[#]<=2&] /. {
  NT[(P|PC|P2)["\[Lambda]"|"\[Kappa]"],___]:>0,
  NT[_[dx[_]],___]:>0,
  NT[(S|SC)["HdZ"]]:>NT[P["vd"]],
  NT[(S|SC)["HuZ"]]:>NT[P["vu"]]
} // SortTDot // Total


Select[MassTerms, Not[FreeQ[#,(S|SC)["HuP"|"HdM"]]]&]//.{
  TDot[x1___,NT[P[t_]],x2___]:>t TDot[x1,x2],
  TDot[x1___,NT[PC[t_]],x2___]:>Conjugate[t] TDot[x1,x2],
  TDot[x1___,NT[P2[t_]],x2___]:>t^2 TDot[x1,x2]
}//.{
  "vu"->v Sin[\[Beta]],
  "vd"->v Cos[\[Beta]],
  "g2"->gZ cw,
  "gY"->gZ sw
}//RewriteIndices//Collect[#, TDot[__], FullSimplify]&
