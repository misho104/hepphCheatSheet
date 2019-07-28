(* ::Package:: *)

(* ::Code:: *)
(*(* for debug *)*)
(*SetDirectory[NotebookDirectory[]];*)
(*<<WeylAlgebra`*)


BeginPackage["WeylAlgebra`"];


Begin["`Private`"];


(* ::Text:: *)
(*Supplemental rules for Conjugate.*)


(* Conjugate Operation is "defined" For (single) Grassmann-type tensor. *)
NT /: Conjugate[a:NT["\[Eta]", Repeated[IndexType]]] := a
NT /: Conjugate[a:NT["\[Delta]", Repeated[IndexType]]] := SwitchOverDot[a]
NT /: Conjugate[a:NT["\[Epsilon]", Repeated[IndexType]]] := SwitchOverDot[a]
NT /: Conjugate[a:NT["\[Sigma]", b:Repeated[IndexType]]] := SwitchOverDot[NT[OverBar[HoldForm["\[Sigma]"]], b]]//ReleaseHoldAll
NT /: Conjugate[a:NT[OverBar["\[Sigma]"], b:Repeated[IndexType]]] := SwitchOverDot[NT[HoldForm["\[Sigma]"], b]]//ReleaseHoldAll


(* ::Text:: *)
(*Derived rules.*)


TDot[OrderlessPatternSequence[GT[n_, (UI|LI)[_, "spinor"]], GT[n_, (UI|LI)[SpinorLabelType, "spinor"]], GT[n_, (UI|LI)[SpinorLabelType, "spinor"]], ___]]:=0


Gen\[Theta]\[Theta][\[Theta]_] := Module[{k=Unique[]}, TDot[GT[\[Theta], UI[k, "spinor"]], GT[\[Theta], LI[k, "spinor"]]]]
Gen\[Theta]\[Theta]b[\[Theta]_] := Module[{k=OverDot[Unique[]]}, TDot[GT[\[Theta], LI[k, "spinor"]], GT[\[Theta], UI[k, "spinor"]]]]

TDot[x1___, a:GT[n_, UI[i:LabelType, "spinor"]], x2___, GT[n_, UI[j:LabelType, "spinor"]], x3___] /; i=!=j := (-\[Epsilon]U[i,j]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta][n], x3]
TDot[x1___, a:GT[n_, LI[i:LabelType, "spinor"]], x2___, GT[n_, LI[j:LabelType, "spinor"]], x3___] /; i=!=j := (+\[Epsilon]L[i,j]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta][n], x3]
TDot[x1___, a:GT[n_, UI[i:LabelType, "spinor"]], x2___, GT[n_, LI[j:LabelType, "spinor"]], x3___] /; i=!=j := (+\[Delta][i,j,"spinor"]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta][n], x3]
TDot[x1___, a:GT[n_, LI[i:LabelType, "spinor"]], x2___, GT[n_, UI[j:LabelType, "spinor"]], x3___] /; i=!=j := (-\[Delta][j,i,"spinor"]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta][n], x3]

TDot[x1___, a:GT[n_, UI[i:OverDot[LabelType], "spinor"]], x2___, GT[n_, UI[j:OverDot[LabelType], "spinor"]], x3___] /; i=!=j := (+\[Epsilon]Ud[i,j]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta]b[n], x3]
TDot[x1___, a:GT[n_, LI[i:OverDot[LabelType], "spinor"]], x2___, GT[n_, LI[j:OverDot[LabelType], "spinor"]], x3___] /; i=!=j := (-\[Epsilon]Ld[i,j]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta]b[n], x3]
TDot[x1___, a:GT[n_, UI[i:OverDot[LabelType], "spinor"]], x2___, GT[n_, LI[j:OverDot[LabelType], "spinor"]], x3___] /; i=!=j := (-\[Delta]d[i,j]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta]b[n], x3]
TDot[x1___, a:GT[n_, LI[i:OverDot[LabelType], "spinor"]], x2___, GT[n_, UI[j:OverDot[LabelType], "spinor"]], x3___] /; i=!=j := (+\[Delta]d[j,i]/2)FlipSign[a,x2]*TDot[x1, x2, Gen\[Theta]\[Theta]b[n], x3]


(* "whole" tag is necessary to keep the order of sequence x1. *)
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_, "spinor"], UI[b_, "spinor"]], NT["\[Epsilon]", LI[b_, "spinor"], LI[c_, "spinor"]]]] := +\[Delta][a,c,"spinor"]TDot[x1]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_, "spinor"], UI[b_, "spinor"]], NT["\[Epsilon]", LI[c_, "spinor"], LI[b_, "spinor"]]]] := -\[Delta][a,c,"spinor"]TDot[x1]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[b_, "spinor"], UI[a_, "spinor"]], NT["\[Epsilon]", LI[b_, "spinor"], LI[c_, "spinor"]]]] := -\[Delta][a,c,"spinor"]TDot[x1]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[b_, "spinor"], UI[a_, "spinor"]], NT["\[Epsilon]", LI[c_, "spinor"], LI[b_, "spinor"]]]] := +\[Delta][a,c,"spinor"]TDot[x1]

TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_, "spinor"], UI[b_, "spinor"]], NT["\[Epsilon]", LI[b_, "spinor"], LI[a_, "spinor"]]]] := +\[Delta][a, a, "spinor"]TDot[x1]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_, "spinor"], UI[b_, "spinor"]], NT["\[Epsilon]", LI[a_, "spinor"], LI[b_, "spinor"]]]] := -\[Delta][a, a, "spinor"]TDot[x1]

TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", LI[a:LabelType, "spinor"], LI[d:LabelType, "spinor"]], NT["\[Epsilon]", LI[b_OverDot, "spinor"], LI[c_OverDot, "spinor"]], NT[OverBar["\[Sigma]"], t:(UI|LI)[\[Mu]_, "lorentz"], UI[c_, "spinor"], UI[d_, "spinor"]]]] := +TDot[x1, NT["\[Sigma]", t, LI[a, "spinor"], LI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", LI[d:LabelType, "spinor"], LI[a:LabelType, "spinor"]], NT["\[Epsilon]", LI[b_OverDot, "spinor"], LI[c_OverDot, "spinor"]], NT[OverBar["\[Sigma]"], t:(UI|LI)[\[Mu]_, "lorentz"], UI[c_, "spinor"], UI[d_, "spinor"]]]] := -TDot[x1, NT["\[Sigma]", t, LI[a, "spinor"], LI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", LI[a:LabelType, "spinor"], LI[d:LabelType, "spinor"]], NT["\[Epsilon]", LI[c_OverDot, "spinor"], LI[b_OverDot, "spinor"]], NT[OverBar["\[Sigma]"], t:(UI|LI)[\[Mu]_, "lorentz"], UI[c_, "spinor"], UI[d_, "spinor"]]]] := -TDot[x1, NT["\[Sigma]", t, LI[a, "spinor"], LI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", LI[d:LabelType, "spinor"], LI[a:LabelType, "spinor"]], NT["\[Epsilon]", LI[c_OverDot, "spinor"], LI[b_OverDot, "spinor"]], NT[OverBar["\[Sigma]"], t:(UI|LI)[\[Mu]_, "lorentz"], UI[c_, "spinor"], UI[d_, "spinor"]]]] := +TDot[x1, NT["\[Sigma]", t, LI[a, "spinor"], LI[b, "spinor"]]]

TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_OverDot, "spinor"], UI[d_OverDot, "spinor"]], NT["\[Epsilon]", UI[b:LabelType, "spinor"], UI[c:LabelType, "spinor"]], NT["\[Sigma]", t:(UI|LI)[\[Mu]_, "lorentz"], LI[c_, "spinor"], LI[d_, "spinor"]]]] := +TDot[x1, NT[OverBar["\[Sigma]"], t, UI[a, "spinor"], UI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[d_OverDot, "spinor"], UI[a_OverDot, "spinor"]], NT["\[Epsilon]", UI[b:LabelType, "spinor"], UI[c:LabelType, "spinor"]], NT["\[Sigma]", t:(UI|LI)[\[Mu]_, "lorentz"], LI[c_, "spinor"], LI[d_, "spinor"]]]] := -TDot[x1, NT[OverBar["\[Sigma]"], t, UI[a, "spinor"], UI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[a_OverDot, "spinor"], UI[d_OverDot, "spinor"]], NT["\[Epsilon]", UI[c:LabelType, "spinor"], UI[b:LabelType, "spinor"]], NT["\[Sigma]", t:(UI|LI)[\[Mu]_, "lorentz"], LI[c_, "spinor"], LI[d_, "spinor"]]]] := -TDot[x1, NT[OverBar["\[Sigma]"], t, UI[a, "spinor"], UI[b, "spinor"]]]
TDot[whole:OrderlessPatternSequence[x1___, NT["\[Epsilon]", UI[d_OverDot, "spinor"], UI[a_OverDot, "spinor"]], NT["\[Epsilon]", UI[c:LabelType, "spinor"], UI[b:LabelType, "spinor"]], NT["\[Sigma]", t:(UI|LI)[\[Mu]_, "lorentz"], LI[c_, "spinor"], LI[d_, "spinor"]]]] := +TDot[x1, NT[OverBar["\[Sigma]"], t, UI[a, "spinor"], UI[b, "spinor"]]]


TDot[whole:OrderlessPatternSequence[x1___,
  NT["\[Sigma]",          t1:(UI|LI)[_, "lorentz"], LI[a:LabelType, "spinor"], LI[b_OverDot, "spinor"]],
  NT[OverBar["\[Sigma]"], t2:(UI|LI)[_, "lorentz"], UI[b_, "spinor"], UI[a_, "spinor"]]]] := 2*TDot[x1, NT["\[Eta]", t1, t2]]

TDot[whole:OrderlessPatternSequence[x1___,
  NT["\[Sigma]",          (t1:UI|LI)[\[Mu]_, "lorentz"], a:LI[LabelType, "spinor"], ad:LI[_OverDot, "spinor"]],
  NT[OverBar["\[Sigma]"], (t2:UI|LI)[\[Mu]_, "lorentz"], bd:UI[_OverDot, "spinor"], b:UI[LabelType, "spinor"]]]] := If[t1===t2, Message[TDot::InvalidIndices, whole]; Abort[], 2*TDot[x1, NT["\[Delta]", bd, ad], NT["\[Delta]", a, b]]]
TDot[whole:OrderlessPatternSequence[x1___,
  NT["\[Sigma]", LI[\[Mu]_, "lorentz"], a:LI[LabelType, "spinor"], ad:LI[_OverDot, "spinor"]],
  NT["\[Sigma]", UI[\[Mu]_, "lorentz"], b:LI[LabelType, "spinor"], bd:LI[_OverDot, "spinor"]]]] := 2*TDot[x1, NT["\[Epsilon]", a, b], NT["\[Epsilon]", ad, bd]]
TDot[whole:OrderlessPatternSequence[x1___,
  NT[OverBar["\[Sigma]"], LI[\[Mu]_, "lorentz"], ad:UI[_OverDot, "spinor"], a:UI[LabelType, "spinor"]],
  NT[OverBar["\[Sigma]"], UI[\[Mu]_, "lorentz"], bd:UI[_OverDot, "spinor"], b:UI[LabelType, "spinor"]]]] := 2*TDot[x1, NT["\[Epsilon]", a, b], NT["\[Epsilon]", ad, bd]]


Rewrite\[Sigma]\[Sigma][exp_] := exp /. {
  TDot[whole:OrderlessPatternSequence[x1___, NT["\[Sigma]", UI[\[Mu]_, "lorentz"], LI[a_, "spinor"], LI[da_OverDot, "spinor"]],  NT["\[Sigma]", UI[\[Nu]_, "lorentz"], LI[b_, "spinor"], LI[db_OverDot, "spinor"]]]] :> Module[
    {c=Unique[], dc=OverDot[Unique[]], \[Rho]=Unique[], \[CapitalSigma]=Unique[]}, (1/2)TDot[x1, Total[{
      -2I \[Epsilon]L[da, dc]\[Sigma]b[\[Mu],\[Nu],dc,db] \[Epsilon]L[a,b],
      -2I \[Sigma][\[Mu],\[Nu],a,c]\[Epsilon]L[c,b]\[Epsilon]L[da,db],
      4\[Sigma][\[Rho],\[Mu],a,c]\[Epsilon]L[c,b]\[Epsilon]L[da,dc]\[Sigma]b[\[CapitalSigma], \[Nu], dc, db]\[Eta]L[\[Rho],\[CapitalSigma]],
      \[Epsilon]L[a,b]\[Epsilon]L[da,db]\[Eta]U[\[Mu],\[Nu]]}]]],
  TDot[whole:OrderlessPatternSequence[x1___, NT[OverBar["\[Sigma]"], UI[\[Mu]_, "lorentz"], UI[da_OverDot, "spinor"], UI[a_, "spinor"]],  NT[OverBar["\[Sigma]"], UI[\[Nu]_, "lorentz"], UI[db_OverDot, "spinor"], UI[b_, "spinor"]]]] :> Module[
    {c=Unique[], dc=OverDot[Unique[]], \[Rho]=Unique[], \[CapitalSigma]=Unique[]}, (1/2)TDot[x1, Total[{
      -2I \[Sigma]b[\[Mu],\[Nu],da,dc] \[Epsilon]U[dc, db] \[Epsilon]U[a,b],
      -2I \[Epsilon]U[a,c]\[Sigma][\[Mu],\[Nu],c,b]\[Epsilon]L[da,db],
      4 \[Epsilon]U[a,c]\[Sigma][\[CapitalSigma],\[Nu],c,b]\[Sigma]b[\[Rho], \[Mu], da, dc]\[Epsilon]U[dc,db]\[Eta]L[\[Rho],\[CapitalSigma]],
      \[Epsilon]U[a,b]\[Epsilon]U[da,db]\[Eta]U[\[Mu],\[Nu]]}]]]
}; (* Not well tested *)


End[];
EndPackage[];
