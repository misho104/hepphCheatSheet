#!/usr/bin/perl

use strict;
use warnings;

my $scalar = {
  "Hu" => "\\hu_{SUB}^{SUP}",
  "Hd" => "\\hd_{SUB}^{SUP}",
  "Q"  => "\\tqL[SUB]^{SUP}",
  "bU" => "\\tuR[SUB]^{SUP*}",
  "bD" => "\\tdR[SUB]^{SUP*}",
  "L"  => "\\tlL[SUB]^{SUP}",
  "bE" => "\\teR[SUB]^{SUP*}",
  "HuP" => "\\hup_{SUB}^{SUP}",
  "HuZ" => "\\huz_{SUB}^{SUP}",
  "HdZ" => "\\hdz_{SUB}^{SUP}",
  "HdM" => "\\hdm_{SUB}^{SUP}",
  "UL"  => "\\tuL[SUB]^{SUP}",
  "DL"  => "\\tdL[SUB]^{SUP}",
  "NUL" => "\\tnuL[SUB]^{SUP}",
  "EL"  => "\\teL[SUB]^{SUP}",
  "HuZR" => "\\hu_{SUB}^{0RSUP}",
  "HdZR" => "\\hd_{SUB}^{0RSUP}",
  "HP" => "H_{SUB}^{+SUP}",
  "G0" => "G_{SUB}^{0SUP}",
  "GP" => "G_{SUB}^{+SUP}",
  "A0" => "A_{SUB}^{0SUP}",
};

my $param = {
  "yu" => "\\yu[SUB]^{SUP}",
  "yd" => "\\yd[SUB]^{SUP}",
  "ye" => "\\ye[SUB]^{SUP}",
  "\\[Mu]" => "\\mu^{SUP}_{SUB}",
  "\\[Kappa]" => "\\kappa^{SUP}_{SUB}",
  "\\[Lambda]" => "\\lambda^{SUP}_{SUB}",
  "\\[Lambda]p" => "\\lambda'^{SUP}_{SUB}",
  "\\[Lambda]pp" => "\\lambda''^{SUP}_{SUB}",
  "yudagyu" => "(\\yu^\\dagger\\yu)^{SUP}_{SUB}",
  "yddagyd" => "(\\yd^\\dagger\\yd)^{SUP}_{SUB}",
  "yedagye" => "(\\ye^\\dagger\\ye)^{SUP}_{SUB}",
  "yuyudag" => "(\\yu\\yu^\\dagger)^{SUP}_{SUB}",
  "ydyddag" => "(\\yd\\yd^\\dagger)^{SUP}_{SUB}",
  "yeyedag" => "(\\ye\\ye^\\dagger)^{SUP}_{SUB}",
  "gY" => "g_Y^{SUP}_{SUB}",
  "g2" => "g_2^{SUP}_{SUB}",
  "g3" => "g_3^{SUP}_{SUB}",
  "ee" => "|e|^{SUP}_{SUB}",
  "gZ" => "g_Z^{SUP}_{SUB}",
  "partial" => "\\partial^{SUP}_{SUB}",
  "\\[Sigma]bmu" => "\\bsigma^{\\mu SUP}_{SUB}",
  "sw" => "\\si{\\mathrm w}^{SUP}_{SUB}",
  "cw" => "\\co{\\mathrm w}^{SUP}_{SUB}",
  "\\tau" => "\\tau^{SUP}_{SUB}",
  "\\[CapitalTheta]G" => "\\Theta_G{}^{SUP}_{SUB}",
  "M1" => "M_1^{SUP}_{SUB}",
  "M2" => "M_2^{SUP}_{SUB}",
  "M3" => "M_3^{SUP}_{SUB}",
  "c\\[Beta]" => "\\co{\\beta}^{SUP}_{SUB}",
  "s\\[Beta]" => "\\si{\\beta}^{SUP}_{SUB}",
  "c2\\[Beta]" => "\\co{2\\beta}^{SUP}_{SUB}",
  "s2\\[Beta]" => "\\si{2\\beta}^{SUP}_{SUB}",
  "mZ" => "m_Z^{SUP}_{SUB}",
  "b" => "b^{SUP}_{SUB}",
  "au" => "a^{SUP}_{{\\mathrm u} SUB}",
  "ad" => "a^{SUP}_{{\\mathrm d} SUB}",
  "ae" => "a^{SUP}_{{\\mathrm e} SUB}",
  "mHd2" => "m_{\\Hd}^2^{SUP}_{SUB}",
  "mHu2" => "m_{\\Hu}^2^{SUP}_{SUB}",
  "mUc2" => "[m_{U^\\cc}^2]^{SUP}_{SUB}",
  "mDc2" => "[m_{D^\\cc}^2]^{SUP}_{SUB}",
  "mEc2" => "[m_{E^\\cc}^2]^{SUP}_{SUB}",
  "mQ2" => "[m_{Q}^2]^{SUP}_{SUB}",
  "mL2" => "[m_{L}^2]^{SUP}_{SUB}",
  "vu" => "\\vu",
  "vd" => "\\vd",
};

my $scalar_conj = {
  "Hu" => "\\hu_{SUB}^{SUP*}",
  "Hd" => "\\hd_{SUB}^{SUP*}",
  "Q"  => "\\tqL[SUB]^{SUP*}",
  "bU" => "\\tuR[SUB]^{SUP}",
  "bD" => "\\tdR[SUB]^{SUP}",
  "L"  => "\\tlL[SUB]^{SUP*}",
  "bE" => "\\teR[SUB]^{SUP}",
  "HuP" => "\\hu_{SUB}^{+SUP*}",
  "HuZ" => "\\hu_{SUB}^{0SUP*}",
  "HdZ" => "\\hd_{SUB}^{0SUP*}",
  "HdM" => "\\hd_{SUB}^{-SUP*}",
  "UL"  => "\\tuL[SUB]^{SUP*}",
  "DL"  => "\\tdL[SUB]^{SUP*}",
  "NUL" => "\\tnuL[SUB]^{SUP*}",
  "EL"  => "\\teL[SUB]^{SUP*}",
  "HP" => "H_{SUB}^{-SUP}",
  "GP" => "G_{SUB}^{-SUP}",
};

my $param_conj = {
  "yu" => "\\yu[SUB]^{SUP*}",
  "yd" => "\\yd[SUB]^{SUP*}",
  "ye" => "\\ye[SUB]^{SUP*}",
  "\\[Mu]" => "\\mu^{SUP*}_{SUB}",
  "\\[Kappa]" => "\\Kappa^{SUP*}_{SUB}",
  "\\[Lambda]" => "\\lambda^{SUP*}_{SUB}",
  "\\[Lambda]p" => "\\lambda'^{SUP*}_{SUB}",
  "\\[Lambda]pp" => "\\lambda''^{SUP*}_{SUB}",
  "M1" => "M_1^{*SUP}_{SUB}",
  "M2" => "M_2^{*SUP}_{SUB}",
  "M3" => "M_3^{*SUP}_{SUB}",
  "b" => "b^{*SUP}_{SUB}",
  "au" => "a^{*SUP}_{{\\mathrm u} SUB}",
  "ad" => "a^{*SUP}_{{\\mathrm d} SUB}",
  "ae" => "a^{*SUP}_{{\\mathrm e} SUB}",
};

my $scalar_sq = {
  "Hu" => "|\\hu_{SUB}^{SUP}|^2",
  "Hd" => "|\\hd_{SUB}^{SUP}|^2",
  "Q"  => "|\\tqL[SUB]^{SUP}|^2",
  "bU" => "|\\tuR[SUB]^{SUP}|^2",
  "bD" => "|\\tdR[SUB]^{SUP}|^2",
  "L"  => "|\\tlL[SUB]^{SUP}|^2",
  "bE" => "|\\teR[SUB]^{SUP}|^2",
};

my $scalar_4 = {
  "Hu" => "|\\hu_{SUB}^{SUP}|^4",
  "Hd" => "|\\hd_{SUB}^{SUP}|^4",
  "Q"  => "|\\tqL[SUB]^{SUP}|^4",
  "bU" => "|\\tuR[SUB]^{SUP}|^4",
  "bD" => "|\\tdR[SUB]^{SUP}|^4",
  "L"  => "|\\tlL[SUB]^{SUP}|^4",
  "bE" => "|\\teR[SUB]^{SUP}|^4",
};

my $param_sq = {
  "yu" => "|\\yu[SUB]^{SUP}|^2",
  "yd" => "|\\yd[SUB]^{SUP}|^2",
  "ye" => "|\\ye[SUB]^{SUP}|^2",
  "\\[Mu]" => "|\\mu^{SUP}_{SUB}|^2",
  "\\[Kappa]" => "|\\kappa^{SUP}_{SUB}|^2",
  "\\[Lambda]" => "|\\lambda^{SUP}_{SUB}|^2",
  "\\[Lambda]p" => "|\\lambda'^{SUP}_{SUB}|^2",
  "\\[Lambda]pp" => "|\\lambda''^{SUP}_{SUB}|^2",
  "gY" => "g_Y^{2SUP}_{SUB}",
  "gZ" => "g_Z^{2SUP}_{SUB}",
  "g2" => "g_2^{2SUP}_{SUB}",
  "g3" => "g_3^{2SUP}_{SUB}",
  "sw" => "\\sisi{\\mathrm w}^{SUP}_{SUB}",
  "cw" => "\\coco{\\mathrm w}^{SUP}_{SUB}",
  "ee" => "e^{2SUP}_{SUB}",
};

my $fermion = {
  "Hu" => "\\thu_{SUB}^{SUP}",
  "Hd" => "\\thd_{SUB}^{SUP}",
  "Q"  => "\\qL[SUB]^{SUP}",
  "bU" => "\\uR[SUB]^{\\cc SUP}",
  "bD" => "\\dR[SUB]^{\\cc SUP}",
  "L"  => "\\lL[SUB]^{SUP}",
  "bE" => "\\eR[SUB]^{\\cc SUP}",
  "Gi" => "\\tig_{SUB}^{SUP}",
  "Wi" => "\\tiw_{SUB}^{SUP}",
  "Bi" => "\\tib_{SUB}^{SUP}",
  "Wi3" => "\\tiw_{SUB}^{3SUP}",
  "WiP" => "\\tiw_{SUB}^{+SUP}",
  "WiM" => "\\tiw_{SUB}^{-SUP}",
  "HuP" => "\\thup_{SUB}^{SUP}",
  "HuZ" => "\\thuz_{SUB}^{SUP}",
  "HdZ" => "\\thdz_{SUB}^{SUP}",
  "HdM" => "\\thdm_{SUB}^{SUP}",
  "UL"  => "\\uL[SUB]^{SUP}",
  "DL"  => "\\dL[SUB]^{SUP}",
  "NUL" => "\\nuL[SUB]^{SUP}",
  "EL"  => "\\eL[SUB]^{SUP}",
  "Neut"  => "\\neut[SUB]^{SUP}",
  "CharP"  => "\\charP[SUB]^{SUP}",
  "CharM"  => "\\charM[SUB]^{SUP}",
};

my $vector = {
  "B" => "B_{SUB}^{SUP}",
  "W" => "W_{SUB}^{SUP}",
  "WP" => "W_{SUB}^{+SUP}",
  "WM" => "W_{SUB}^{-SUP}",
  "W3" => "W_{SUB}^{3SUP}",
  "g" => "g_{SUB}^{SUP}",
  "A" => "A_{SUB}^{SUP}",
  "Z" => "Z_{SUB}^{SUP}",
};

my $fermion_conj = {
  "Hu" => "\\bthu_{SUB}^{SUP}",
  "Hd" => "\\bthd_{SUB}^{SUP}",
  "Q"  => "\\bqL[SUB]^{SUP}",
  "bU" => "\\buR[SUB]^{\\cc SUP}",
  "bD" => "\\bdR[SUB]^{\\cc SUP}",
  "L"  => "\\blL[SUB]^{SUP}",
  "bE" => "\\beR[SUB]^{\\cc SUP}",
  "Gi" => "\\bar{\\tig}_{SUB}^{SUP}",
  "Wi" => "\\bar{\\tiw}_{SUB}^{SUP}",
  "Bi" => "\\bar{\\tib}_{SUB}^{SUP}",
  "Wi3" => "\\bar{\\tiw}_{SUB}^{3SUP}",
  "WiP" => "\\bar{\\tiw}_{SUB}^{+SUP}",
  "WiM" => "\\bar{\\tiw}_{SUB}^{-SUP}",
  "HuP" => "\\bthup_{SUB}^{SUP}",
  "HuZ" => "\\bthuz_{SUB}^{SUP}",
  "HdZ" => "\\bthdz_{SUB}^{SUP}",
  "HdM" => "\\bthdm_{SUB}^{SUP}",
  "UL"  => "\\buL[SUB]^{SUP}",
  "DL"  => "\\bdL[SUB]^{SUP}",
  "NUL" => "\\bnuL[SUB]^{SUP}",
  "EL"  => "\\beL[SUB]^{SUP}",
  "Neut"  => "\\bar\\neut[SUB]^{SUP}",
  "CharP"  => "\\bar\\charP[SUB]^{SUP}",
  "CharM"  => "\\bar\\charM[SUB]^{SUP}",
};




sub fieldname_to_tex{
  my ($type, $name, $subscript, $superscript) = @_;
  my $tex = "";
  if($type eq "S"){
    $tex = $scalar->{$name} or die "undefined scalar $name";
  }elsif($type eq "P"){
    $tex = $param->{$name} or die "undefined param $name";
  }elsif($type eq "SC"){
    $tex = $scalar_conj->{$name} or die "undefined scalar $name";
  }elsif($type eq "PC"){
    $tex = $param_conj->{$name} or die "undefined param $name";
  }elsif($type eq "S2"){
    $tex = $scalar_sq->{$name} or die "undefined scalar $name";
  }elsif($type eq "S4"){
    $tex = $scalar_4->{$name} or die "undefined scalar $name";
  }elsif($type eq "P2"){
    $tex = $param_sq->{$name} or die "undefined param $name";
  }elsif($type eq "F"){
    $tex = $fermion->{$name} or die "undefined F $name";
  }elsif($type eq "FC"){
    $tex = $fermion_conj->{$name} or die "undefined FC $name";
  }elsif($type eq "V"){
    $tex = $vector->{$name} or die "undefined vector $name";
  }
  $tex =~ s/SUB/$subscript/;
  $tex =~ s/SUP/$superscript/;
  return $tex;
}

foreach my $line(<>){
  $line =~ s/\$\\lambda\s*\$/\\[Lambda]/g;
  $line =~ s/\$\\sigma\s*\$/\\[Sigma]/g;
  $line =~ s/\$\\backslash\s*\\backslash\s*\$/\\/g;
  $line =~ s/_\{\}//g;
  $line =~ s/\@(P|S|F|V|SF|PC|SC|FC|S2|S4|P2):(.+?):(.*?):(.*?)\@/fieldname_to_tex($1, $2, $3, $4)/ge;
  $line =~ s/@(\\epsilon|f):(.*?):(.*?)@/$1_{$2}^{$3}/g;
  $line =~ s/_\{\}//g;
  $line =~ s/\[\]//g;
  $line =~ s/\^\{\}//g;
  $line =~ s/'\^\{/^\{\\prime /g;
  $line =~ s/'\^\{/^\{\\prime /g;
  $line =~ s/\$/\@/g;
  $line =~ s/\\left\(\s*\(-1\)/\\left\( - /g;
  $line =~ s/\+\s*\(-1\)\s*/- /g;
  $line =~ s/\^\{2\}/^2/g;
  $line =~ s/\\frac\{(1)\}\{(\d+)\}\s*(g_Y\^2|g_2\^2|g_3\^2)/\\frac{$3}{$2}/g;
  $line =~ s/\\frac\{(\d+)\}\{(\d+)\}\s*(g_Y\^2|g_2\^2|g_3\^2)/\\frac{$1$3}{$2}/g;
  #
  $line =~ s/\\\[Mu\]/\\mu/g;
  $line =~ s/\\\[Nu\]/\\nu/g;
  $line =~ s/\\text\{ii\}/{\\ii}/g;
  #
  $line =~ s/\s*\+\s*-\s*/ - /g;
  $line =~ s/\s*\+\s*-\s*\(-1\)\s*/ - /g;
  print($line);
}
