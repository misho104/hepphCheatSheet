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
  "bE" => "\\teR[SUB]^{SUP*}"
};

my $param = {
  "yu" => "\\yu[SUB]^{SUP}",
  "yd" => "\\yd[SUB]^{SUP}",
  "ye" => "\\ye[SUB]^{SUP}",
  "\\[Mu]" => "\\mu^{SUP}_{SUB}",
  "\\[Mu]p" => "\\mu'^{SUP}_{SUB}",
  "\\[Lambda]" => "\\lambda^{SUP}_{SUB}",
  "\\[Lambda]p" => "\\lambda'^{SUP}_{SUB}",
  "\\[Lambda]pp" => "\\lambda''^{SUP}_{SUB}",
  "yudagyu" => "(\\yu^\\dagger\\yu)^{SUP}_{SUB}",
  "yddagyd" => "(\\yd^\\dagger\\yd)^{SUP}_{SUB}",
  "yedagye" => "(\\ye^\\dagger\\ye)^{SUP}_{SUB}",
  "yuyudag" => "(\\yu\\yu^\\dagger)^{SUP}_{SUB}",
  "ydyddag" => "(\\yd\\yd^\\dagger)^{SUP}_{SUB}",
  "yeyedag" => "(\\ye\\ye^\\dagger)^{SUP}_{SUB}",
};

my $scalar_conj = {
  "Hu" => "\\hu_{SUB}^{SUP*}",
  "Hd" => "\\hd_{SUB}^{SUP*}",
  "Q"  => "\\tqL[SUB]^{SUP*}",
  "bU" => "\\tuR[SUB]^{SUP}",
  "bD" => "\\tdR[SUB]^{SUP}",
  "L"  => "\\tlL[SUB]^{SUP*}",
  "bE" => "\\teR[SUB]^{SUP}"
};

my $param_conj = {
  "yu" => "\\yu[SUB]^{SUP*}",
  "yd" => "\\yd[SUB]^{SUP*}",
  "ye" => "\\ye[SUB]^{SUP*}",
  "\\[Mu]" => "\\mu^{SUP*}_{SUB}",
  "\\[Mu]p" => "\\mu'^{SUP*}_{SUB}",
  "\\[Lambda]" => "\\lambda^{SUP*}_{SUB}",
  "\\[Lambda]p" => "\\lambda'^{SUP*}_{SUB}",
  "\\[Lambda]pp" => "\\lambda''^{SUP*}_{SUB}",
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
  "\\[Mu]p" => "|\\mu'^{SUP}_{SUB}|^2",
  "\\[Lambda]" => "|\\lambda^{SUP}_{SUB}|^2",
  "\\[Lambda]p" => "|\\lambda'^{SUP}_{SUB}|^2",
  "\\[Lambda]pp" => "|\\lambda''^{SUP}_{SUB}|^2",
  "gY" => "g_Y^2",
  "g2" => "g_2^2",
  "g3" => "g_3^2",
};

my $fermion = {
  "Hu" => "\\thu_{SUB}^{SUP}",
  "Hd" => "\\thd_{SUB}^{SUP}",
  "Q"  => "\\qL[SUB]^{SUP}",
  "bU" => "\\uR[SUB]^{\\cc SUP}",
  "bD" => "\\dR[SUB]^{\\cc SUP}",
  "L"  => "\\lL[SUB]^{SUP}",
  "bE" => "\\eR[SUB]^{\\cc SUP}"
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
    $tex = $fermion->{$name} or die "undefined scalar $name";
  }
  $tex =~ s/SUB/$subscript/;
  $tex =~ s/SUP/$superscript/;
  return $tex;
}

foreach my $line(<>){
  $line =~ s/_\{\}//g;
  $line =~ s/\@(P|S|F|SF|PC|SC|S2|S4|P2):(.+?):(.*?):(.*?)\@/fieldname_to_tex($1, $2, $3, $4)/ge;
  $line =~ s/@(\\epsilon|f):(.*?):(.*?)@/$1_{$2}^{$3}/g;
  $line =~ s/_\{\}//g;
  $line =~ s/\[\]//g;
  $line =~ s/\^\{\}//g;
  $line =~ s/'\^\{/^\{\\prime /g;
  $line =~ s/'\^\{/^\{\\prime /g;
  $line =~ s/\$/\@/g;
  $line =~ s/\\left\(\s*\(-1\)/\\left\( - /g;
  $line =~ s/\+\s*\(-1\)\s*/- /g;
  $line =~ s/\\frac\{(1)\}\{(\d+)\}(g_Y\^2|g_2\^2|g_3\^2)/\\frac{$3}{$2}/g;
  $line =~ s/\\frac\{(\d+)\}\{(\d+)\}(g_Y\^2|g_2\^2|g_3\^2)/\\frac{$1$3}{$2}/g;
  print($line);
}
