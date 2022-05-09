% Time-Stamp: <2022-05-09 21:10:41>
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{CheatSheet}[2022/05/10 Sho Iwamoto]

\LoadClass[a4paper,10pt]{article}
\usepackage[fleqn]{amsmath}\automatichyphenmode=1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[a-2u]{pdfx}
\pdfvariable omitcidset=1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\misho@font@english{STIXTwoText}
\def\misho@font@sf{Roboto}
\def\misho@font@tt{Roboto Mono}
%\def\misho@font@math{latinmodern-math.otf}
\def\misho@font@math{STIXTwoMath-Regular.otf}

\usepackage[luatexrenderer=OpenType]{polyglossia} % automatically load fontspec
    % no particular reason to avoid Harfbuzz
\newfontfamily{\englishfont}[Ligatures={TeX}]{\misho@font@english}
\newfontfamily{\englishfontsf}[Scale=0.91]{\misho@font@sf}
\newfontfamily{\englishfonttt}[Scale=0.85]{\misho@font@tt}
\newfontfamily{\japanesefont}{HaranoAjiMincho-Regular.otf}
\setmainfont{\misho@font@english}
\setsansfont[Scale=0.91]{\misho@font@sf}
\setmonofont[Scale=0.85]{\misho@font@tt}
\setdefaultlanguage[variant=us]{english}
\setotherlanguages{japanese}

\newcommand*\JAPANESE[1]{\japanese#1\endjapanese}

% MathFont setting copied from MySlideFont.sty
  \usepackage{unicode-math}
  \ExplSyntaxOn
    \bool_gset_false:N \g__um_bfliteral_bool
    \bool_gset_true:N  \g__um_bfupGreek_bool
    \bool_gset_false:N \g__um_bfupgreek_bool
    \bool_gset_false:N \g__um_bfupLatin_bool
    \bool_gset_false:N \g__um_bfuplatin_bool
    \bool_gset_false:N \g__um_mathrm_text_bool % I understand their philosophy
    \bool_gset_false:N \g__um_mathit_text_bool % but still not use it for an
    \bool_gset_false:N \g__um_mathbf_text_bool % inconsistency in greek.
    \bool_gset_false:N \g__um_mathsf_text_bool
    \bool_gset_false:N \g__um_mathtt_text_bool
  \ExplSyntaxOff
  \setmathfont{\misho@font@math}
  \setoperatorfont\mathrm

  % fine tuning of some letters
  % https://tex.stackexchange.com/questions/364310/
  \setmathfont{latinmodern-math.otf}[range={\mupUpsilon,\mitUpsilon,\mbfUpsilon,\mbfitUpsilon}]
  \setmathfont{\misho@font@math}[range=\int]
  \AtBeginDocument{\renewcommand*\Upsilon{\mupUpsilon}}

% Logical fonts
\newcommand*{\headfont}{\normalcolor\sffamily\bfseries}

% More math fonts (but not ever used)
% \usepackage{wasysym}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand*\@convertto[2]{\strip@pt\dimexpr #2*65536/\number\dimexpr 1#1}
\newcommand*\ShowLength[1]{\@convertto{em}{#1}em = \@convertto{mm}{#1}mm} % for debugging

\setlength\textwidth{160mm}  % 25mm margin
\setlength\textheight{237mm}  % 30mm margin
\setlength\headheight{18pt}
\setlength\headsep{16pt}

\newdimen\@tempdima
\newdimen\@total@leftsep
\newdimen\@total@headsep

\@tempdima\paperheight
\advance\@tempdima -\textheight
\divide\@tempdima by 2
\@total@headsep\@tempdima

\advance\@tempdima -\headheight
\advance\@tempdima -\headsep
\advance\@tempdima -1in % the one-inch
\topmargin\@tempdima

\@tempdima\paperwidth
\advance\@tempdima -\textwidth
\divide\@tempdima by 2
\@total@leftsep\@tempdima
\advance\@tempdima -1in % the one-inch
\oddsidemargin\@tempdima\relax
\evensidemargin\oddsidemargin\relax

% baselineskip = 1.242em = 4.77988mm
\parskip=1mm plus .5mm minus 1mm

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\let\cheatsheet@s@normalsize\normalsize
\let\cheatsheet@s@small\small
\let\cheatsheet@s@footnotesize\footnotesize
\let\cheatsheet@s@scriptsize\scriptsize

\DeclareRobustCommand\cheatsheet@d@normalsize{%
   \@setfontsize\normalsize{9}{10.8}%
   \abovedisplayskip       3 \p@\@plus 2\p@\@minus 3\p@\relax
   \abovedisplayshortskip    \z@\@plus 3\p@\relax
   \belowdisplayshortskip  3 \p@\@plus 2\p@\@minus 3\p@\relax
   \belowdisplayskip\abovedisplayskip
   \let\@listi\@listI}
\DeclareRobustCommand\cheatsheet@d@small{%
   \@setfontsize\small{8.1}{9.9}%
   \def\@listi{\leftmargin\leftmargini%
               \topsep 3.6\p@ \@plus1.8\p@ \@minus1.8\p@%
               \parsep 1.8\p@ \@plus0.9\p@ \@minus0.9\p@%
               \itemsep \parsep}}
\DeclareRobustCommand\cheatsheet@d@footnotesize{%
   \@setfontsize\footnotesize{8.1}{8.5}%
   \def\@listi{\leftmargin\leftmargini%
               \topsep 2.7\p@ \@plus0.9\p@ \@minus0.9\p@%
               \parsep 1.8\p@ \@plus0.9\p@ \@minus0.9\p@%
               \itemsep \parsep}}
\DeclareRobustCommand\cheatsheet@d@scriptsize{\@setfontsize\scriptsize{6.3}{7.2}}

\def\summarystyle{%
  \let\normalsize  \cheatsheet@s@normalsize%
  \let\small       \cheatsheet@s@small%
  \let\footnotesize\cheatsheet@s@footnotesize%
  \let\scriptsize  \cheatsheet@s@scriptsize%
  \setlength\parindent{10\p@}\normalsize}
\def\detailstyle{%
  \let\normalsize  \cheatsheet@d@normalsize%
  \let\small       \cheatsheet@d@small%
  \let\footnotesize\cheatsheet@d@footnotesize%
  \let\scriptsize  \cheatsheet@d@scriptsize%
  \setlength\parindent{9\p@}\normalsize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[hhmmss]{datetime}
\newdateformat{mydate}{\THEDAY-\shortmonthname-\THEYEAR}

\def\EvenFootPlain{}
\def\ps@plain{%
  \def\@evenfoot{} % \hfil\color{dimgray}{\fontsize{8}{12}\selectfont\EvenFootPlain}}
  \let\@oddfoot\@evenfoot
  \def\@evenhead{%
  \kern2mm{}\hfil{\fontsize{9}{12}\selectfont\color{lightgray}\texttt{[\jobname\,@\,\mydate\today~\currenttime]}}%
  \makebox[4em][r]{\fontsize{12}{12}\selectfont\sffamily\bfseries\thepage}\kern2mm}
  \let\@oddhead\@evenhead
}
\pagestyle{plain}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\renewcommand\section{\@startsection {section}{1}{\z@}%
                                   {-3.5ex \@plus -1ex \@minus -.2ex}%
                                   {2.3ex \@plus.2ex}%
                                   {\headfont\Large\bfseries}}
\renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.5ex \@plus .2ex}%
                                     {\headfont\large\bfseries}}
\renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.5ex \@plus .2ex}%
                                     {\headfont\normalsize\bfseries}}
\renewcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
                                    {3.25ex \@plus1ex \@minus.2ex}%
                                    {-1em}%
                                    {\headfont\normalsize\bfseries}}
\renewcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}%
                                       {3.25ex \@plus1ex \@minus .2ex}%
                                       {-1em}%
                                      {\headfont\normalsize\bfseries}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\definecolor{gray}         {gray}{0.5}
\definecolor{lightgray}    {gray}{0.8}
\definecolor{dimgray}      {gray}{0.9}
\definecolor{pBlue}        {rgb}{0.0549,0.3176,0.7882} % #0e51c9
\definecolor{pPink}        {rgb}{1.0000,0.2706,0.6275} % #4ff5a0
\definecolor{pGreen}       {rgb}{0.2039,0.5529,0.1059} % #348d1b
\definecolor{pLightOrange} {rgb}{1.0000,0.8392,0.6157} % #ffd69d
\definecolor{pLightPurple} {rgb}{0.6667,0.4706,0.8392} % #aa78d6
\definecolor{pLightGreen}  {rgb}{0.0000,1.0000,0.8157} % #00ffd0
\definecolor{AltDefA}      {rgb}{1.0000,0.2000,0.0000}
\definecolor{AltDefB}      {rgb}{0.1500,0.5000,0.7000} % but not to abuse

% these are color command but should be considered as emphasize commands
\newcommand\@colored[2]{{\color{#1}#2}}
\newcommand\BLUE {\@colored{pBlue}}
\newcommand\PINK {\@colored{pPink}}
\newcommand\GREEN{\@colored{pGreen}}
\newcommand\C    {\@ifstar{\@colored{AltDefB}}{\@colored{AltDefA}}}

\usepackage{hyperref}
\hypersetup{
  pdfborder=0 0 0,
  colorlinks=true, urlcolor=pBlue, linkcolor=pBlue, citecolor=pGreen}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[xparse,skins]{tcolorbox}
\tcbsetforeverylayer{
  parbox=false,
  boxsep=0mm,
  before skip balanced=12pt plus 3pt minus 9pt,
  after skip balanced=12pt plus 3pt minus 9pt
}

\newcounter{NoteBox}

% margin(15mm) + bar(2mm) + padding (2mm) is realized by
% margin=15mm, padding=4mm, bar 2mm noshift
% invert-rescaling only for margin and padding, not for bar.
% width = textwidth - trueleftskip

\newdimen\NoteBoxWidthA
\NoteBoxWidthA\textwidth
\advance\NoteBoxWidthA-15mm

\DeclareTColorBox[use counter=NoteBox]{NoteBox}{o}{%
  reset,enhanced,
  title={\theNoteBox},
  boxrule=0pt,frame hidden,
  borderline west={2mm}{\z@}{gray!50},colback=gray!10,
  left skip=17.647mm, left=4.706mm, width=1.176\NoteBoxWidthA,
  coltitle=black,fonttitle=\headfont,
  scale=0.85,
  attach title to upper,after title={:~},#1
}
\newcommand*\Note[1]{\NoteBox #1\endNoteBox}

\DeclareTColorBox[use counter=NoteBox]{RemarkBox}{o}{%
  reset,enhanced,
  title={Remark \theNoteBox},
  boxrule=0pt,frame hidden,
  borderline west={2mm}{\z@}{gray!50},colback=gray!10,
  left skip=15mm, left=4mm,
  coltitle=black,fonttitle=\headfont,
  attach title to upper,after title={:~},#1
}
\newcommand*\Remark[1]{\RemarkBox #1\endRemarkBox}

\DeclareTColorBox[]{DownPara}{}{%
  reset,enhanced,
  interior hidden,frame hidden,
  left skip=15mm,left=0pt,boxrule=0pt,right=0pt
}

\newcommand\g@bble@put[1]{#1}
\DeclareDocumentCommand{\RefBox}{O{6cm} O{text width=5cm} > { \TrimSpaces } m}{%
  \begin{tikzpicture}[overlay,anchor=north east,remember picture,every node/.style={#2}]%
  \draw [draw=none] (\textwidth,3\baselineskip) node {\hfill\colorbox{pGreen!10}{\small\GREEN{#3}}};%
  \end{tikzpicture}\g@bble@put}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{fancyvrb,ifplatform,listings}
\lstset{columns=[l]fullflexible,basicstyle=\ttfamily\small,xleftmargin=15mm,frame=L,keepspaces=true}
\CustomVerbatimCommand{\code}{Verb}{} %,formatcom=\color{black}}
\ifshellescape
\usepackage{minted}
\def\minted@formatter{lib/minted_formatter.py -x}
\setminted{linenos,xleftmargin=15mm,breaklines,fontsize=\small,frame=leftline,stepnumber=5,framesep=2\fboxsep,escapeinside=!!,mathescape=true}
%\setminted[console]{xleftmargin=1fboxsep,frame=none}
\usemintedstyle[wolfram]{mathematica}
\else
\lstnewenvironment{minted}[1]
  {\csname\@lst @SetFirstNumber\endcsname}
  {\csname\@lst @SaveFirstNumber\endcsname}
\def\mintinline#1{\code}
\fi

%\DeclareUnicodeCharacter{02BC}{'}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ReDeclareMathCommand
% https://tex.stackexchange.com/questions/175251/
\newcommand*\RedeclareMathOperator{%
  \@ifstar{\def\rmo@s{m}\rmo@redeclare}{\def\rmo@s{o}\rmo@redeclare}%
}
\newcommand*\rmo@redeclare[2]{%
  \begingroup \escapechar\m@ne\xdef\@gtempa{{\string#1}}\endgroup
  \expandafter\@ifundefined\@gtempa
     {\@latex@error{\noexpand#1undefined}\@ehc}%
     \relax
  \expandafter\rmo@declmathop\rmo@s{#1}{#2}}
\newcommand*\rmo@declmathop[3]{%
  \DeclareRobustCommand{#2}{\qopname\newmcodes@#1{#3}}%
}

\newcommand*\ii{{\mathrm{i}}}
\newcommand*\ee{{\mathrm{e}}}
\newcommand*\dd{\mathop{\mathrm{d}}}
\newcommand*\DD{\mathop{\mathrm{D}}}
\newcommand*\TT{{\mathrm{T}}}
\newcommand*\cc{{\mathrm{c}}}
\newcommand*\RR{{\mathbb{R}}}
\newcommand*\CC{{\mathbb{C}}}
\newcommand*\KK{{\mathbb{K}}}
\newcommand*\GG{{\mathbb{G}}}

\newcommand*\vep{\varepsilon} % \vep^{12} = \vep^{0123} = 1 but \vep_{12} = \vep_{0123} = -1.
\newcommand*\nep{\epsilon}    % to distinguish from vep:  \nep^{12} = \nep_{12} = +1.

\newcommand*\vc[1]{{\symbfit{#1}}}
\newcommand*\vipro[2]{\vc{#1}\cdot\vc{#2}}
\newcommand*\vopro[2]{\vc{#1}\times\vc{#2}}

\NewDocumentCommand\w  {sm}{\IfBooleanTF{#1}{_{\text{#2}}{_{\mathrm{#2}}}}}
\NewDocumentCommand\wup{sm}{\IfBooleanTF{#1}{^{\text{#2}}{^{\mathrm{#2}}}}}

\NewDocumentCommand\abs  {sm}{\IfBooleanTF{#1}{\lvert#1\rvert}{\left\lvert#1\right\rvert}}
\NewDocumentCommand\norm {sm}{\IfBooleanTF{#1}{\lVert#1\rVert}{\left\lVert#1\right\rVert}}
\NewDocumentCommand\vnorm{sm}{\norm#1{\vc #2}}

\newcommand*{\wdiag}{^{\text{diag}}}

\newcommand\co[1]{\mathrm{c}_{#1}}
\newcommand\si[1]{\mathrm{s}_{#1}}
\newcommand\ta[1]{\mathrm{t}_{#1}}
\newcommand\coco[1]{\mathrm{c}^2_{#1}}
\newcommand\sisi[1]{\mathrm{s}^2_{#1}}

\RedeclareMathOperator{\Re}   {\mathrm{Re}}
\RedeclareMathOperator{\Im}   {\mathrm{Im}}
\DeclareMathOperator{\arctanh}{\mathrm{arctanh}}
\DeclareMathOperator{\arccoth}{\mathrm{arccoth}}
\DeclareMathOperator{\arcsinh}{\mathrm{arcsinh}}
\DeclareMathOperator{\arccosh}{\mathrm{arccosh}}
\DeclareMathOperator{\sech}   {\mathrm{sech}}
\DeclareMathOperator{\csch}   {\mathrm{csch}}
\DeclareMathOperator{\Tr}     {\mathrm{Tr}}
\DeclareMathOperator{\diag}   {\mathrm{diag}}
\DeclareMathOperator{\ad}     {\mathrm{ad}}
\DeclareMathOperator{\Order}  {\symcal{O}}
\DeclareMathOperator{\sign}   {\mathrm{sign}}
\DeclareMathOperator{\Br}     {\mathrm{Br}}

\newcommand*\EE{\@ifnextchar-{\@@EE}{\@EE}}
\newcommand*\@EE[1]{\ifnum#1=1 \times\!10 \else \times\!10^{#1}\fi}
\newcommand*\@@EE[2]{\times\!10^{-#2}}

\NewDocumentCommand\pfrac{omm}{\left(\frac{#2}{#3}\right)\IfValueT{#1}{^#1}}
\NewDocumentCommand\diff{O{\dd}omm}{\IfValueTF{#2}{\frac{#1^#2#3}{#1#4^#2}}{\frac{#1#3}{#1#4}}}
\newcommand*\pdiff[3][]{\diff{\partial}{#1}{#2}{#3}}

\newcommand*\diracdelta[1][]{\qopname\relax o{\ifx\\#1\\\mathrm{\delta}\else\mathrm{\delta}^{(#1)}\fi}}
\newcommand*\Kallen    [1][]{\qopname\relax o{\ifx\\#1\\\mathrm{\lambda}\else\mathrm{\lambda}^{#1}\fi}}

\newcommand*\pmat[1]{\begin{pmatrix}#1\end{pmatrix}}
\newcommand*\spmat[1]{\left(\begin{smallmatrix}#1\end{smallmatrix}\right)}

\newcommand\unit[1]{\,\mathrm{#1}\xspace}
\newcommand\eV {\unit{eV}}
\newcommand\keV{\unit{keV}}
\newcommand\MeV{\unit{MeV}}
\newcommand\GeV{\unit{GeV}}
\newcommand\TeV{\unit{TeV}}
\newcommand\PeV{\unit{PeV}}
\newcommand\fb {\unit{fb}}
\newcommand\pb {\unit{pb}}
\newcommand\iab{\unit{ab^{-1}}}
\newcommand\ifb{\unit{fb^{-1}}}
\newcommand\ipb{\unit{pb^{-1}}}
\newcommand\fm {\unit{fm}}

\renewcommand\leadsto{\mathrel{\rightdasharrow}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{slashed,xspace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[capitalize]{cleveref}
\newcommand\package[2][\relax]{\texttt{#2}\ifx#1\relax\relax\else~\texttt{#1}\fi}

\newcommand{\TODO}[1]{{\color{red}{$\clubsuit$\texttt{TODO:}#1$\clubsuit$}}}
\newcommand{\TOCHECK}[1][needs proofreeding]{{\color{red}{$\clubsuit$#1$\clubsuit$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

