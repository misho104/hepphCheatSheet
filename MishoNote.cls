% Time-Stamp: <2022-06-25 16:11:17>
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{MishoNote}[2022/06/24 Sho Iwamoto]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newif\ifmisho@cmyk
\newcount\misho@pdftype
\DeclareOption{10pt}{\def\misho@font@size{10pt}}
\DeclareOption{11pt}{\def\misho@font@size{11pt}}
\DeclareOption{draft}{\def\misho@isdraft{draft}}
\DeclareOption{final}{\def\misho@isdraft{final}}
\DeclareOption{pdf0}{\misho@cmyktrue \misho@pdftype=0\def\misho@hropt{bookmarks=True}}
\DeclareOption{pdfx}{\misho@cmyktrue \misho@pdftype=1\def\misho@hropt{bookmarks=False}}
\DeclareOption{pdfa}{\misho@cmykfalse\misho@pdftype=2\def\misho@hropt{bookmarks=True}}
\ExecuteOptions{11pt,final,pdf0}
\ProcessOptions

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\pdfvariable omitcidset=1
\LoadClass[a4paper,\misho@font@size,\misho@isdraft]{article}
\usepackage{hyperxmp}
\usepackage[final,keeppdfinfo,psdextra,pdfversion=1.6,\misho@hropt]{hyperref}
\hypersetup{
  breaklinks=True, pdfborder=0 0 0,
  colorlinks=true, urlcolor=pBlue, linkcolor=pBlue, citecolor=pGreen}

\ifnum\misho@pdftype=1\relax%
  \dimen0=0.996264009963\paperwidth\relax
  \edef\pdfx@mwidth{\strip@pt\dimen0}%
  \advance\dimen0 -25\p@
  \edef\pdfx@twidth{\strip@pt\dimen0}%
  \dimen0=0.996264009963\paperheight\relax
  \edef\pdfx@mheight{\strip@pt\dimen0}%
  \advance\dimen0 -20\p@
  \edef\pdfx@theight{\strip@pt\dimen0}%
  \edef\mypdfpageattr{
    /MediaBox[0 0 \pdfx@mwidth\space \pdfx@mheight]^^J
    /BleedBox[0 0 \pdfx@mwidth\space \pdfx@mheight]^^J
    /CropBox[0 0 \pdfx@mwidth\space \pdfx@mheight]^^J
    /TrimBox[25 20 \pdfx@twidth\space \pdfx@theight]
  }
  \expandafter\pdfpageattr\expandafter{\mypdfpageattr}
  \immediate\pdfobj stream attr{/N 4} file{FOGRA39L_coated.icc}
  \pdfcatalog{%
    /OutputIntents [<<
      /Type /OutputIntent
      /S /GTS_PDFX
      /OutputCondition(FOGRA39L Coated)
      /OutputConditionIdentifier (Offset printing, according to ISO 12647-2:2004/Amd 1, OFCOM, paper type 1 or 2 = coated art, 115 g/m2, tone value increase curves A (CMY) and B (K))
      /DestOutputProfile \the\pdflastobj\space 0 R
      /RegistryName(http://www.fogra.org)
      /Info (FOGRA39L coated) >>]}
  \hypersetup{pdfxstandard={PDF/X-4},pdftrapped=True,pdfpagemode=UseNone,pdfstartview=}
  \global\def\hyper@linkfile#1#2#3{\Hy@colorlink\@filecolor#1\Hy@xspace@end}
  \global\def\hyper@linkurl#1#2{\Hy@colorlink\@urlcolor#1\endgroup\Hy@xspace@end}
  \global\def\hyper@linkstart#1#2#3{\Hy@colorlink\@linkcolor#3\endgroup\Hy@xspace@end}
  \global\let\hyper@linkend\relax
  \global\def\Hy@StartlinkName#1#2{}
  \global\def\close@pdflink{\Hy@VerboseLinkStop\Hy@endcolorlink}%
  \global\def\AcrobatMenu#1#2{#2}
\fi
\ifnum\misho@pdftype=2\relax%
  \immediate\pdfobj stream attr{/N 3} file{sRGB.icc}
  \pdfcatalog{%
    /OutputIntents [<<
      /Type /OutputIntent
      /S /GTS_PDFA1
      /DestOutputProfile \the\pdflastobj\space 0 R
      /OutputConditionIdentifier (sRGB)
      /Info (sRGB) >>]}
  \hypersetup{pdfa,pdfapart=2,pdfaconformance=u,pdftrapped=True}
\fi

\ifmisho@cmyk
  \usepackage[hyperref,cmyk]{xcolor}
\else
  \usepackage[hyperref,rgb]{xcolor}
\fi

\def\title@cr{}
\def\title@ce{}
\def\title@cu{}
\def\title@lu{}
\define@key{Hyp}{pdfcopyright}{\hyxmp@pdfstringdef\@pdfcopyright{#1}\def\title@cr{#1}}
\define@key{Hyp}{pdfcontactemail}{\hyxmp@pdfstringdef\@pdfcontactemail{#1}\def\title@ce{#1}}
\define@key{Hyp}{pdfcontacturl}{\hyxmp@pdfstringdef\@pdfcontacturl{#1}\def\title@cu{#1}}
\define@key{Hyp}{pdflicenseurl}{\hyxmp@pdfstringdef\@pdflicenseurl{#1}\def\title@lu{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\automatichyphenmode=1
\def\misho@font@english{STIXTwoText}
\def\misho@font@sf{Roboto}
\def\misho@font@tt{Roboto Mono}
%\def\misho@font@math{latinmodern-math.otf}
\def\misho@font@math{STIXTwoMath-Regular.otf}

\usepackage[quiet]{fontspec}
\usepackage[luatexrenderer=OpenType]{polyglossia}
    % no particular reason to avoid Harfbuzz
\newfontfamily{\englishfont}[Ligatures={TeX}]{\misho@font@english}
\newfontfamily{\englishfontsf}[Scale=0.91]{\misho@font@sf}
\newfontfamily{\englishfonttt}[Scale=0.85]{\misho@font@tt}
\newfontfamily{\japanesefont}[
  ItalicFont=HaranoAjiMincho-Regular.otf,
  ItalicFeatures={FakeSlant}
]{HaranoAjiMincho-Regular.otf}
\setdefaultlanguage[variant=us]{english}
\setmainfont{\misho@font@english}
\setsansfont[Scale=0.91]{\misho@font@sf}
\setmonofont[Scale=0.85]{\misho@font@tt}

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

\abovedisplayskip=12pt plus 3pt minus 9pt
\belowdisplayskip=12pt plus 3pt minus 9pt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[hhmmss]{datetime}
\newdateformat{mydate}{\THEDAY-\shortmonthname-\THEYEAR}

%\newdimen\head@colwidth
%\head@colwidth\textwidth
%\advance\head@colwidth -11em % for datetime region
%\divide\head@colwidth by 2

\def\leftmark{\expandafter\@leftmark\firstmark\@empty\@empty}
\def\rightmark{\expandafter\@rightmark\botmark\@empty\@empty}

\def\head@hrule{} % \lower1mm\null\vadjust{{\color{lightgray}\hrule height .7mm}\vskip-2mm}
\def\head@h{}     % \ifnum \c@secnumdepth >\z@ \leftmark\fi
\def\head@j{[\jobname\,@\,\mydate\today~\currenttime]}
\def\head@hstyle{\sffamily\small}
\def\head@jstyle{\fontsize{9}{12}\selectfont\color{lightgray}\texttt}
\def\head@pstyle{\fontsize{12}{12}\selectfont\sffamily\bfseries}
\def\ps@plain{%
  \def\@evenfoot{} % {\reset@font\hfil\thepage\hfil}
  \let\@oddfoot\@evenfoot
  \def\@evenhead{%
    \kern2mm{\head@hstyle{\head@h}}\hfil{\head@jstyle{\head@j}}%
    \makebox[3em][r]{\head@pstyle\thepage}\kern2mm%
    \aftergroup\head@hrule}%
  \let\@oddhead\@evenhead
}
\def\sectionmark#1{\markright{\ifnum \c@secnumdepth >\z@ %
  {\thesection}\hskip1em
\fi #1}}%
\pagestyle{plain}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\@headframebox#1{
  \setlength\@tempdima{25.5mm}%
  \advance\@tempdima 32mm%
  \begin{tikzpicture}[remember picture,overlay]
    \node[xshift=\@total@leftsep,yshift=-\@tempdima] at (current page.north west) {%
      \begin{tikzpicture}[remember picture, overlay]
        \fill[lightgray!50] (0,0) rectangle (\textwidth,32mm); % (2,16,2)mm plus 12mm space
        \draw (2mm,20mm) rectangle (\textwidth-2mm, 30mm) {}; #1 %
      \end{tikzpicture}
    };
  \end{tikzpicture}%
  \vskip28mm%
}

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

\def\link@ifurl#1#2{\IfStrEq{#1}{}{#2}{\href{#1}{#2}}}
\def\maketitle{%
\begin{titlepage}%
  \IfStrEq{\title@cr}{}{\setlength\@tempdimb{6mm}}{\setlength\@tempdimb{7.5mm}}
  \setcounter{page}{0}
  \let\footnoterule\relax
  \let\footnote\thanks
  \@headframebox{%
    \node[fill=lightgray!50,anchor=south west,xshift= 5mm,yshift=15.7mm]
      {\normalfont\fontsize{24}{24}\selectfont\bfseries\strut\@title};
    \node[anchor=south west,xshift=85mm,yshift=\@tempdimb]
      {\headfont\fontsize{16}{16}\selectfont \@author\strut};
    \advance\@tempdimb -4.5mm%
    \node[anchor=south west,xshift=85mm,yshift=\@tempdimb]
      {\ttfamily\mydate\today~\currenttime\strut};
    \IfStrEq{\title@cr}{}{}{%
      \node[anchor=south west,xshift=85mm,yshift=-1mm]{%
        \link@ifurl{\title@lu}{\sffamily\small\color{gray}\copyright\title@cr}\strut};
    }
}}
\def\endmaketitle{\par\vfil\null\end{titlepage}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% technical modification of URL fields in bibliography
\let\original@thebibliography\thebibliography
\let\original@bibitem\bibitem
%\def\thebibliography{%
%  \gdef\url##1{\rightskip 1em plus 1fil\linebreak[0]\mbox{\href{##1}{\hyper@normalise{\ttfamily{##1}}}}}%
%  \original@thebibliography%
%}
\def\bibitem{\rightskip0em\original@bibitem}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\definecolor{gray}         {gray}{0.5}
\definecolor{lightgray}    {gray}{0.8}
\definecolor{dimgray}      {gray}{0.9}
\ifmisho@cmyk  % CMYK
  \definecolor{pBlue}        {cmyk}{0.894,0.688,0.000,0} % #0e51c9
  \definecolor{pPink}        {cmyk}{0.000,0.834,0.000,0} % #ff45a0
  \definecolor{pGreen}       {cmyk}{0.782,0.314,1.000,0} % #348d1b
  \definecolor{pLightOrange} {cmyk}{0.000,0.223,0.419,0} % #ffd69d
  \definecolor{pLightPurple} {cmyk}{0.452,0.580,0.000,0} % #aa78d6
  \definecolor{pLightGreen}  {cmyk}{0.570,0.000,0.374,0} % #00ffd0
  \definecolor{AltDefA}      {cmyk}{0.000,0.892,0.946,0}
  \definecolor{AltDefB}      {cmyk}{0.911,0.788,0.000,0} % but not to abuse
\else          % RGB
  \definecolor{pBlue}        {rgb}{0.0549,0.3176,0.7882} % #0e51c9
  \definecolor{pPink}        {rgb}{1.0000,0.2706,0.6275} % #ff45a0
  \definecolor{pGreen}       {rgb}{0.2039,0.5529,0.1059} % #348d1b
  \definecolor{pLightOrange} {rgb}{1.0000,0.8392,0.6157} % #ffd69d
  \definecolor{pLightPurple} {rgb}{0.6667,0.4706,0.8392} % #aa78d6
  \definecolor{pLightGreen}  {rgb}{0.0000,1.0000,0.8157} % #00ffd0
  \definecolor{AltDefA}      {rgb}{1.0000,0.2000,0.0000}
  \definecolor{AltDefB}      {rgb}{0.1500,0.5000,0.7000} % but not to abuse
\fi
% these are color command but should be considered as emphasize commands
\newcommand\@colored[2]{{\color{#1}#2}}
\newcommand\GRAY {\@colored{gray}}
\newcommand\BLUE {\@colored{pBlue}}
\newcommand\PINK {\@colored{pPink}}
\newcommand\GREEN{\@colored{pGreen}}
\newcommand\C    {\@ifstar{\@colored{AltDefB}}{\@colored{AltDefA}}}

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

\DeclareTColorBox[use counter=NoteBox]{NoteBox}{O{}}{%
  reset,enhanced,
  title={\theNoteBox},
  boxrule=0pt,frame hidden,
  borderline west={2mm}{\z@}{gray!50},colback=gray!10,
  left skip=17.647mm, left=4.706mm, width=1.176\NoteBoxWidthA,
  coltitle=black,fonttitle=\headfont,
  scale=0.85,
  attach title to upper,after title={:~},#1
}
\newcommand\Note[1]{\begin{NoteBox}#1\end{NoteBox}}

\DeclareTColorBox[use counter=NoteBox]{RemarkBox}{O{}}{%
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

\renewcommand\theNoteBox{$\sharp$\@arabic\c@NoteBox}

\newcommand\g@bble@put[1]{#1}
\DeclareDocumentCommand{\RefBox}{O{6cm} O{text width=5cm} > { \TrimSpaces } m}{%
  \begin{tikzpicture}[overlay,anchor=north east,remember picture,every node/.style={#2}]%
  \draw [draw=none] (\textwidth,3\baselineskip) node {\hfill\colorbox{pGreen!10}{\small\GREEN{#3}}};%
  \end{tikzpicture}\g@bble@put}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcounter{NoteAnchor}

\def\NoteBoxStack{}
\NewDocumentCommand\addnote{som}{%
  \stepcounter{NoteAnchor}%
  \IfValueTF{#2}{\def\notetag{#2}}{\let\notetag\theNoteAnchor}%
  \IfBooleanTF{#1}{\def\@NoteBoxStack{}}{\let\@NoteBoxStack\NoteBoxStack}%
  \global\edef\NoteBoxStack{\@NoteBoxStack\noexpand\OutputNote@{\notetag}{#3}}%
  \mbox{$^{\text{\ref{Note:\notetag}}}$}\relax}
\def\OutputNote@#1#2{{\NoteBox[label=Note:#1]{#2}\endNoteBox}\relax}
\def\OutputNote{\NoteBoxStack\global\def\NoteBoxStack{}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{fancyvrb,ifplatform,listings}
\lstset{columns=[l]fullflexible,basicstyle=\ttfamily\small,xleftmargin=15mm,frame=L,keepspaces=true}
\CustomVerbatimCommand{\code}{Verb}{}
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
\newcommand*\dd{{\mathrm{d}}}
\newcommand*\DD{{\mathrm{D}}}
\newcommand*\TT{{\mathrm{T}}}
\newcommand*\cc{{\mathrm{c}}}
\newcommand*\RR{{\mathbb{R}}}
\newcommand*\CC{{\mathbb{C}}}
\newcommand*\KK{{\mathbb{K}}}
\newcommand*\GG{{\mathbb{G}}}

\newcommand*\vep{\varepsilon} % \vep^{12} = \vep^{0123} = 1 but \vep_{12} = \vep_{0123} = -1.
\newcommand*\nep{\epsilon}    % to distinguish from vep:  \nep^{12} = \nep_{12} = +1.

\newcommand*\vc[1]{{\mathbf{#1}}}
\newcommand*\vipro[2]{\vc{#1}\cdot\vc{#2}}
\newcommand*\vopro[2]{\vc{#1}\times\vc{#2}}

\NewDocumentCommand\w  {sm}{\IfBooleanTF{#1}{_{\text{#2}}}{_{\mathrm{#2}}}}
\NewDocumentCommand\wup{sm}{\IfBooleanTF{#1}{^{\text{#2}}}{^{\mathrm{#2}}}}

\NewDocumentCommand\abs  {sm}{\IfBooleanTF{#1}{\left\lvert#2\right\rvert}{\lvert#2\rvert}}
\NewDocumentCommand\norm {sm}{\IfBooleanTF{#1}{\left\lVert#2\right\rVert}{\lVert#2\rVert}}
\NewDocumentCommand\vnorm{sm}{\IfBooleanTF{#1}{\left\lVert\vc{#2}\right\rVert}{\lVert\vc{#2}\rVert}}
\NewDocumentCommand\mean {sm}{\IfBooleanTF{#1}{\left\langle#2\right\rangle}{\langle#2\rangle}}

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
\DeclareMathOperator{\rank}   {\mathrm{rank}}
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

\usepackage{subcaption,booktabs,wrapfig,slashed,xspace,xstring,braket,cancel}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[capitalize]{cleveref}

\renewcommand\thefootnote{*\arabic{footnote}}
\numberwithin{equation}{section}

\newcommand\package[2][\relax]{\texttt{#2}\ifx#1\relax\relax\else~\texttt{#1}\fi}

\newcommand{\TODO}[1]{{\color{red}{$\clubsuit$\texttt{TODO:}#1$\clubsuit$}}}
\newcommand{\TOCHECK}[1][needs proofreeding]{{\color{red}{$\clubsuit$#1$\clubsuit$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

