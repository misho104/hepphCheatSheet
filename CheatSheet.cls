% Time-Stamp: <2025-02-09 17:12:58>
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{CheatSheet}[2022/05/10 Sho Iwamoto]

\def\misho@ispdfx{}
\DeclareOption{draft}{\def\misho@isdraft{draft}}
\DeclareOption{final}{\def\misho@isdraft{final}}
\DeclareOption{pdfx}{\def\misho@ispdfx{pdfx}}
\ExecuteOptions{final}
\ProcessOptions\relax

\usepackage[fleqn]{amsmath}
\LoadClass[10pt,\misho@isdraft,\misho@ispdfx]{MishoNote}

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

\renewcommand\section{\@startsection {section}{1}{\z@}%
                                   {-3.5ex \@plus -1ex \@minus -.2ex}%
                                   {2.3ex \@plus.2ex}%
                                   {\headfont\Large\bfseries}}
\renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.0ex \@plus .2ex}%
                                     {\headfont\large\bfseries}}
\renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.0ex \@plus .2ex}%
                                     {\headfont\normalsize\bfseries}}
\renewcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
                                    {2.25ex \@plus1ex \@minus.2ex}%
                                    {-1em}%
                                    {\headfont\normalsize\bfseries}}
\renewcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}%
                                       {2.25ex \@plus1ex \@minus .2ex}%
                                       {-1em}%
                                      {\headfont\normalsize\bfseries}}

\newenvironment{lalignat}{\begingroup\@mathmargin\z@\start@align\z@\st@rredfalse}{\endalign\endgroup}
\newenvironment{lalignat*}{\begingroup\@mathmargin\z@\start@align\z@\st@rredtrue}{\endalign\endgroup}
\newcommand\llabel[1]{&\text{#1}\quad&&}
