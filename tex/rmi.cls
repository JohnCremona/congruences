%%%%%%%%%%%%%%%%%%%%%%%%%%%% This is file RMI4.cls%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%for articles to be submitted to Revista Matem\'atica Iberoamericana%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 15/09/2011%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%amsthm.sty [2004/08/06 v2.20] is included in this macro%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This file is based on `article.cls', 2007/10/19 v1.4h,
%% Copyright 1993 1994 1995 1996 1997 1998 1999 2000 2001 2002 2003 2004 2005 2006 2007 2008 2009
%%
\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{RMI4}
              [2011/09/15]

\newif\if@footnoteinfo
\@footnoteinfotrue

\newif\if@fnsymbolintitle
\@fnsymbolintitletrue

\newcommand\@ptsize{}
\newif\if@restonecol
\newif\if@titlepage
\@titlepagefalse
\if@compatibility\else
\DeclareOption{symbols-for-thanks}{\@fnsymbolintitletrue}
\DeclareOption{a4paper}
   {\setlength\paperheight {297mm}%
    \setlength\paperwidth  {210mm}}
\DeclareOption{a5paper}
   {\setlength\paperheight {210mm}%
    \setlength\paperwidth  {148mm}}
\DeclareOption{b5paper}
   {\setlength\paperheight {250mm}%
    \setlength\paperwidth  {176mm}}
\DeclareOption{letterpaper}
   {\setlength\paperheight {11in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{legalpaper}
   {\setlength\paperheight {14in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{executivepaper}
   {\setlength\paperheight {10.5in}%
    \setlength\paperwidth  {7.25in}}
\DeclareOption{landscape}
   {\setlength\@tempdima   {\paperheight}%
    \setlength\paperheight {\paperwidth}%
    \setlength\paperwidth  {\@tempdima}}
\fi
\if@compatibility
  \renewcommand\@ptsize{0}
\else
\DeclareOption{10pt}{\renewcommand\@ptsize{0}}
\fi
\DeclareOption{11pt}{\renewcommand\@ptsize{1}}
\DeclareOption{12pt}{\renewcommand\@ptsize{2}}
\if@compatibility\else
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\fi
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\DeclareOption{draft}{\setlength\overfullrule{5pt}}
\if@compatibility\else
\DeclareOption{final}{\setlength\overfullrule{0pt}}
\fi
\DeclareOption{titlepage}{\@titlepagetrue}
\if@compatibility\else
\DeclareOption{notitlepage}{\@titlepagefalse}
\fi
\if@compatibility\else
\DeclareOption{onecolumn}{\@twocolumnfalse}
\fi
\DeclareOption{twocolumn}{\@twocolumntrue}
\DeclareOption{leqno}{\input{leqno.clo}}
\DeclareOption{fleqn}{\input{fleqn.clo}}
\DeclareOption{openbib}{%
  \AtEndOfPackage{%
   \renewcommand\@openbib@code{%
      \advance\leftmargin\bibindent
      \itemindent -\bibindent
      \listparindent \itemindent
      \parsep \z@
      }%
   \renewcommand\newblock{\par}}%
}
\ExecuteOptions{a4paper,10pt,twoside,onecolumn,final}
\ProcessOptions

%%%%%%%%%%%%%%%%%%%%
%% Foot Note Info %%
%%%%%%%%%%%%%%%%%%%%

\let\save@footnote=\footnote
\long\def\special@makefntext#1{\noindent #1}%

%\def\amsclassification#1{\def\ams@@classification{#1}} %%% RMI-dor
\newcommand{\amsclassification}[2][]{%%% RMI-dor
  \ifthenelse{\equal{#1}{}}
  {\def\ams@@classification{#2}}
  {\def\ams@@classification{Primary #2; Secondary #1}}} %%% RMI-dor
\def\keywords#1{\def\listof@@keywords{#1}}

\if@footnoteinfo
 \def\ams@classification{%
  \let\save@makefntext=\@makefntext
  \let\save@makefnmark=\@makefnmark
  \let\@makefntext=\special@makefntext
  \def\@makefnmark{\relax}%
    \save@footnote{\textit{\classificationname}: \ams@@classification.}%
  \let\@makefntext=\save@makefntext
  \let\@makefnmark=\save@makefnmark
  \addtocounter{footnote}{-1}}
 \def\listof@keywords{%
  \let\save@makefntext=\@makefntext
  \let\save@makefnmark=\@makefnmark
  \let\@makefntext=\special@makefntext
  \def\@makefnmark{\relax}%
  \save@footnote{\textit{\keywordname: }\listof@@keywords.}%
  \let\@makefntext=\save@makefntext
  \let\@makefnmark=\save@makefnmark
  \addtocounter{footnote}{-1}}
\else
 \def\ams@classification{%
        \ams@@classification
    \def\listof@keywords{%
         \listof@@keywords
   }}
\fi

\def\footnote@info{%
   \ams@classification
  \listof@keywords
}

\def\par@info{%
 \if@footnoteinfo
  \relax
 \else
  \ams@classification
  \listof@keywords
 \fi}

\let\footnoteinfo=\true
 \let\fnsymbolintitle=\true

%% This is file `size10.clo'
\renewcommand\normalsize{%
   \@setfontsize\normalsize\@xpt\@xiipt
   \abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@
   \abovedisplayshortskip \z@ \@plus3\p@
   \belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@
   \belowdisplayskip \abovedisplayskip
   \let\@listi\@listI}
\normalsize
\newcommand\small{%
   \@setfontsize\small\@ixpt{11}%
   \abovedisplayskip 8.5\p@ \@plus3\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus2\p@
   \belowdisplayshortskip 4\p@ \@plus2\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 4\p@ \@plus2\p@ \@minus2\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\footnotesize{%
   \@setfontsize\footnotesize\@viiipt{9.5}%
   \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3\p@ \@plus\p@ \@minus\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\scriptsize{\@setfontsize\scriptsize\@viipt\@viiipt}
\newcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
\newcommand\large{\@setfontsize\large\@xiipt{14}}
\newcommand\Large{\@setfontsize\Large\@xivpt{18}}
\newcommand\LARGE{\@setfontsize\LARGE\@xviipt{22}}
\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}
\if@twocolumn
  \setlength\parindent{1em}
\else
  \setlength\parindent{15\p@}
\fi
\setlength\smallskipamount{3\p@ \@plus 1\p@ \@minus 1\p@}
\setlength\medskipamount{6\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\bigskipamount{12\p@ \@plus 4\p@ \@minus 4\p@}
\setlength\headheight{12\p@}
\setlength\headsep   {14\p@}%%%{25\p@}
\setlength\topskip   {10\p@}
\setlength\footskip{30\p@}
\if@compatibility \setlength\maxdepth{4\p@} \else
\setlength\maxdepth{.5\topskip} \fi
\if@compatibility
  \if@twocolumn
    \setlength\textwidth{410\p@}
  \else
    \setlength\textwidth{345\p@}
  \fi
\else
  \setlength\@tempdima{\paperwidth}
  \addtolength\@tempdima{-2in}
  \setlength\@tempdimb{345\p@}
  \if@twocolumn
    \ifdim\@tempdima>2\@tempdimb\relax
      \setlength\textwidth{2\@tempdimb}
    \else
      \setlength\textwidth{\@tempdima}
    \fi
  \else
    \ifdim\@tempdima>\@tempdimb\relax
      \setlength\textwidth{\@tempdimb}
    \else
      \setlength\textwidth{\@tempdima}
    \fi
  \fi
\fi
\if@compatibility\else
  \@settopoint\textwidth
\fi
\if@compatibility
  \setlength\textheight{43\baselineskip}
\else
  \setlength\@tempdima{\paperheight}
  \addtolength\@tempdima{-2in}
  \addtolength\@tempdima{-1.5in}
  \divide\@tempdima\baselineskip
  \@tempcnta=\@tempdima
  \setlength\textheight{\@tempcnta\baselineskip}
\fi
\addtolength\textheight{\topskip}
\if@twocolumn
 \setlength\marginparsep {10\p@}
\else
  \setlength\marginparsep{11\p@}
\fi
\setlength\marginparpush{5\p@}
\if@compatibility
  \if@twoside
     \setlength\oddsidemargin   {44\p@}
     \setlength\evensidemargin  {82\p@}
     \setlength\marginparwidth {107\p@}
  \else
     \setlength\oddsidemargin   {63\p@}
     \setlength\evensidemargin  {63\p@}
     \setlength\marginparwidth  {90\p@}
  \fi
  \if@twocolumn
     \setlength\oddsidemargin  {30\p@}
     \setlength\evensidemargin {30\p@}
     \setlength\marginparwidth {48\p@}
  \fi
\else
  \if@twoside
    \setlength\@tempdima        {\paperwidth}
    \addtolength\@tempdima      {-\textwidth}
    \setlength\oddsidemargin    {.4\@tempdima}
    \addtolength\oddsidemargin  {-1in}
    \setlength\marginparwidth   {.6\@tempdima}
    \addtolength\marginparwidth {-\marginparsep}
    \addtolength\marginparwidth {-0.4in}
  \else
    \setlength\@tempdima        {\paperwidth}
    \addtolength\@tempdima      {-\textwidth}
    \setlength\oddsidemargin    {.5\@tempdima}
    \addtolength\oddsidemargin  {-1in}
    \setlength\marginparwidth   {.5\@tempdima}
    \addtolength\marginparwidth {-\marginparsep}
    \addtolength\marginparwidth {-0.4in}
    \addtolength\marginparwidth {-.4in}
  \fi
  \ifdim \marginparwidth >2in
     \setlength\marginparwidth{2in}
  \fi
  \@settopoint\oddsidemargin
  \@settopoint\marginparwidth
  \setlength\evensidemargin  {\paperwidth}
  \addtolength\evensidemargin{-2in}
  \addtolength\evensidemargin{-\textwidth}
  \addtolength\evensidemargin{-\oddsidemargin}
  \@settopoint\evensidemargin
\fi
\if@compatibility
  \setlength\topmargin{27pt}
\else
  \setlength\topmargin{\paperheight}
  \addtolength\topmargin{-2in}
  \addtolength\topmargin{-\headheight}
  \addtolength\topmargin{-\headsep}
  \addtolength\topmargin{-\textheight}
  \addtolength\topmargin{-\footskip}     % this might be wrong!
  \addtolength\topmargin{-.5\topmargin}
  \@settopoint\topmargin
\fi
\setlength\footnotesep{6.65\p@}
\setlength{\skip\footins}{9\p@ \@plus 4\p@ \@minus 2\p@}
\setlength\floatsep    {12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\textfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\intextsep   {12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dblfloatsep    {12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\@fptop{0\p@ \@plus 1fil}
\setlength\@fpsep{8\p@ \@plus 2fil}
\setlength\@fpbot{0\p@ \@plus 1fil}
\setlength\@dblfptop{0\p@ \@plus 1fil}
\setlength\@dblfpsep{8\p@ \@plus 2fil}
\setlength\@dblfpbot{0\p@ \@plus 1fil}
\setlength\partopsep{2\p@ \@plus 1\p@ \@minus 1\p@}
\def\@listi{\leftmargin\leftmargini
            \parsep 4\p@ \@plus2\p@ \@minus\p@
            \topsep 4\p@ \@plus2\p@ \@minus2\p@   %%%8\p@ \@plus2\p@ \@minus4\p@
            \itemsep4\p@ \@plus2\p@ \@minus\p@}  %%%4\p@ \@plus2\p@ \@minus\p@
\let\@listI\@listi
\@listi
\def\@listii {\leftmargin\leftmarginii
              \labelwidth\leftmarginii
              \advance\labelwidth-\labelsep
              \topsep    2\p@ \@plus2\p@ \@minus\p@%%%4\p@ \@plus2\p@ \@minus\p@
              \parsep    2\p@ \@plus\p@  \@minus\p@
              \itemsep   \parsep}
\def\@listiii{\leftmargin\leftmarginiii
              \labelwidth\leftmarginiii
              \advance\labelwidth-\labelsep
              \topsep    2\p@ \@plus\p@\@minus\p@
              \parsep    \z@
              \partopsep \p@ \@plus\z@ \@minus\p@
              \itemsep   \topsep}
\def\@listiv {\leftmargin\leftmarginiv
              \labelwidth\leftmarginiv
              \advance\labelwidth-\labelsep}
\def\@listv  {\leftmargin\leftmarginv
              \labelwidth\leftmarginv
              \advance\labelwidth-\labelsep}
\def\@listvi {\leftmargin\leftmarginvi
              \labelwidth\leftmarginvi
              \advance\labelwidth-\labelsep}
%% End of file `size10.clo'.
\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}
\setlength\parskip{0\p@ \@plus \p@}
\@lowpenalty   51
\@medpenalty  151
\@highpenalty 301
\setcounter{topnumber}{2}
\renewcommand\topfraction{.7}
\setcounter{bottomnumber}{1}
\renewcommand\bottomfraction{.3}
\setcounter{totalnumber}{3}
\renewcommand\textfraction{.2}
\renewcommand\floatpagefraction{.5}
\setcounter{dbltopnumber}{2}
\renewcommand\dbltopfraction{.7}
\renewcommand\dblfloatpagefraction{.5}
\if@twoside
  \def\ps@headings{%
      \let\@oddfoot\@empty\let\@evenfoot\@empty
      \def\@evenhead{\thepage\hfil\slshape\leftmark}%
      \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
      \let\@mkboth\markboth
    \def\sectionmark##1{%
      \markboth {\MakeUppercase{%
        \ifnum \c@secnumdepth >\z@
          \thesection\quad
        \fi
        ##1}}{}}%
    \def\subsectionmark##1{%
      \markright {%
        \ifnum \c@secnumdepth >\@ne
          \thesubsection\quad
        \fi
        ##1}}}
\else
  \def\ps@headings{%
    \let\@oddfoot\@empty
    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
    \let\@mkboth\markboth
    \def\sectionmark##1{%
      \markright {\MakeUppercase{%
        \ifnum \c@secnumdepth >\m@ne
          \thesection\quad
        \fi
        ##1}}}}
\fi
\def\ps@myheadings{%
    \let\@oddfoot\@empty\let\@evenfoot\@empty
    \def\@evenhead{\thepage\hfil\small\scshape\leftmark}%%%\slshape
    \def\@oddhead{{\small\scshape\rightmark}\hfil\thepage}%%%\slshape
    \let\@mkboth\@gobbletwo
    \let\sectionmark\@gobble
    \let\subsectionmark\@gobble
    }
  \if@titlepage
  \newcommand\maketitle{\begin{titlepage}%
  \let\footnotesize\small
  \let\footnoterule\relax
  \let \footnote \thanks
  \null\vfil
  \vskip 60\p@
  \begin{center}%
       {\LARGE \@title \par}%
    \vskip 3em%
    {\large
     \lineskip .75em%
      \begin{tabular}[t]{c}%
        \@author
      \end{tabular}\par}%
      \vskip 1.5em%
    {\large \@date \par}%       % Set date in \large size.
  \end{center}\par
  \@thanks
  \vfil\null
  \end{titlepage}%
  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\and\relax
}
\else
\newcommand\maketitle{\par
  \begingroup
    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
    \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
    \long\def\@makefntext##1{\parindent 1em\noindent
            \hb@xt@1.8em{%
                \hss\@textsuperscript{\normalfont\@thefnmark}}##1}%
    \if@twocolumn
      \ifnum \col@number=\@ne
        \@maketitle
      \else
        \twocolumn[\@maketitle]%
      \fi
    \else
      \newpage
      \global\@topnum\z@   % Prevents figures from going at top of page.
      \@maketitle
    \fi
    \thispagestyle{fancy}\@thanks%%%{plain}\@thanks
  \endgroup
  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\and\relax
}
\def\@maketitle{%
  \newpage
  \null
  \vskip 7em
  \if@fnsymbolintitle
     \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
     \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}\,}%%%%
   \fi
   \hrule\par\vskip 1em%%%
  \begin{center}%
  \let \footnote \thanks
       {\Large\bfseries\boldmath \@title \par}%%%\LARGE
        \vskip 1.5em%
    {\large
      \lineskip .5em%
      \lineskip .5em%
      \footnote@info
      \begin{tabular}[t]{c}%
        \large\@author%%%\@author
      \end{tabular}\par}%
  \end{center}%
  \hrule%%%
  \par
  \vskip 1.5em}
\fi
\setcounter{secnumdepth}{3}
\newcounter {part}
\newcounter {section}
\newcounter {subsection}[section]
\newcounter {subsubsection}[subsection]
\newcounter {paragraph}[subsubsection]
\newcounter {subparagraph}[paragraph]
\renewcommand \thepart {\@Roman\c@part}
\renewcommand \thesection {\@arabic\c@section}
\renewcommand\thesubsection   {\thesection.\@arabic\c@subsection}
\renewcommand\thesubsubsection{\thesubsection.\@arabic\c@subsubsection}
\renewcommand\theparagraph    {\thesubsubsection.\@arabic\c@paragraph}
\renewcommand\thesubparagraph {\theparagraph.\@arabic\c@subparagraph}
\newcommand\part{%
   \if@noskipsec \leavevmode \fi
   \par
   \addvspace{4ex}%
   \@afterindentfalse
   \secdef\@part\@spart}

\def\@part[#1]#2{%
    \ifnum \c@secnumdepth >\m@ne
      \refstepcounter{part}%
      \addcontentsline{toc}{part}{\thepart\hspace{1em}#1}%
    \else
      \addcontentsline{toc}{part}{#1}%
    \fi
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \ifnum \c@secnumdepth >\m@ne
       \Large\bfseries \partname\nobreakspace\thepart
       \par\nobreak
     \fi
     \huge \bfseries #2%
     \markboth{}{}\par}%
    \nobreak
    \vskip 3ex
    \@afterheading}
\def\@spart#1{%
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \huge \bfseries #1\par}%
     \nobreak
     \vskip 3ex
     \@afterheading}
\newcommand\section{\@startsection {section}{1}{\z@}%
                                   {-5.5ex \@plus -1ex \@minus -.2ex}%%%{-3.5ex \@plus -1ex \@minus -.2ex}
                                   {2.3ex \@plus.2ex}
                                   {\normalfont\large\bfseries\boldmath}}%%%{\normalfont\Large\bfseries}}
\newcommand\subsection{\@startsection{subsection}{2}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.5ex \@plus .2ex}%
                                     {\normalfont\bfseries\boldmath}}%%%{\normalfont\large\bfseries}}
\newcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
                                     {12pt\@plus 1ex \@minus -.2ex}%%%{-3.25ex\@plus -1ex \@minus -.2ex}
                                     {-1.5ex \@plus -.2ex}%%%{1.5ex \@plus .2ex}
                                     {\normalfont\normalsize\bfseries\boldmath}}%%%{\normalfont\normalsize\bfseries}}
\newcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
                                    {3.25ex \@plus1ex \@minus.2ex}%
                                    {-1em}%
                                    {\normalfont\normalsize\bfseries}}
\newcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}%
                                       {3.25ex \@plus1ex \@minus .2ex}%
                                       {-1em}%
                                      {\normalfont\normalsize\bfseries}}
\if@twocolumn
  \setlength\leftmargini  {2em}
\else
  \setlength\leftmargini  {2.5em}
\fi
\leftmargin  \leftmargini
\setlength\leftmarginii  {2.2em}
\setlength\leftmarginiii {1.87em}
\setlength\leftmarginiv  {1.7em}
\if@twocolumn
  \setlength\leftmarginv  {.5em}
  \setlength\leftmarginvi {.5em}
\else
  \setlength\leftmarginv  {1em}
  \setlength\leftmarginvi {1em}
\fi
\setlength  \labelsep  {.5em}
\setlength  \labelwidth{\leftmargini}
\addtolength\labelwidth{-\labelsep}
\@beginparpenalty -\@lowpenalty
\@endparpenalty   -\@lowpenalty
\@itempenalty     -\@lowpenalty
\renewcommand\theenumi{\@arabic\c@enumi}
\renewcommand\theenumii{\@alph\c@enumii}
\renewcommand\theenumiii{\@roman\c@enumiii}
\renewcommand\theenumiv{\@Alph\c@enumiv}
\newcommand\labelenumi{\upshape\theenumi.}%%%\theenumi.
\newcommand\labelenumii{\upshape(\theenumii)}%%%(\theenumii)
\newcommand\labelenumiii{\upshape\theenumiii.}%%%\theenumiii.
\newcommand\labelenumiv{\upshape\theenumiv.}%%%\theenumiv.
\renewcommand\p@enumii{\theenumi}
\renewcommand\p@enumiii{\theenumi(\theenumii)}
\renewcommand\p@enumiv{\p@enumiii\theenumiii}
\newcommand\labelitemi{\smallbullet}%%%\textbullet
\newcommand\labelitemii{\normalfont\bfseries \textendash}
\newcommand\labelitemiii{\textasteriskcentered}
\newcommand\labelitemiv{\textperiodcentered}
\newenvironment{description}
               {\list{}{\labelwidth\z@ \itemindent-\leftmargin
                        \let\makelabel\descriptionlabel}}
               {\endlist}
\newcommand*\descriptionlabel[1]{\hspace\labelsep
                                \normalfont\bfseries #1}

\newenvironment{abstract}{%
              \small
         \narrower\narrower\noindent
        {\bfseries \abstractname.\vspace{\z@}}}

\newenvironment{verse}
               {\let\\\@centercr
                \list{}{\itemsep      \z@
                        \itemindent   -1.5em%
                        \listparindent\itemindent
                        \rightmargin  \leftmargin
                        \advance\leftmargin 1.5em}%
                \item\relax}
               {\endlist}
\newenvironment{quotation}
               {\list{}{\listparindent 1.5em%
                        \itemindent    \listparindent
                        \rightmargin   \leftmargin
                        \parsep        \z@ \@plus\p@}%
                \item\relax}
               {\endlist}
\newenvironment{quote}
               {\list{}{\rightmargin\leftmargin}%
                \item\relax}
               {\endlist}
\if@compatibility
\newenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\z@
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
    }
\else
\newenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\@ne
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
     \if@twoside\else
        \setcounter{page}\@ne
     \fi
    }
\fi
\newcommand\appendix{\par
  \setcounter{section}{0}%
  \setcounter{subsection}{0}%
  \gdef\thesection{\@Alph\c@section}}
\setlength\arraycolsep{5\p@}
\setlength\tabcolsep{6\p@}
\setlength\arrayrulewidth{.4\p@}
\setlength\doublerulesep{2\p@}
\setlength\tabbingsep{\labelsep}
\skip\@mpfootins = \skip\footins
\setlength\fboxsep{3\p@}
\setlength\fboxrule{.4\p@}
\renewcommand \theequation {\@arabic\c@equation}
\newcounter{figure}
\renewcommand \thefigure {\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename\nobreakspace\thefigure}
\newenvironment{figure}
               {\@float{figure}}
               {\end@float}
\newenvironment{figure*}
               {\@dblfloat{figure}}
               {\end@dblfloat}
\newcounter{table}
\renewcommand\thetable{\@arabic\c@table}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename\nobreakspace\thetable}
\newenvironment{table}
               {\@float{table}}
               {\end@float}
\newenvironment{table*}
               {\@dblfloat{table}}
               {\end@dblfloat}
\newlength\abovecaptionskip
\newlength\belowcaptionskip
\setlength\abovecaptionskip{10\p@}
\setlength\belowcaptionskip{0\p@}
\long\def\@makecaption#1#2{%
  \vskip\abovecaptionskip
  \sbox\@tempboxa{\small #1: #2}%%%{#1: #2}
  \ifdim \wd\@tempboxa >\hsize
    #1: #2\par
  \else
    \global \@minipagefalse
    \hb@xt@\hsize{\hfil\box\@tempboxa\hfil}%
  \fi
  \vskip\belowcaptionskip}
\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*\mit{\@fontswitch\relax\mathnormal}
\newcommand\@pnumwidth{1.55em}
\newcommand\@tocrmarg{2.55em}
\newcommand\@dotsep{4.5}
\setcounter{tocdepth}{3}
\newcommand\tableofcontents{%
    \section*{\contentsname
        \@mkboth{%
           \MakeUppercase\contentsname}{\MakeUppercase\contentsname}}%
    \@starttoc{toc}%
    }
\newcommand*\l@part[2]{%
  \ifnum \c@tocdepth >-2\relax
    \addpenalty\@secpenalty
    \addvspace{2.25em \@plus\p@}%
    \setlength\@tempdima{3em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      {\leavevmode
       \large \bfseries #1\hfil \hb@xt@\@pnumwidth{\hss #2}}\par
       \nobreak
       \if@compatibility
         \global\@nobreaktrue
         \everypar{\global\@nobreakfalse\everypar{}}%
      \fi
    \endgroup
  \fi}
\newcommand*\l@section[2]{%
  \ifnum \c@tocdepth >\z@
    \addpenalty\@secpenalty
    \addvspace{1.0em \@plus\p@}%
    \setlength\@tempdima{1.5em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      \leavevmode \bfseries
      \advance\leftskip\@tempdima
      \hskip -\leftskip
      #1\nobreak\hfil \nobreak\hb@xt@\@pnumwidth{\hss #2}\par
    \endgroup
  \fi}
\newcommand*\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\newcommand*\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\newcommand*\l@paragraph{\@dottedtocline{4}{7.0em}{4.1em}}
\newcommand*\l@subparagraph{\@dottedtocline{5}{10em}{5em}}
\newcommand\listoffigures{%
    \section*{\listfigurename}%
      \@mkboth{\MakeUppercase\listfigurename}%
              {\MakeUppercase\listfigurename}%
    \@starttoc{lof}%
    }
\newcommand*\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\newcommand\listoftables{%
    \section*{\listtablename}%
      \@mkboth{%
          \MakeUppercase\listtablename}%
         {\MakeUppercase\listtablename}%
    \@starttoc{lot}%
    }
\let\l@table\l@figure
\newdimen\bibindent
\setlength\bibindent{1.5em}

%%%%%%% RMI - bibliography commands %%%%
\newcommand{\RMIauthor}[1]{{\sc #1:}} %% RMI-dor
\newcommand{\RMIpaper}[1]{{\rm #1.}} %% RMI-dor
\newcommand{\RMIbook}[1]{{\sl #1.}} %% RMI-dor
\newcommand{\RMIjournal}[1]{{\sl #1}} %% RMI-dor
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newenvironment{thebibliography}[1]
     {\section*{\refname}%
      \@mkboth{\MakeUppercase\refname}{\MakeUppercase\refname}%
      \small%%%
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy
      \clubpenalty4000
      \@clubpenalty \clubpenalty
      \widowpenalty4000%
      \sfcode`\.\@m}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}
\newcommand\newblock{\hskip .11em\@plus.33em\@minus.07em}
\let\@openbib@code\@empty
\newenvironment{theindex}
               {\if@twocolumn
                  \@restonecolfalse
                \else
                  \@restonecoltrue
                \fi
                \twocolumn[\section*{\indexname}]%
                \@mkboth{\MakeUppercase\indexname}%
                        {\MakeUppercase\indexname}%
                \thispagestyle{plain}\parindent\z@
                \parskip\z@ \@plus .3\p@\relax
                \columnseprule \z@
                \columnsep 35\p@
                \let\item\@idxitem}
               {\if@restonecol\onecolumn\else\clearpage\fi}
\newcommand\@idxitem{\par\hangindent 40\p@}
\newcommand\subitem{\@idxitem \hspace*{20\p@}}
\newcommand\subsubitem{\@idxitem \hspace*{30\p@}}
\newcommand\indexspace{\par \vskip 10\p@ \@plus5\p@ \@minus3\p@\relax}
\renewcommand\footnoterule{%
  \kern-3\p@
  \hrule\@width.4\columnwidth
  \kern2.6\p@}
\newcommand\@makefntext[1]{%
    \parindent 1em%
    \noindent
    \hb@xt@1.8em{\hss\@makefnmark}#1}
\newcommand\contentsname{Contents}
\newcommand\listfigurename{List of Figures}
\newcommand\listtablename{List of Tables}
\newcommand\refname{References}
\newcommand\indexname{Index}
\newcommand\figurename{Figure}
\newcommand\tablename{Table}
\newcommand\partname{Part}
\newcommand\appendixname{Appendix}
\newcommand\abstractname{Abstract}
\newcommand\keywordname{Keywords}%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand\classificationname{Mathematics Subject Classification \rm (2010)}%%%%%%%%
\def\today{\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
\setlength\columnsep{10\p@}
\setlength\columnseprule{0\p@}
\pagestyle{plain}
\pagenumbering{arabic}
\if@twoside
\else
  \raggedbottom
\fi
\if@twocolumn
  \twocolumn
  \sloppy
  \flushbottom
\else
  \onecolumn
\fi
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% This is file `amsthm.sty'[2009/07/02 v2.20.1]
%\let\@xp=\expandafter
%\let\@nx=\noexpand
%\def\@oparg#1[#2]{\@ifnextchar[{#1}{#1[#2]}}
%\long\def\@ifempty#1{\@xifempty#1@@..\@nil}
%\long\def\@xifempty#1#2@#3#4#5\@nil{%
%  \ifx#3#4\@xp\@firstoftwo\else\@xp\@secondoftwo\fi}
%\long\def\@ifnotempty#1{\@ifempty{#1}{}}
%\def\setboxz@h{\setbox\z@\hbox}
%\def\@addpunct#1{%
%  \relax\ifhmode
%    \ifnum\spacefactor>\@m \else#1\fi
%  \fi}
%\def\nopunct{\spacefactor 1007 }
%\def\frenchspacing{\sfcode`\.1006\sfcode`\?1005\sfcode`\!1004%
%  \sfcode`\:1003\sfcode`\;1002\sfcode`\,1001 }
%\DeclareOption*{\input{\CurrentOption .thm}}
%\ProcessOptions
%
%\newcommand{\theoremstyle}[1]{%
%  \@ifundefined{th@#1}{%
%    \PackageWarning{amsthm}{Unknown theoremstyle `#1'}%
%    \thm@style{plain}%
%  }{%
%    \thm@style{#1}%
%  }%
%}
%\newskip\toppsep%%%%
%\toppsep 10\p@ \@plus2\p@ \@minus4\p@%%%%
%\newtoks\thm@style
%\thm@style{plain}
%\newtoks\thm@bodyfont  \thm@bodyfont{\itshape}
%\newtoks\thm@headfont  \thm@headfont{\bfseries}
%\newtoks\thm@notefont  \thm@notefont{}
%\newtoks\thm@headpunct \thm@headpunct{.}
%\newskip\thm@preskip \newskip\thm@postskip
%\def\thm@space@setup{%
%   \thm@preskip=\toppsep \thm@postskip=\thm@preskip%%%\thm@preskip=\topsep \thm@postskip=\thm@preskip
%}
%\renewcommand{\newtheorem}{\@ifstar{\@xnthm *}{\@xnthm \relax}}
%\def\@xnthm#1#2{%
%  \let\@tempa\relax
%  \@xp\@ifdefinable\csname #2\endcsname{%
%    \global\@xp\let\csname end#2\endcsname\@endtheorem
%    \ifx *#1% unnumbered, need to get one more mandatory arg
%      \edef\@tempa##1{%
%        \gdef\@xp\@nx\csname#2\endcsname{%
%          \@nx\@thm{\@xp\@nx\csname th@\the\thm@style\endcsname}%
%            {}{##1}}}%
%    \else % numbered theorem, need to check for optional arg
%      \def\@tempa{\@oparg{\@ynthm{#2}}[]}%
%    \fi
%  }%
%  \@tempa
%}
%\def\@ynthm#1[#2]#3{%
%  \ifx\relax#2\relax
%    \def\@tempa{\@oparg{\@xthm{#1}{#3}}[]}%
%  \else
%    \@ifundefined{c@#2}{%
%      \def\@tempa{\@nocounterr{#2}}%
%    }{%
%      \@xp\xdef\csname the#1\endcsname{\@xp\@nx\csname the#2\endcsname}%
%      \toks@{#3}%
%      \@xp\xdef\csname#1\endcsname{%
%        \@nx\@thm{%
%          \let\@nx\thm@swap
%            \if S\thm@swap\@nx\@firstoftwo\else\@nx\@gobble\fi
%          \@xp\@nx\csname th@\the\thm@style\endcsname}%
%            {#2}{\the\toks@}}%
%      \let\@tempa\relax
%    }%
%  \fi
%  \@tempa
%}
%\def\@xthm#1#2[#3]{%
%  \ifx\relax#3\relax
%    \newcounter{#1}%
%  \else
%    \newcounter{#1}[#3]%
%    \@xp\xdef\csname the#1\endcsname{\@xp\@nx\csname the#3\endcsname
%      \@thmcountersep\@thmcounter{#1}}%
%  \fi
%  \toks@{#2}%
%  \@xp\xdef\csname#1\endcsname{%
%    \@nx\@thm{%
%      \let\@nx\thm@swap
%        \if S\thm@swap\@nx\@firstoftwo\else\@nx\@gobble\fi
%      \@xp\@nx\csname th@\the\thm@style\endcsname}%
%      {#1}{\the\toks@}}%
%}
%\def\@thm#1#2#3{%
%  \ifhmode\unskip\unskip\par\fi
%  \normalfont
%  \trivlist
%  \let\thmheadnl\relax
%  \let\thm@swap\@gobble
%  \thm@notefont{\fontseries\mddefault\upshape}%
%  \thm@headpunct{.}% add period after heading
%  \thm@headsep 5\p@ plus\p@ minus\p@\relax
%  \thm@space@setup
%  #1% style overrides
%  \@topsep \thm@preskip               % used by thm head
%  \@topsepadd \thm@postskip           % used by \@endparenv
%  \def\@tempa{#2}\ifx\@empty\@tempa
%    \def\@tempa{\@oparg{\@begintheorem{#3}{}}[]}%
%  \else
%    \refstepcounter{#2}%
%    \def\@tempa{\@oparg{\@begintheorem{#3}{\csname the#2\endcsname}}[]}%
%  \fi
%  \@tempa
%}
%\def\@restorelabelsep{\relax}
%\let\@ythm\relax
%\let\thmname\@iden \let\thmnote\@iden \let\thmnumber\@iden
%\providecommand\@upn{\textup}
%\def\thmhead@plain#1#2#3{%
%  \thmname{#1}\thmnumber{\@ifnotempty{#1}{ }\@upn{#2}}%
%  \thmnote{ \the\thm@notefont(#3)}}%%%{ {\the\thm@notefont(#3)}}}
%\let\thmhead\thmhead@plain
%\def\swappedhead#1#2#3{%
%  \thmnumber{#2}%
%  \thmname{\@ifnotempty{#2}{~}#1}%
%  \thmnote{ \the\thm@notefont(#3)}}%%%{ {\the\thm@notefont(#3)}}}
%\let\swappedhead@plain=\swappedhead
%\let\thmheadnl\relax
%\let\thm@indent\noindent
%\let\thm@swap\@gobble
%\def\@begintheorem#1#2[#3]{%
%  \deferred@thm@head{\the\thm@headfont \thm@indent
%    \@ifempty{#1}{\let\thmname\@gobble}{\let\thmname\@iden}%
%    \@ifempty{#2}{\let\thmnumber\@gobble}{\let\thmnumber\@iden}%
%    \@ifempty{#3}{\let\thmnote\@gobble}{\let\thmnote\@iden}%
%    \thm@swap\swappedhead\thmhead{#1}{#2}{#3}%
%    \the\thm@headpunct
%    \thmheadnl % possibly a newline.
%    \hskip\thm@headsep
%  }%
%  \ignorespaces}
%\newskip\thm@headsep
%\thm@headsep=5pt plus1pt minus1pt\relax
%\let\adjust@parskip@nobreak=\@nbitem
%\newtoks\dth@everypar
%\dth@everypar={%
%  \@minipagefalse \global\@newlistfalse
%  \@noparitemfalse
%  \if@inlabel
%    \global\@inlabelfalse
%    \begingroup \setbox\z@\lastbox
%     \ifvoid\z@ \kern-\itemindent \fi
%    \endgroup
%    \unhbox\@labels
%  \fi
%  \if@nobreak \@nobreakfalse \clubpenalty\@M
%  \else \clubpenalty\@clubpenalty \everypar{}%
%  \fi
%}%
%\def\deferred@thm@head#1{%
%  \if@inlabel \indent \par \fi % eject a section head if one is pending
%  \if@nobreak
%    \adjust@parskip@nobreak
%  \else
%    \addpenalty\@beginparpenalty
%    \addvspace\@topsep
%    \addvspace{-\parskip}%
%  \fi
%  \global\@inlabeltrue
%  \everypar\dth@everypar
%  \sbox\@labels{\normalfont#1}%
%  \ignorespaces
%}
%\def\nonslanted{\relax
%  \@xp\let\@xp\@tempa\csname\f@shape shape\endcsname
%  \ifx\@tempa\itshape\upshape
%  \else\ifx\@tempa\slshape\upshape\fi\fi}
%\def\swapnumbers{\edef\thm@swap{\if S\thm@swap N\else S\fi}}
%\def\thm@swap{N}%
%\let\@opargbegintheorem\relax
%\def\th@plain{%
%%%  \let\thm@indent\noindent % no indent
%%%  \thm@headfont{\bfseries}% heading font is bold
%%%  \thm@notefont{}% same as heading font
%%%  \thm@headpunct{.}% add period after heading
%%%  \let\thm@swap\@gobble
%%%  \thm@preskip\topsep
%%%  \thm@postskip\theorempreskipamount
%  \itshape % body font
%}
%\def\th@definition{%
%  \normalfont % body font
%}
%\def\th@remark{%
%  \thm@headfont{\itshape}%
%  \normalfont % body font
%  \thm@preskip\topsep \divide\thm@preskip\tw@
%  \thm@postskip\thm@preskip
%}
%\def\@endtheorem{\endtrivlist\@endpefalse }
%\newcommand{\newtheoremstyle}[9]{%
%  \@ifempty{#5}{\dimen@\z@skip}{\dimen@#5\relax}%
%  \ifdim\dimen@=\z@
%    \toks@{#4\let\thm@indent\noindent}%
%  \else
%    \toks@{#4\def\thm@indent{\noindent\hbox to#5{}}}%
%  \fi
%  \def\@tempa{#8}\ifx\space\@tempa
%    \toks@\@xp{\the\toks@ \thm@headsep\fontdimen\tw@\font\relax}%
%  \else
%    \def\@tempb{\newline}%
%    \ifx\@tempb\@tempa
%      \toks@\@xp{\the\toks@ \thm@headsep\z@skip
%        \def\thmheadnl{\newline}}%
%    \else
%      \toks@\@xp{\the\toks@ \thm@headsep#8\relax}%
%    \fi
%  \fi
%  \begingroup
%  \thm@space@setup
%  \@defaultunits\@tempskipa#2\thm@preskip\relax\@nnil
%  \@defaultunits\@tempskipb#3\thm@postskip\relax\@nnil
%  \xdef\@gtempa{\thm@preskip\the\@tempskipa
%    \thm@postskip\the\@tempskipb\relax}%
%  \endgroup
%  \@temptokena\@xp{\@gtempa
%    \thm@headfont{#6}\thm@headpunct{#7}%
%  }%
%  \@ifempty{#9}{%
%    \let\thmhead\thmhead@plain
%  }{%
%    \@namedef{thmhead@#1}##1##2##3{#9}%
%    \@temptokena\@xp{\the\@temptokena
%      \@xp\let\@xp\thmhead\csname thmhead@#1\endcsname}%
%  }%
%  \@xp\xdef\csname th@#1\endcsname{\the\toks@ \the\@temptokena}%
%}
%
%\DeclareRobustCommand{\qed}{%
%  \ifmmode \mathqed
%  \else
%    \leavevmode\unskip\penalty9999 \hbox{}\nobreak\hfill
%    \quad\hbox{\qedsymbol}%
%  \fi
%}
%\let\QED@stack\@empty
%\let\qed@elt\relax
%\newcommand{\pushQED}[1]{%
%  \toks@{\qed@elt{#1}}\@temptokena\expandafter{\QED@stack}%
%  \xdef\QED@stack{\the\toks@\the\@temptokena}%
%}
%\newcommand{\popQED}{%
%  \begingroup\let\qed@elt\popQED@elt \QED@stack\relax\relax\endgroup
%}
%\def\popQED@elt#1#2\relax{#1\gdef\QED@stack{#2}}
%\newcommand{\qedhere}{%
%  \begingroup \let\mathqed\math@qedhere
%    \let\qed@elt\setQED@elt \QED@stack\relax\relax \endgroup
%}
%
%\newcommand{\hideqed}{\renewcommand{\qed}{}} %%% EMS
%
%\newif\ifmeasuring@
%\newif\iffirstchoice@ \firstchoice@true
%\def\setQED@elt#1#2\relax{%
%  \ifmeasuring@
%  \else \iffirstchoice@ \gdef\QED@stack{\qed@elt{}#2}\fi
%  \fi
%  #1%
%}
%\def\qed@warning{%
%  \PackageWarning{amsthm}{The \@nx\qedhere command may not work
%    correctly here}%
%}
%\newcommand{\mathqed}{\quad\hbox{\qedsymbol}}
%\def\linebox@qed{\hfil\hbox{\qedsymbol}\hfilneg}
%\@ifpackageloaded{amsmath}{%
%  \def\math@qedhere{%
%    \@ifundefined{\@currenvir @qed}{%
%      \qed@warning\quad\hbox{\qedsymbol}%
%    }{%
%      \@xp\aftergroup\csname\@currenvir @qed\endcsname
%    }%
%  }
%  \def\displaymath@qed{%
%    \relax
%    \ifmmode
%      \ifinner \aftergroup\linebox@qed
%      \else
%        \eqno
%        \let\eqno\relax \let\leqno\relax \let\veqno\relax
%        \hbox{\qedsymbol}%
%      \fi
%    \else
%       \aftergroup\linebox@qed
%    \fi
%  }
%  \@xp\let\csname equation*@qed\endcsname\displaymath@qed
%  \def\equation@qed{%
%    \iftagsleft@
%      \hbox{\phantom{\quad\qedsymbol}}%
%      \gdef\alt@tag{%
%        \rlap{\hbox to\displaywidth{\hfil\qedsymbol}}%
%        \global\let\alt@tag\@empty
%      }%
%    \else
%      \gdef\alt@tag{%
%        \global\let\alt@tag\@empty
%        \vtop{\ialign{\hfil####\cr
%                \tagform@\theequation\cr
%                \qedsymbol\cr}}%
%        \setbox\z@
%      }%
%    \fi
%  }
%  \def\qed@tag{%
%    \global\tag@true \nonumber
%    &\omit\setboxz@h {\strut@ \qedsymbol}\tagsleft@false
%    \place@tag@gather
%    \kern-\tabskip
%    \ifst@rred \else \global\@eqnswtrue \fi \global\advance\row@\@ne \cr
%  }
%  \def\split@qed{%
%    \def\endsplit{\crcr\egroup \egroup \ctagsplit@false \rendsplit@
%      \aftergroup\align@qed
%    }%
%  }
%  \def\align@qed{%
%    \ifmeasuring@ \tag*{\qedsymbol}%
%    \else \let\math@cr@@@\qed@tag
%    \fi
%  }
%  \@xp\let\csname align*@qed\endcsname\align@qed
%  \@xp\let\csname gather*@qed\endcsname\align@qed
%%% Needs some patching up for amsmath 1.2
%}{% end of amsmath branch, start plain LaTeX branch
%  \def\math@qedhere{%
%    \@ifundefined{\@currenvir @qed}{%
%      \qed@warning \aftergroup\displaymath@qed
%    }{%
%      \@xp\aftergroup\csname\@currenvir @qed\endcsname
%    }%
%  }
%  \def\displaymath@qed{%
%    \relax
%    \ifmmode
%      \ifinner \aftergroup\aftergroup\aftergroup\linebox@qed
%      \else
%        \eqno \def\@badmath{$$}%
%        \let\eqno\relax \let\leqno\relax \let\veqno\relax
%        \hbox{\qedsymbol}%
%      \fi
%    \else
%       \aftergroup\linebox@qed
%    \fi
%  }
%  \@ifundefined{ver@leqno.clo}{%
%    \def\equation@qed{\displaymath@qed \quad}%
%  }{%
%    \def\equation@qed{\displaymath@qed}%
%  }
%  \def\@tempa#1$#2#3\@nil{%
%    \def\[{#1$#2\def\@currenvir{displaymath}#3}%
%  }%
%  \expandafter\@tempa\[\@nil
%}
%\@ifpackageloaded{amstex}{%
%  \def\@tempa{TT}%
%}{%
%  \@ifpackageloaded{amsmath}{%
%    \def\@tempb#1 v#2.#3\@nil{#2}%
%    \ifnum\@xp\@xp\@xp\@tempb\csname ver@amsmath.sty\endcsname v0.0\@nil
%       <\tw@
%      \def\@tempa{TT}%
%    \else
%      \def\@tempa{TF}%
%    \fi
%  }{%
%    \def\@tempa{TF}
%  }%
%}
%\if\@tempa
%  \renewcommand{\math@qedhere}{\quad\hbox{\qedsymbol}}%
%\fi
%\newcommand{\openbox}{\leavevmode
%  \hbox to.77778em{%
%  \hfil\vrule
%  \vbox to.675em{\hrule width.6em\vfil\hrule}%
%  \vrule\hfil}}
%\DeclareRobustCommand{\textsquare}{%
%  \begingroup \usefont{U}{msa}{m}{n}\thr@@\endgroup
%}
%\providecommand{\qedsymbol}{\openbox}
%\newenvironment{proof}[1][\proofname]{\par
%  \pushQED{\qed}%
%  \normalfont \topsep6\p@\@plus6\p@\relax
%  \trivlist
%  \item[\hskip\labelsep
%        \itshape
%    #1\@addpunct{.}]\ignorespaces
%}{%
%  \popQED\endtrivlist\@endpefalse
%}
%\providecommand{\proofname}{Proof}
%%% End of file `amsthm.sty'.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%
%% fancyhdr %%
%%%%%%%%%%%%%%

%\ProvidesPackage{fancyhdr}
\let\fancy@def\gdef

\def\if@mpty#1#2#3{\def\temp@ty{#1}\ifx\@empty\temp@ty #2\else#3\fi}

\def\@forc#1#2#3{\expandafter\f@rc\expandafter#1\expandafter{#2}{#3}}
\def\f@rc#1#2#3{\def\temp@ty{#2}\ifx\@empty\temp@ty\else
                                    \f@@rc#1#2\f@@rc{#3}\fi}
\def\f@@rc#1#2#3\f@@rc#4{\def#1{#2}#4\f@rc#1{#3}{#4}}

\newcommand{\f@nfor}[3]{\edef\@fortmp{#2}%
    \expandafter\@forloop#2,\@nil,\@nil\@@#1{#3}}

\newcommand\def@ult[3]{%
    \edef\temp@a{\lowercase{\edef\noexpand\temp@a{#3}}}\temp@a
    \def#1{}%
    \@forc\tmpf@ra{#2}%
        {\expandafter\if@in\tmpf@ra\temp@a{\edef#1{#1\tmpf@ra}}{}}%
    \ifx\@empty#1\def#1{#2}\fi}

\newcommand{\if@in}[4]{%
    \edef\temp@a{#2}\def\temp@b##1#1##2\temp@b{\def\temp@b{##1}}%
    \expandafter\temp@b#2#1\temp@b\ifx\temp@a\temp@b #4\else #3\fi}

\newcommand{\fancyhead}{\@ifnextchar[{\f@ncyhf h}{\f@ncyhf h[]}}
\newcommand{\fancyfoot}{\@ifnextchar[{\f@ncyhf f}{\f@ncyhf f[]}}
\newcommand{\fancyhf}{\@ifnextchar[{\f@ncyhf {}}{\f@ncyhf {}[]}}

\def\f@ncyhf#1[#2]#3{%
    \def\temp@c{}%
    \@forc\tmpf@ra{#2}%
        {\expandafter\if@in\tmpf@ra{eolcrhf,EOLCRHF}%
            {}{\edef\temp@c{\temp@c\tmpf@ra}}}%
    \ifx\@empty\temp@c\else
        \ifx\PackageError\undefined
        \errmessage{Illegal char `\temp@c' in fancyhdr argument:
          [#2]}\else
        \PackageError{Fancyhdr}{Illegal char `\temp@c' in fancyhdr argument:
          [#2]}{}\fi
    \fi
    \f@nfor\temp@c{#2}%
        {\def@ult\f@@@eo{eo}\temp@c
         \def@ult\f@@@lcr{lcr}\temp@c
         \def@ult\f@@@hf{hf}{#1\temp@c}%
         \@forc\f@@eo\f@@@eo
             {\@forc\f@@lcr\f@@@lcr
                 {\@forc\f@@hf\f@@@hf
                     {\expandafter\fancy@def\csname
                      f@ncy\f@@eo\f@@lcr\f@@hf\endcsname
                      {#3}}}}}}

\newcommand{\lhead}{\@ifnextchar[{\@xlhead}{\@ylhead}}
\def\@xlhead[#1]#2{\fancy@def\f@ncyelh{#1}\fancy@def\f@ncyolh{#2}}
\def\@ylhead#1{\fancy@def\f@ncyelh{#1}\fancy@def\f@ncyolh{#1}}

\newcommand{\chead}{\@ifnextchar[{\@xchead}{\@ychead}}
\def\@xchead[#1]#2{\fancy@def\f@ncyech{#1}\fancy@def\f@ncyoch{#2}}
\def\@ychead#1{\fancy@def\f@ncyech{#1}\fancy@def\f@ncyoch{#1}}

\newcommand{\rhead}{\@ifnextchar[{\@xrhead}{\@yrhead}}
\def\@xrhead[#1]#2{\fancy@def\f@ncyerh{#1}\fancy@def\f@ncyorh{#2}}
\def\@yrhead#1{\fancy@def\f@ncyerh{#1}\fancy@def\f@ncyorh{#1}}

\newcommand{\lfoot}{\@ifnextchar[{\@xlfoot}{\@ylfoot}}
\def\@xlfoot[#1]#2{\fancy@def\f@ncyelf{#1}\fancy@def\f@ncyolf{#2}}
\def\@ylfoot#1{\fancy@def\f@ncyelf{#1}\fancy@def\f@ncyolf{#1}}

\newcommand{\cfoot}{\@ifnextchar[{\@xcfoot}{\@ycfoot}}
\def\@xcfoot[#1]#2{\fancy@def\f@ncyecf{#1}\fancy@def\f@ncyocf{#2}}
\def\@ycfoot#1{\fancy@def\f@ncyecf{#1}\fancy@def\f@ncyocf{#1}}

\newcommand{\rfoot}{\@ifnextchar[{\@xrfoot}{\@yrfoot}}
\def\@xrfoot[#1]#2{\fancy@def\f@ncyerf{#1}\fancy@def\f@ncyorf{#2}}
\def\@yrfoot#1{\fancy@def\f@ncyerf{#1}\fancy@def\f@ncyorf{#1}}


\newdimen\headwidth
\newcommand{\headrulewidth}{0.4pt}
\newcommand{\footrulewidth}{\z@skip}
\newcommand{\footruleskip}{.3\normalbaselineskip}


\newif\if@fancyplain \@fancyplainfalse
\def\fancyplain#1#2{\if@fancyplain#1\else#2\fi}

\headwidth=-123456789sp %magic constant

\def\fancy@reset{\restorecr
 \def\baselinestretch{1}%
 \def\nouppercase##1{{\let\uppercase\relax\let\MakeUppercase\relax
     \expandafter\let\csname MakeUppercase \endcsname\relax##1}}%
 \ifx\undefined\@newbaseline% NFSS not present; 2.09 or 2e
   \ifx\@normalsize\undefined \normalsize % for ucthesis.cls
   \else \@normalsize \fi
 \else% NFSS (2.09) present
  \@newbaseline%
 \fi}

\fancyhf{}


\def\@fancyhead#1#2#3#4#5{#1\hbox to\headwidth{\fancy@reset\vbox{\vspace*{5.8pt}\hbox
{\rlap{\parbox[b]{\headwidth}{\raggedright#2\strut}}\hfill
\parbox[b]{\headwidth}{\centering#3\strut}\hfill
\llap{\parbox[b]{\headwidth}{\raggedleft#4\strut}}}\headrule}}#5}

\def\@fancyfoot#1#2#3#4#5{#1\hbox to\headwidth{\fancy@reset\vbox{\footrule
\hbox{\rlap{\parbox[t]{\headwidth}{\raggedright#2\strut}}\hfill
\parbox[t]{\headwidth}{\centering#3\strut}\hfill
\llap{\parbox[t]{\headwidth}{\raggedleft#4\strut}}}}}#5}

\def\headrule{}

\def\footrule{{\if@fancyplain\let\footrulewidth\plainfootrulewidth\fi
\vskip-\footruleskip\vskip-\footrulewidth
\hrule\@width\headwidth\@height\footrulewidth\vskip\footruleskip}}


\def\ps@fancy{%
\@ifundefined{@chapapp}{\let\@chapapp\chaptername}{}%for amsbook
\@ifundefined{MakeUppercase}{\def\MakeUppercase{\uppercase}}{}%
\@ifundefined{chapter}{\def\sectionmark##1{\markboth
{\MakeUppercase{\ifnum \c@secnumdepth>\z@
 \thesection\hskip 1em\relax \fi ##1}}{}}%
\def\subsectionmark##1{\markright {\ifnum \c@secnumdepth >\@ne
 \thesubsection\hskip 1em\relax \fi ##1}}}%
{\def\chaptermark##1{\markboth {\MakeUppercase{\ifnum \c@secnumdepth>\m@ne
 \@chapapp\ \thechapter. \ \fi ##1}}{}}%
\def\sectionmark##1{\markright{\MakeUppercase{\ifnum \c@secnumdepth >\z@
 \thesection. \ \fi ##1}}}}%
\ps@@fancy
\gdef\ps@fancy{\@fancyplainfalse\ps@@fancy}%
\ifdim\headwidth<0sp
    \global\advance\headwidth123456789sp\global\advance\headwidth\textwidth
\fi}
\def\ps@fancyplain{\ps@fancy \let\ps@plain\ps@plain@fancy}
\def\ps@plain@fancy{\@fancyplaintrue\ps@@fancy}
\let\ps@@empty\ps@empty
\def\ps@@fancy{%
\ps@@empty % This is for amsbook/amsart, which do strange things with \topskip
\def\@mkboth{\protect\markboth}%
\def\@oddhead{\@fancyhead\@lodd\f@ncyolh\f@ncyoch\f@ncyorh\@rodd}%
\def\@oddfoot{\@fancyfoot\@lodd\f@ncyolf\f@ncyocf\f@ncyorf\@rodd}%
\def\@evenhead{\@fancyhead\@rodd\f@ncyelh\f@ncyech\f@ncyerh\@lodd}%
\def\@evenfoot{\@fancyfoot\@rodd\f@ncyelf\f@ncyecf\f@ncyerf\@lodd}%
}
\def\@lodd{\if@reversemargin\hss\else\relax\fi}
\def\@rodd{\if@reversemargin\relax\else\hss\fi}

\newif\iffootnote
\let\latex@makecol\@makecol
\def\@makecol{\ifvoid\footins\footnotetrue\else\footnotefalse\fi
\let\topfloat\@toplist\let\botfloat\@botlist\latex@makecol}
\def\iftopfloat#1#2{\ifx\topfloat\empty #2\else #1\fi}
\def\ifbotfloat#1#2{\ifx\botfloat\empty #2\else #1\fi}
\def\iffloatpage#1#2{\if@fcolmade #1\else #2\fi}


%%%%%%%%%%%%%%%
%%%% load some packages%%%%%%
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{latexsym}
\RequirePackage{ifthen}
\RequirePackage{graphicx}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% define block environment as short for trivlist
 \newenvironment{block}{\begin{trivlist}\item{}}{\end{trivlist}}

% define commands for the last page
\newcommand{\@received}{\noindent Use \texttt{\textbackslash received\{1
  January, 2000\}} before \textbackslash
  begin\{document\}\par}
\newcommand{\received}[2][]{\renewcommand{\@received}{\begin{block}\small
      Received #2%
      \ifthenelse{\equal{#1}{}}{}{; revised #1}\\ \end{block}}}
\newlength{\@textwidthminusparindent}
\newlength{\@saveparindent}
\let\@address=\empty

\newcommand{\address}[2][]{
  \expandafter\gdef\expandafter\@address\expandafter{%
    \@address
  \setlength{\@textwidthminusparindent}{\textwidth}
  \setlength{\@saveparindent}{\parindent}
  \addtolength{\@textwidthminusparindent}{-\parindent}
  \small
  \begin{block}%\hspace{\parindent}%
    \begin{minipage}{\@textwidthminusparindent}%
     \setlength{\parindent}{\@saveparindent}%
      \noindent%\hspace*{-\parindent}%
      {#2}\ifthenelse{\equal{#1}{}}{}{\\[1pt] E-mail: \tt
  \email{#1}}
    \end{minipage}
  \end{block}\mbox{} \smallskip}}

% provide command to set end matter
\newcommand{\makelastpage}{
  \ifx\empty\@address
  \address{Address ??}
  \fi
  \medskip\@received%\smallskip
  \ifx\empty\@address\empty\noindent
  Use \texttt{\textbackslash address[peter@mail]\{Peter Smith, York\} before
  \textbackslash begin\{document\}}
  \par
  \else\@address\fi}

\let\s@bsubsection=\subsubsection
\newcommand{\c@mdsuba}[2][]{\s@bsubsection[#1]{#2.}}
\newcommand{\c@mdsubb}[1]{\s@bsubsection*{#1.}}
\renewcommand{\subsubsection}{\secdef\c@mdsuba\c@mdsubb}

\let\s@bsectionx=\subsectionx
\newcommand{\c@mdx}[2][]{\s@bsection[#1]{#2}}
\newcommand{\c@mdy}[1]{\s@bsection*{#1}}

\let\s@bsubsectionx=\subsubsectionx
\newcommand{\c@mdu}[2][]{\s@bsubbsection[#1]{#2}}
\newcommand{\c@mdv}[1]{\s@bsubsection*{#1}}


% provide commands \author, \title
% for the headings and the titlepage
% and provide default values to hint user
\pagestyle{myheadings}
\renewcommand{\@author}{}
\renewcommand{\@title}{}

\newcommand{\@authorhead}{}
\newcommand{\@titlehead}{}
\renewcommand{\author}[2][no@ption]{
  \renewcommand{\@author}{#2}
  \ifthenelse{\equal{#1}{no@ption}}{
    \renewcommand{\@authorhead}{#2}}{
    \renewcommand{\@authorhead}{#1}}
  \markboth{\@authorhead}{\@titlehead}}
\renewcommand{\title}[2][no@ption]{
  \renewcommand{\@title}{\boldmath{}#2}
  \ifthenelse{\equal{#1}{no@ption}}{
    \renewcommand{\@titlehead}{#2}}{
    \renewcommand{\@titlehead}{#1}}
  \markboth{\@authorhead}{\@titlehead}}

% set quotations and references in textup
% original commands are still accesible with
% \origcite, \origref, \origpageref and \origeqref
\let\origcite=\cite
\renewcommand{\cite}[2][no@ption]
{\ifthenelse{\equal{#1}{no@ption}}
  {\textup{\origcite{#2}}}
  {\textup{\origcite[#1]{#2}}}}
\let\origref=\ref
\renewcommand{\ref}[1]{\textup{\origref{#1}}}
\let\origpageref=\pageref
\renewcommand{\pageref}[1]{\textup{\origpageref{#1}}}
%\renewcommand{\eqref}[1]{\textup{(\origref{#1})}}

\let\origdocument\document
\def\document{\origdocument\maketitle}
\let\endorigdocument\enddocument
\def\enddocument{\makelastpage\endorigdocument}

\newcommand{\cprime}{'} % for AMS bibliography
\newcommand{\tagsleft}{\tagsleft@true}
\newcommand{\tagsright}{\tagsleft@false}
\newcommand{\smallbullet}{\protect\raisebox{1.5pt}{\scriptsize$\,\bullet\,$}}

\renewcommand{\@seccntformat}[1]{{\csname the#1\endcsname.}\hspace{.5em}}

\def\captionx{\refstepcounter\@captype \@dblarg{\@captionx\@captype}}

\long\def\@captionx#1[#2]#3{\par\addcontentsline{\csname
  ext@#1\endcsname}{#1}{\protect\numberline{\csname
  the#1\endcsname}{\ignorespaces #2}}\begingroup
    \@parboxrestore
    \normalsize
    \@makecaptionx{\csname fnum@#1\endcsname}{\ignorespaces #3}\par
  \endgroup}

\newlength\abovecaptionxskip
\newlength\belowcaptionxskip
\setlength\abovecaptionxskip{10\p@}
\setlength\belowcaptionxskip{0\p@}
\long\def\@makecaptionx#1#2{%
  \vskip\abovecaptionxskip
  \sbox\@tempboxa{\small#1.  #2}%%%{#1:  #2}
  \ifdim \wd\@tempboxa >\hsize
    \small#1.  #2\par%%%#1: #2\par
  \else
    \global \@minipagefalse
    \hb@xt@\hsize{\hfil\box\@tempboxa\hfil}%
  \fi
  \vskip\belowcaptionxskip}

\renewcommand\l@section{\@dottedtocline{1}{0em}{1.4em}}

\def\myfnsymbol#1{\expandafter\@myfnsymbol\csname c@#1\endcsname}

\def\@myfnsymbol#1{\ensuremath{\ifcase#1\or 1\or 2\or 3\or
   4\or \mathparagraph\or \|\or **\or \dagger\dagger
   \or \ddagger\ddagger \else\@ctrerr\fi}}

%%%%%%%%%%%%%%%%%%%%%%
%%%% RMI-commands %%%%
%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\projects}[1]{\def\thefootnote{}\footnote{#1}
\addtocounter{footnote}{-1}
\def\thefootnote{\arabic{footnote}}}
%%

%%%%%%%%%%%%
%% Header %%
%%%%%%%%%%%%

\RequirePackage{lastpage}

\received{??}

\newcounter{initialpage}
\setcounter{initialpage}{1}
\newcommand{\setinitialpage}[1]{\setcounter{initialpage}{#1}}
\gdef\initialpage{\@arabic\c@initialpage}


\def\email#1{\href{mailto:#1}{#1}}

\def\@DOI{??}
\def\DOI#1{\def\@DOI{#1}}

\def\@RMIvol{1}
\def\RMIvol#1{\def\@RMIvol{#1}}

\def\@RMIyear{2010}
\def\RMIyear#1{\def\@RMIyear{#1}}

\def\@RMIissue{1}
\def\RMIissue#1{\def\@RMIissue{#1}}


\def\RMIdata#1#2#3#4#5{\RMIvol{#1}\RMIyear{#2}\DOI{#3}\received{#4}\setinitialpage{#5}}

\newcommand{\lastpage}{\pageref{LastPage}}
\newcommand{\finalpage}{\lastpage}
\def\setfinalpage#1{\def\finalpage{#1}}


\lfoot{} \rfoot{} \cfoot{}

\rhead{\hfill\rm\small{\footnotesize\copyright} European Mathematical Society}
    

\lhead{\small \textit{Submitted to} Rev.~Mat.~Iberoam., {\initialpage}--{\finalpage}}

\chead{}
\AtBeginDocument{\setcounter{page}{\value{initialpage}}}
%%%%%%%typesetting area
\textwidth=357pt
\textheight=548pt


%%% Un par de entornos \'{u}tiles
\newcommand{\arriba}[1]{\mbox{}\vspace{-#1pt}\mbox{}}

%%% Para las figuras
\newcounter{lafigura}
\def\thelafigura{\arabic{lafigura}}
\newenvironment{figura}[2]{\refstepcounter{lafigura}\begin{center}
{#1}
\end{center}
\begin{quote}
{\small\textsc{Figure
\thelafigura}: #2}
\end{quote}}{}

\endinput
%% End of file `RMI4.cls'.
