%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Recommended by the ACM ppl
\usepackage{booktabs}
\usepackage{subfigure}
\usepackage{wrapfig}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our packages
\usepackage{amsmath}
\usepackage{xcolor}
\usepackage{booktabs}
\usepackage{qtree}

\usepackage{graphicx}
\usepackage{tikz}
\usepackage{pgfplots}
\usetikzlibrary{positioning}
\usetikzlibrary{calc}
\usetikzlibrary{plotmarks}
\usetikzlibrary{fit}
\usetikzlibrary{shapes}

%% Cleveref must be the last loaded package
%% since it modifies the cross-ref system.
\usepackage{cleveref}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our defs

%% More space between rows
\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%% Logistic Stuff

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
 {\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}
}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\victor}[2][nolabel]{%
 {\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}%
}
\newcommand{\msm}[2][nolabel]{%
 {\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Mark: } #2 \textbf{$]$}}%
}

%% LaTeX stuff

\newenvironment{myhs}{\vspace{0.10cm}\par\noindent\begin{minipage}{\textwidth}\small}{\end{minipage}\vspace{0.10cm}}

\def\dotminus{\mathbin{\ooalign{\hss\raise1ex\hbox{.}\hss\cr
  \mathsurround=0pt$-$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% lhs2TeX Formatting Rules
%%
%% Comment out to use lhs2TeX default formatting.
%%
%include stylish.lhs
%%

% Easy to typeset Haskell types using the 
% commands from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

%% Here's a number of handy commands for adding dashes to words
%% The proper construction was sugested by Guy Steele, thanks Guy!
\newcommand{\textdash}{-{\hskip-0.3em}-}
\newcommand{\wdw}[2]{\hbox{\it #1\textdash{}#2}}
\newcommand{\wdwdw}[3]{\hbox{\it #1\textdash{}#2\textdash{}#3}}
\newcommand{\wdwdwdw}[4]{\hbox{\it #1\textdash{}#2\textdash{}#3\textdash{}#4}}

%%% Datatype Promotion
%format (P (a)) = "\HS{''}" a
%% Special case for promoting (:)
%format PCons   = "\HS{''\!\!:}"

%%% Usefull Notation
%format dots    = "\HS{\dots}"
%format forall  = "\HS{\forall}"
%format lambda  = "\HS{\lambda}"
%format alpha   = "\HS{\alpha}"
%format valpha  = "\HS{v\alpha}"
%format valpha'
%format dot     = "\HS{.}"
%format ^=      = "\HS{\bumpeq}"
%format :       = "\HS{\mathrel{:}}"


%format Nat         = "\HT{\mathbb{N}}"
%format MINUS       = "\HT{\mathbin{\dotminus}}"
%format TIMES       = "\HT{\mathbin{\times}}"

%%% Notation for this paper

%format b0        = "\HV{b_0}"
%format b1        = "\HV{b_1}"
%format b2        = "\HV{b_2}"
%format b3        = "\HV{b_3}"
%format b4        = "\HV{b_4}"
%format b5        = "\HV{b_5}"
%format b6        = "\HV{b_6}"
%format q0        = "\HV{q_0}"
%format q1        = "\HV{q_1}"
%format q2        = "\HV{q_2}"
%format q3        = "\HV{q_3}"
%format q4        = "\HV{q_4}"
%format q5        = "\HV{q_5}"
%format q6        = "\HV{q_6}"
%format p0        = "\HV{p_0}"
%format p1        = "\HV{p_1}"
%format r0        = "\HV{r_0}"
%format r1        = "\HV{r_1}"
%format r2        = "\HV{r_2}"

%format Set1      = "\HV{Set_1}"

%format Honest    = "\HSPostulate{Honest}"
%format lemmaB1   = "\HSPostulate{\wdw{lemma}{B1}}"
%format inQC      = "\HT{\mathbin{\!\in_{\mathit{QC}}\!}}"
%format inRC      = "\HT{\mathbin{\!\in_{\mathit{RC}}\!}}"
%format inRCD     = "\HT{\_\!\in_{\mathit{RC}}\!\_}"
%format exists (a) b = "\HT{\exists[}" a "\HT{]}\;" b

%% Macro to generate this: "adwddyyPwwdw"aPf{;wdw"aP

%format lemmaS11       = "\HV{\wdw{lemmaS1}{1}}"
%format lemmaS12       = "\HV{\wdw{lemmaS1}{2}}"
%format lemmaS13       = "\HV{\wdw{lemmaS1}{3}}"
%format isInPool       = "\HV{\mathit{isInPool}}"
%format mkInitial      = "\HV{\mathit{mkInitial}}"
%format bAuthor        = "\HV{\mathit{bAuthor}}"
%format bCommand       = "\HV{\mathit{bCommand}}"
%format bPrevQCHash    = "\HV{\mathit{bPrevQCHash}}"
%format bRound         = "\HV{\mathit{bRound}}"
%format vAuthor        = "\HV{\mathit{vAuthor}}"
%format vBlockHash     = "\HV{\mathit{vBlockHash}}"
%format vRound         = "\HV{\mathit{vRound}}"
%format qAuthor        = "\HV{\mathit{qAuthor}}"
%format qBlockHash     = "\HV{\mathit{qBlockHash}}"
%format qRound         = "\HV{\mathit{qRound}}"
%format qVotes         = "\HV{\mathit{qVotes}}"
%format qVotesC1       = "\HV{\wdw{qVotes}{C1}}"
%format qVotesC2       = "\HV{\wdw{qVotes}{C2}}"
%format qVotesC3       = "\HV{\wdw{qVotes}{C3}}"
%format qVotesC4       = "\HV{\wdw{qVotes}{C4}}"
%format seed           = "\HV{\mathit{seed}}"
%format authorsN       = "\HV{\mathit{authorsN}}"
%format isBFT          = "\HV{\mathit{isBFT}}"
%format epochId        = "\HV{\mathit{epochId}}"
%format RecordChain    = "\HT{\mathit{RecordChain}}"
%format HashBroke      = "\HT{\mathit{HashBroke}}"
%format Valid          = "\HT{\mathit{Valid}}"
%format IsInPool       = "\HT{\mathit{IsInPool}}"
%format ValidBlockInit = "\HT{\mathit{ValidBlockInit}}"
%format ValicBlockStep = "\HT{\mathit{ValicBlockStep}}"
%format ValidQC        = "\HT{\mathit{ValidQC}}"
%format BlockHash      = "\HT{\mathit{BlockHash}}"
%format QC             = "\HT{\mathit{QC}}"
%format Vote           = "\HT{\mathit{Vote}}"
%format Block          = "\HT{\mathit{Block}}"
%format EpochId        = "\HT{\mathit{EpochId}}"
%format EpochConfig    = "\HT{\mathit{EpochConfig}}"

%format SafeRSS        = "\HT{\mathit{SafeRSS}}"

%format incrround      = "\HT{\wdw{incr}{round}}"
%format votesonce      = "\HT{\wdw{votes}{once}}"
%format lockedround    = "\HT{\wdw{locked}{round}}"
%format kchaincontig   = "\HT{\wdw{Kchain}{contig}}"



%format IEXTB          = "\HT{I\!\!\leftarrow\!\!B}"
%format QEXTB          = "\HT{Q\!\!\leftarrow\!\!B}"
%format BEXTQ          = "\HT{B\!\!\leftarrow\!\!Q}"
%format EXT            = "\HT{\leftarrow}"
%format EXTTR          = "\HT{\leftarrow^{\star}}"
%format EXTD           = "\HT{\_\leftarrow\_}"
%format EXTTRD         = "\HT{\_\leftarrow^{\star}\_}"
