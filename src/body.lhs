\section{Introduction}

\victor{Loose sentences follow; might even be wrong, sorry!}

  In this paper we discuss an Agda model of LibraBFT~\cite{Baudet2019} safety properties.
Our model is heavily based on the original paper's \emph{proof of safety}. The main
goal is to machine check the original author's proof that the set of all commits
seen by an honest node form a linear chain. In other words, the commit rule
is safe: no two blocks that match the commit rule will depend on conflicting pasts.

The LibraBFT is a pratical implementation of the \emph{HotStuff}~\cite{Yin2019} consensus
protocol.

\section{Abstract LibraBFT}

  In this section we go over the core constructions needed to
encode LibraBFT in Agda. We start with a small description
of how to work with hash functions in Agda, then \victor{...}
This sets the stage for our proofs~\Cref{sec:proof}.

\victor{I use the word ``chain'' later; would be good to give an idea of
what it means here}

\victor{
The model:
\begin{itemize}
  \item The idea is to encode a state transition system;
  \item Prove the properties as invariants of this system.
\end{itemize}
}

\subsection{Epochs and Records and their Laws}

  In LibraBFT, time is divided in \emph{epochs}. Each epoch
has a configuration which dictates who is allowed to participate in consensus
for that epoch. The BFT assumptions states that the number of authors
in an epoch must always be greater than $3f$, where $f$ is the amount
of byzantine failures we want to withstand.

\begin{myhs}
\begin{code}
EpochId : Set
EpochId = Nat

record EpochConfig (f : Nat) : Set where
  field
    epochId   : EpochId
    authorsN  : Nat
    isBFT     : suc (3 * f) <= authorsN

    seed      : Nat

  QuorumSize  : Nat
  QuorumSize  = authorsN MINUS f
\end{code}
\end{myhs}

  During an epoch the protocol is run in \emph{rounds}.  In each
round, one node is designated \emph{leader} and is responsible for
receiving and propagating requests from clients. Leaders are selected
deterministically from the current |EpochId| and round number.  The
set of nodes allowed to participate in a given epoch is fixed and
specified by the epoch configuration. We use a finite type for this
purpose.

\begin{myhs}
\begin{code}
Author : forall {f} -> EpochConfig f -> Set
Author ec = Fin (authorsN ec)
\end{code}
\end{myhs}

\victor{postulate BFT assumption or finally prove it!}

  A typical round of the LibraBFT protocol consists the leader
broadcasting a new \emph{block} to the participants. Each other node
will then verify whether the aforementioned block is valid and, when
that is the case, cast a vote.  When the leader receives enough votes,
it issues a \emph{quorum certificate} and broadcasts this
certificate. This certifies that the block which it refers has been
verified and concludes the round.  On the next round, another node
will be the leader and the process is repeated.

\victor{illustrate this stuff!}

  The nodes participating in consensus maintain a pool of
\emph{records} which can be abstracted by a type supporting
a predicate that indicates whether a record belonds in
the pool, as shown with |isRecordStoreState| below.
We require the |isInPool| predicate to be proof irrelevant for
technical reasons: we will be storing inhabitants of |isInPool|
on some auxiliary proof objects throughout our model and
we must be able to rewrite them freely. 
\victor{more info on it? I don't wanna get too technical too fast}


%format isInPoolirrelevant = "\HV{\wdw{isInPool}{irrelevant}}"
\begin{myhs}
\begin{code}
  record isRecordStoreState {a}(RSS : Set a) : Set (suc a) where
    constructor rss
    field
      isInPool            : Record -> Set
      isInPoolirrelevant  : forall {r}(p0 p1 : isInPool r) -> p0 == p1
\end{code}
\end{myhs}

  This pool of records is logically organized a tree rooted in
the initial record. The edges of the tree indicate that a record
\emph{extends} another. Naturally, records are only allowed to
extend records that are either in the pool or are the initial record.
This \emph{extends} relation is written |EXTD| and illustrated in
\Cref{fig:recordstorestate}.

\begin{figure}
\resizebox{.8\textwidth}{!}{%
\begin{tikzpicture}[txt/.style={scale=1.6}]
\node [txt] (hinit) {|hi|};
\node [txt, right = of hinit] (b0) {|b0|};
\node [txt, right = of b0]   (q0) {|q0|};
\node [txt, right = of q0]   (b1) {|b1|};
\node [txt, right = of b1]   (q1) {|q1|};
\node [txt, above = of b1]   (b2) {|b2|};
\node [txt, right = of b2]   (q2) {|q2|};
\node [txt, right = of q1]   (b3) {|b3|};
\node [txt, right = of b3]   (q3) {|q3|};
\node [txt, below = of b3]   (b4) {|b4|};
\node [txt, right = of b4]   (q4) {|q4|};
\node [txt, right = of q3]   (b5) {|b5|};
\node [txt, right = of b5]   (q5) {|q5|};
\node [txt, right = of q4]   (b6) {|b6|};
\node [txt, right = of b6]   (q6) {|q6|};

\draw[->] (q6) -- (b6);
\draw[->] (b6) -- (q4);
\draw[->] (q4) -- (b4);
\draw[->] (b4) to[in=270 , out=180] (q1);
\draw[->] (q5) -- (b5);
\draw[->] (b5) -- (q3);
\draw[->] (q3) -- (b3);
\draw[->] (b3) -- (q1);
\draw[->] (q1) -- (b1);
\draw[->] (b1) -- (q0);
\draw[->] (q0) -- (b0);
\draw[->] (b0) -- (hinit);
\draw[->] (q2) -- (b2);
\draw[->] (b2) to[in=90 , out=180] (q0);

\node (box) [fit=(b0) (q2) (q6) , draw , dashed, rounded corners=2mm] {};
\node at (box.north) [scale = 1.6, above, inner sep=1mm] 
  {\textit{Record Pool}}; 

\draw [dotted] (hinit.south) -- ($ (q1.south) - (0.5,0) $)
               to[out=270, in=180] (b4.north) -- (q6.north);
\node at (b6.north) [scale = 1.6, above , inner sep=1mm] {\textit{RecordChain}};

\end{tikzpicture}}
\caption{A abstract record store state, inside the dashed box, 
with its records ordered as a tree. A |RecordChain q6| is shown in a 
dotted line. Records have their rounds as a subscript}
\label{fig:recordstorestate}
\end{figure}


Whenever a node receives a certified block --- a block
followed by a quorum certificate for it -- it adds it
to its pool extending one of the tree of blocks. 
A path in this tree is denoted a \emph{chain}
and consists of blocks alternating with quorum certificates.
These are denoted in the original paper~\cite{Baudet2019}
by: $B_0 \leftarrow Q_0 \leftarrow B_1 \cdots$.
The |Record| datatype encapsulates the different kinds of
records. We will discuss the $\_\leftarrow\_$ relation shortly.

\begin{myhs}
\begin{code}
data Record : Set where
    I  : Initial -> Record
    B  : Block   -> Record
    Q  : QC      -> Record
\end{code}
\end{myhs}

  These different records correspond to network messages that
have already had their signatures, author and format checked.
Naturally, each of those contains specific data. \Cref{fig:records-def} shows
the complete definition. We record the fact that a record
has been created by a valid author by parametrizing everything
by an epoch config and taking authors directly from there.

  \victor{sloppy para; fix this}
  Although there are four different messages that nodes exchange throughout the
execution of LibraBFT --- blocks, votes, quorum certificates,
and timeouts --- we did not consider timeouts in our first model for they
pose no issue to safety \victor{why?}.  

\begin{figure}
\begin{myhs}
\begin{code}
data Initial : Set where
  mkInitial : Initial

module _ {f : Nat}(ec : EpochConfig f) where
record Block : Set where
  constructor mkBlock
  field
    bAuthor     : Author ec
    bCommand    : Command
    bPrevQCHash : QCHash
    bRound      : Round

record Vote : Set where
  constructor mkVote
  field
    vAuthor    : Author ec
    vBlockHash : BlockHash
    vRound     : Round

record QC : Set where
 field
   qAuthor        : Author ec
   qBlockHash     : BlockHash
   qRound         : Round
   qVotes         : List Vote
\end{code}
\end{myhs}
\caption{Record Definitions}
\label{fig:records-defs}
\end{figure}

  The type of record chains is the central datatype in our development.
We seek to verify (in a machine-checkable manner) that the LibraBFT
protocol provides the safety guarantees their authors claim. These
safety guarantees culminate in lemma S6~\cite{Baudet2019}, which states
that blocks considered commited belong all to the \emph{same chain}.
That is, there is only one path from the root of the tree of records
that is extended through commits.

  A |RecordChain|, defined below, is essentially just a path in the tree. Differently
from the original work~\cite{Baudet2019}, where the authors denote any
path by \emph{chain}, we require these to extended explicitely all
the way to the root of the tree, represented by the initial record, |I|.
There is a fairly technical reason for this: we must only consider records
that belong in the record pool, i.e., have been received with a valid signature,
to take part in a chain. \victor{Shall we add that in the original paper
they imply this?} The |IsInPool : Record -> Set| is kept abstract throughout the
abstract model. We will come back to it in \Cref{sec:concrete-model-template}, for now,
we can think of a static, immutable pool of records we can use to construct
our chain. An inhabitant of |IsInPool r| indicates that |r| belongs to this pool.

\begin{myhs}
\begin{code}
data RecordChain : Record -> Set where
  empty  : forall {hi} -> RecordChain (I hi)
  step   : forall {r r'}
         -> (rc : RecordChain r) 
         -> r EXT r'
         -> Valid rc r' 
         -> {prf : IsInPool r'} 
         -> RecordChain r'
\end{code}
\end{myhs}

\victor{This makes me wonder... why do we even have |EXTD| and not
just add the hashing contraints to |Valid|?}

  Looking into |RecordChain| above we see that a record |r'| can only
be appended into a chain that ends in |r| iff |r EXT r'| and
|r'| is \emph{valid} with respect to said chain. The |EXTD| relation is concerned 
with hashes, ensuring the \emph{previous hash} field of |r'| matches the
hash of |r|. The |Valid| predicate, on the other hand, is concerned with 
ensuring that the rounds increase correctly. It is defined in a |mutual|
block together with |RecordChain|. 

\begin{myhs}
\begin{code}
data Valid : {r : Record} -> RecordChain r -> Record -> Set where
  ValidBlockInit : {b : Block}{hi : Initial} 
                 -> 1 <= bRound b -> Valid (empty {hi}) (B b)
  ValidBlockStep : {b : Block}{q : QC}
                 -> (rc : RecordChain (Q q))
                 -> qRound (qBase q) < bRound b
                 -> Valid rc (B b)
  ValidQC        : {q : QC} {b : Block}
                 -> (rc : RecordChain (B b))
                 -> qRound (qBase q) == bRound b
                 -> Valid rc (Q q)
\end{code}
\end{myhs}

  \victor{Still need more on chains and $k$-chains and the commit rule}
  
\subsubsection{Voting Constraints}

  The LibraBFT protocol imposes two restrictions on which blocks
an honest participant is allowed to vote for. These restrictions are
in place to guarantee the safety of the commit rule. The first 
voting contraint is the \emph{increasing-round} constraint
and is presented in the original work~\cite{Baudet2019} as:

\begin{quote}
An honest node that voted once for a block |b| in the past may only vote for |b'|
if |round b < round b'|
\end{quote}

  At this point, we have modeled a snapshot of a local honest participant's
state at a single point in time, with the objective of verifying that
having enough honest participants following the LibraBFT protocol
implies the safety of the commit rule. Yet, the \emph{increasing-round} constraint
poses a modeling challenge. Any attempt to naively encode this constraint in a model of
a single local |RecordChain| will fail. The reason being the informal use
of temporal modalities such as ``has voted'' and ``may only vote'' (in the future).
Squinting at the \emph{increasing-round} constraint, though, we see that 
it imposes an order on the votes an honest participant may cast. We proceed
to add a |vOrder : Nat| field to the |Vote| record to make this explicit.

  With an explicit |vOrder| field, the task of encoding the \emph{increasing-round}
constraint becomes much simpler. It states that if an honest participant |alpha|
has voted for two blocks, the round of this blocks is proportional to the
order in which |alpha| voted:

\victor{this is more subtle than that... this is parametrized
by a record store state and such; I'm unsure on how to tie this knot pedagogically
at this moment}
\begin{myhs}
\begin{code}
IncreasingRoundRule : Set1
IncreasingRoundRule 
   = (alpha : Author ec) → Honest alpha
   -> forall {q q'}(va  : alpha inQC q)(va' : alpha inQC q') -- alpha has voted for q and q'
   -> vOrder (inQCVote q va) < vOrder (inQCVote q' va')
   -> qRound (qBase q) < qRound (qBase q')
\end{code}
\end{myhs}

  There are different mechanisms one could think of ensuring the relationship
between |vOrder| and rounds. One example is to actually change the protocol and include
|vOrder| directly in the network messages. This would enable honest participants
to keep a tally and detect dishonest participants breaking this rule,
increasing the accountability of the system. Translating |vOrder| to an actual
implementation of LibraBFT is out of the scope of this paper, but we argue it
is the observational consequence of the \emph{increasing-round} constraint
and a realistic assumption to add to our abstract model.



\subsection{Dealing with Cryptographic Hash Functions}

  We assume the existence of a cryptographic hash function throughout
our development. To capture this assumption, we use a module
parameter on the relevant modules: |hash : ByteString -> Hash|,
where |ByteString| is a list of booleans and |Hash| is an abstract datatype.
As is standard practice with hash functions, our reasoning here works modulo
hash collisions. To encode that, we borrow the techniques from Miraldo et al.~\cite{Miraldo2019},
where a hash collision is evidenced by the |HashBroke| datatype:

\begin{myhs}
\begin{code}
HashBroke : Set
HashBroke = exists (x , y) (Collision hash x y)

Collision : {A B : Set}(f : A -> B)(a1 a2 : A) -> Set
Collision f a1 a2 = a1 /= a2 TIMES f a1 == f a2
\end{code}
\end{myhs}

  Collision resistance of |hash| can be assumed via another module
parameter of type |CR hash|, defined below. This assumption provides
us with an injectivity principle for our abstract |hash| function that
works as expected: if the hash of two objects is the same, either the
objects are the same or we found a hash collision.

\begin{myhs}
\begin{code}
CR : (ByteString -> Hash) -> Set
CR hash = forall {x y} -> hash x == hash y -> Either (Collision hash x y) (x == y)
\end{code}
\end{myhs}

