\section{Introduction}

\victor{Loose sentences follow; might even be wrong, sorry!}

  In this paper we discuss an Agda model of LibraBFT~\cite{Baudet2019} safety properties.
Our model is heavily based on the original paper's \emph{proof of safety}. The main
goal is to machine check the original author's proof that the set of all commits
seen by an honest node form a linear chain. In other words, the commit rule
is safe: no two blocks that match the commit rule will depend on conflicting pasts.

The LibraBFT is a pratical implementation of the \emph{HotStuff}~\cite{Yin2019} consensus
protocol.



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

\section{The Model}

  Before delving into the components of LibraBFT and how they were
encoded in our model, it is worth looking at the high level architecture.
A node participating in the LibraBFT network sends and receives messages
and consequently, transition its internal state, first from $s_0$ to $s_1$, then to $s_2$ and
so on and so forth. A concrete model, proving that an imlementation of the protocol
is correct, that is, all the possible states we can reach will satisfy certain safety 
properties -- committed entries never conflict (\Cref{thm:s5}) -- would proceed by
of proving that the state transitions preserve the LibraBFT invariants. These
invariants are provided by, and proven to guarantee \Cref{thm:s5}, by the
abstract model, \Cref{sec:abstract-librabft}.

\subsection{Abstract LibraBFT}
\label{sec:abstract-librabft}

  In this section we go over the core constructions needed to
encode the LibraBFT invariants and prove that they imply
the necessary safety properties. 

\subsection{Epochs and Records}

  In LibraBFT, time is divided in \emph{epochs}. Each epoch
has a configuration which dictates who is allowed to participate in consensus
for that epoch. The BFT assumptions states that the overall number of authors
in an epoch must always be greater than $3f$, where $f$ is the amount
of byzantine failures we wish to withstand.

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

  The properties we wish to prove often mention ``an honest
author'', hence, we must bring the notion of \emph{honest} into our model. 
Given that we must not be able to inspect who is honest or not, we
encode this as a postuate. Nevertheless, there are points in the proofs
that we must use the existence of an honest author. This can be estailished
by the classic BFT lemma, also wirten as a postulate here. 
The classic BFT lemma states that for every two quorums of nodes,
that is, a subset of nodes whose combined voting power is at least
|QuorumSize|, there exists at least one honest node that belongs to
both quorums. Our |lemmaB1| below encodes the BFT assumption --- a |QC|
denotes a quorum certificate and |a inQC q| indicates |a|
has voted in |q|, as we shall see shortly.

\begin{myhs}
\begin{code}
postulate
  Honest   : forall {f}{ec : EpochConfig ec} -> Author ec -> Set
  lemmaB1  : (q1 q2 : QC) -> exists (a) (a inQC q1 TIMES a inQC q2 TIMES Honest a)
\end{code}
\end{myhs}

\victor{I feel we might need more info on honest nodes vs dishonest ones; 
For that though, I need to find a better mental model}

\begin{figure}
\victor{finish this figure!}
\centering
\resizebox{.8\textwidth}{!}{%
\begin{tikzpicture}
\node (node1) {$\mathit{node}_1$};
\node [below = .3cm of node1] (node2) {$\mathit{node}_2$};
\node [below = .3cm of node2] (node3) {$\mathit{node}_3$};
\node [below = .3cm of node3] (node4) {$\mathit{node}_4$};
\node [right = .5cm of node1] (e11) {};
\node [right = .5cm of node2] (e12) {};
\node [right = .5cm of node3] (e13) {};
\node [right = .5cm of node4] (e14) {};
\node [right = 1cm of e11] (e21) {};
\node [right = 1cm of e12] (e22) {};
\node [right = 1cm of e13] (e23) {};
\node [right = 1cm of e14] (e24) {};
\node [right = 1cm of e21] (e31) {};
\node [right = 1cm of e22] (e32) {};
\node [right = 1cm of e23] (e33) {};
\node [right = 1cm of e24] (e34) {};
\node [right = 1cm of e31] (e41) {};
\node [right = 1cm of e32] (e42) {};
\node [right = 1cm of e33] (e43) {};
\node [right = 1cm of e34] (e44) {};
\node [right = 1cm of e41] (e51) {};
\node [right = 1cm of e42] (e52) {};
\node [right = 1cm of e43] (e53) {};
\node [right = 1cm of e44] (e54) {};
\node [right = 1cm of e51] (e61) {};
\node [right = 1cm of e52] (e62) {};
\node [right = 1cm of e53] (e63) {};
\node [right = 1cm of e54] (e64) {};
\node [right = 1cm of e61] (e71) {};
\node [right = 1cm of e62] (e72) {};
\node [right = 1cm of e63] (e73) {};
\node [right = 1cm of e64] (e74) {};

\draw[-] (node1.east) -- ($ (e71) + (1,0) $);
\draw[-] (node2.east) -- ($ (e72) + (1,0) $);
\draw[-] (node3.east) -- ($ (e73) + (1,0) $);
\draw[-] (node4.east) -- ($ (e74) + (1,0) $);

\draw[->] (e12) -- (e21);
\draw[->] (e12) -- (e23);
\draw[->] (e12) -- (e24);
\draw[->] (e21) -- (e32);
\draw[->] (e23) -- (e32);
\draw[->] (e24) -- (e32);
\draw[->] (e32) -- (e41.west);
\draw[->] (e32) -- (e43.west);
\draw[->] (e32) -- (e44.west);

\draw[->] (e44.east) -- (e51);
\draw[->] (e44.east) -- (e52);
\draw[->] (e44.east) -- (e53);
\draw[->] (e51) -- (e64);
\draw[->] (e52) -- (e64);
\draw[->] (e53) -- (e64);
\draw[->] (e64) -- (e71);
\draw[->] (e64) -- (e72);
\draw[->] (e64) -- (e73);

\draw[dashed] ($ (e11) + (-.1,1) $)
          --  ($ (e14) + (-.1,-1) $);

\draw[dashed] ($ (e41) + (0,1) $)
           -- ($ (e44) - (0,1) $);

\draw[dashed] ($ (e71) + (0,1) $)
           -- ($ (e74) - (0,1) $);

\node at ($ (e14)!0.5!(e44) - (0,1) $) {$\mathit{round}\;n$};
\node at ($ (e44)!0.5!(e74) - (0,1) $) {$\mathit{round}\;(n+1)$};
\end{tikzpicture}}
\caption{Simplified overview of the consecutive rounds of LibraBFT
after round synchorinization has settled.}
\label{fig:librabft-simplified-execution}
\end{figure}

  A typical round of LibraBFT, illustrated in
\Cref{fig:librabft-simplified-execution}, consists in the leader
broadcasting a new \emph{block} to the other notes. Each other node
will then verify whether the aforementioned block is valid and, when
that is the case, cast a vote.  When the leader receives enough votes,
it issues a \emph{quorum certificate}, which consists in a set of votes, and broadcasts this
certificate. This certifies that the block which it refers has been
verified and concludes the round.  On the next round, another node
will be the determined leader and the process is repeated. 

  The nodes participating in consensus maintain a pool of
\emph{records}. How this pool is implemented is uninportant,
hence, we abstract it by a type supporting
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
\centering
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


Whenever a node receives a certified block -- a block
followed by a valid quorum certificate -- it adds it
to its pool extending one of leaves of the tree of blocks. 
A path in this tree is denoted a \emph{chain}
and consists of blocks alternating with quorum certificates.
These are denoted in the original paper~\cite{Baudet2019}
by: $B_0 \leftarrow Q_0 \leftarrow B_1 \cdots$.
The |Record| datatype encapsulates the different kinds of
records, which is required to provide a homogeneous treatment of $\_\leftarrow\_$.

\begin{myhs}
\begin{code}
data Record : Set where
  I  : Initial  -> Record
  B  : Block    -> Record
  Q  : QC       -> Record
\end{code}
\end{myhs}

  These different records correspond to network messages that
have already had their signatures, author and format checked.
Naturally, each of those contains specific data.
We record the fact that a record
has been created by a valid author by parametrizing everything
by an epoch config and taking authors directly from there. 
We also store the necessary checks to ensure that a quorum certificate is valid,
namely: (1) no duplicate votes are present; (2) we have at least |QuorumSize ec|
votes; (3) all votes vote for the same block and (4) all votes happened on the same
round. All the records can be seen in \Cref{fig:record-defs}.
\victor{It is curious we do not use the properties in |QC| anywhere in the
development, isn't it?} \victor{We do! I found c3 and c4 already} The original paper~\cite{Baudet2019} also defines timeouts
as a record. We did not consider timeouts in our first model for they pose no issue
to safety. They are simply a mechanism to prevent a dishonest leader to stop progress.
\victor{more on timeouts?}

\begin{figure}
\begin{myhs}
\begin{code}
data Initial : Set where
  mkInitial : Initial

module _ {f : Nat}(ec : EpochConfig f) where
  record Block : Set where
    constructor mkBlock
    field
      bAuthor       : Author ec
      bCommand      : Command
      bPrevQCHash   : QCHash
      bRound        : Round

  record Vote : Set where
    constructor mkVote
    field
      vAuthor       : Author ec
      vBlockHash    : BlockHash
      vRound        : Round

  record QC : Set where
   field
     qAuthor        : Author ec
     qBlockHash     : BlockHash
     qRound         : Round
     qVotes         : List Vote
     qVotesC1       : IsSorted (\ v0 v1 -> vAuthor v0 <Fin vAuthor v1) qVotes
     qVotesC2       : QuorumSize ec <= length qVotes
     qVotesC3       : All (\ v -> vBlockHash v == qBlockHash qBase)  qVotes
     qVotesC4       : All (\ v -> vRound v == qRound qBase)          qVotes
\end{code}
\end{myhs}
\caption{Record Definitions}
\label{fig:record-defs}
\end{figure}

\subsection{Record Chains and the Commit Rule}

  Record chains have already been informally introduced, for 
example, in \Cref{fig:recordstorestate}.  A
record chain into a record |r| is a path from the initial record into
|r| through the tree of records that nodes keep locally. Naturally,
one can only use valid records to build these chains. In this section
we explore what does it mean for a record to be valid and how we
encoded this in Agda. In fact, the type of record chains is the
central datatype in our development.  The main property we want to
verify (in a machine-checkable manner) that the LibraBFT protocol
provides the safety guarantees that culminate in lemma
S6~\cite{Baudet2019}, which states that blocks considered commited
belong all to the \emph{same chain}.  That is, there is only one path
from the root of the tree of records that is extended through commits.
In other words, all new commits will take into account the same
previously commited history.

  A value of type |RecordChain r| is a proof that we can build a path from
the initial record into |r|, using only the records in a given record store state.
The dependency on a given record store state is important: one must not conjure
records to satisfy dependencies while proving theorems. The |RecordChain| datatype
will then be parametrized by an arbitrary record store state and contain two
constructors. One representing the empty chain, and another representing
a chain that contains at least one valid record on its tail.
 
\begin{myhs}
\begin{code}
module _ (RSS : Set)(isRSS : isRecordStoreState RSS) where
  data RecordChain  : Record -> Set where
    empty  : forall {hi} -> RecordChain (I hi)
    step   : forall {r r'}(rc : RecordChain r) 
           -> r EXT r'
           -> ValidRound rc r' 
           -> {prf : isInPool isRSS r'} 
           -> RecordChain r'
\end{code}
\end{myhs}

\victor{This makes me wonder... why do we even have |EXTD| and not
just add the hashing contraints to |Valid|?}

  Validity of records is estabilished in two steps. The |ValidRound| datatype
makes sure that the round annotated within the record is consistent with 
the rest of the chain whereas |EXTD| makes sure the previous hash field of
the record matches the hash of the record it is extending. The |ValidRound|
datatype must actually be declared as mutually recursive with |RecordChain|
because of its first constructor, otherwise we would never be able to
extend the empty |RecordChain|.

\begin{myhs}
\begin{code}
module _ (RSS : Set)(isRSS : isRecordStoreState RSS) where
  data ValidRound : {r : Record} -> RecordChain r -> Record -> Set where
    ValidBlockInit  : {b : Block}{hi : Initial} 
                    -> 1 <= bRound b -> ValidRound (empty {hi}) (B b)
    ValidBlockStep  : {b : Block}{q : QC}(rc : RecordChain (Q q))
                    -> qRound q < bRound b -> ValidRound rc (B b)
    ValidQC         : {q : QC} {b : Block}(rc : RecordChain (B b))
                    -> qRound q == bRound b -> ValidRound rc (Q q)
\end{code}
\end{myhs}

  The |EXTD| relation is standalone from record chains as it only enforces
that the hash of the previous record matches the \emph{previous hash} field
of the next. The |EXTTRD| type is the reflexive-transitive closure of |EXT|.

\begin{myhs}
\begin{code}
data EXTD : Record -> Record -> Set where
  IEXTB  : {i : Initial} {b : Block}
         -> HashR (I i) ==  bPrevQCHash b
         -> I i EXT B b
  QEXTB  : {q : QC} {b : Block}
         -> HashR (Q q) ==  bPrevQCHash b
         -> Q q EXT B b
  BEXTQ  : {b : Block} {q : QC}
         -> HashR (B b) ==  qBlockHash q
         -> B b EXT Q q

data EXTTRD (r0 : Record) : Record -> Set where
  ssRefl  : r0 EXTTR r0
  ssStep  : forall {r1 r2 : Record} -> (r0 EXTTR r1) -> (r1 EXT r2) -> r0 EXTTR r2
\end{code}
\end{myhs}

  Another way of thinking about the |EXTD| relation is in terms of
dependency. A value of type |r0 EXT r1| proves that |r1| depends on |r0|.
Which brings us to our first lemma: all valid records depend on the initial
record:

\begin{myhs}
\begin{code}
lemmaS11 : {i : Initial}{r : Record} -> RecordChain r -> (I i) EXTTR r
\end{code}
\end{myhs}

  Its proof is an expected induction on |RecordChain|, extracting the
|EXTD| fields and building |EXTTRD|. A second, more interesting lemma,
states the injectivity of |EXTD|. Its proof is also trivial and depends
solely on the injectivity of the hash function, modulo hash collisions.

\begin{myhs}
\begin{code}
lemmaS12 : forall {r0 r1 r2} -> r0 EXT r2 -> r1 EXT r2 -> Either HashBroke (r0 == r1)
\end{code}
\end{myhs}

  The third and final lemma for now states that for whatever record |r2| that
comes to depend on two others, |r0| and |r1|, then these two others must
also be dependent -- again, modulo hash collisions.

\begin{myhs}
\begin{code}
lemmaS13  : ∀{r0 r1 r2} -> RecordChain r0 -> RecordChain r1
          -> r0 EXTTR r2 -> r1 EXTTR r2
          -> round r0 < round r1
          -> Either HashBroke (r0 EXTTR r1)
\end{code}
\end{myhs}

  The last notion we need at the moment is that of a $k$-chain
(Section 5.2 in the original paper~\cite{Baudet2019}), that is, a
record chain with at least $k$ blocks in its tail. The definition
below might seem intricate, but it is simply unfolding $k$ steps in a
record chain. Both datatypes are shown in

\begin{myhs}
\begin{code}
data Kchain (R : Record -> Record -> Set) : (k : Nat){r : Record} -> RecordChain r -> Set1 where
    zchain  : forall {r}{rc : RecordChain r} -> Kchain R 0 rc
    schain  : forall {k r}{rc : RecordChain r}{b : Block}{q : QC}
            -> (r←b : r   ← B b)
            -> {prfB : IsInPool (B b)}
            -> (vb  : Valid rc (B b))
            -> (prf : R r (B b))
            -> (b←q : B b ← Q q)
            -> {prfQ : IsInPool (Q q)}
            -> (vq  : Valid (step rc r←b vb {prfB}) (Q q))
            -> Kchain R k rc
            -> Kchain R (suc k) (step (step rc r←b vb {prfB}) b←q vq {prfQ})
\end{code}
\end{myhs}


  Note we parametrize |Kchain| by a relation |R|, over records. This enables us to
use the same datatype to talk about \emph{simple} and \emph{contiguous} $k$-chains -- where the rounds of of each block in the chain are contiguous.

\begin{myhs}
\begin{code}
Contig : Record -> Record -> Set
Contig r r' = round r' ≡ suc (round r)

Simple : Record -> Record -> Set
Simple _ _ = Unit

Kchain-contig : (k : Nat){r : Record} -> RecordChain r -> Set1
Kchain-contig = Kchain Contig
\end{code}
\end{myhs}

  Which brings us to the \emph{commit rule}. In LibraBFT, a block is said
to be commited if it is the head of a contiguous 3-chain, where the \emph{head}
of a chain is defined below.

\begin{myhs}
\begin{code}
kchainHead : forall {k r R}{rc : RecordChain r} -> Kchain R k rc -> Record
kchainHead (zchain {r = r})       = r
kchainHead (schain _ _ _ _ _ ch)  = kchainHead ch
\end{code}
\end{myhs}

  When proving properties about $k$-chains it is often
more useful to talk about the $n$-th block of a chain, counting
from the tail. The head is but the $k$-th block of a $k$-chain:

\begin{myhs}
\begin{code}
kchainBlock : forall {k r R}{rc : RecordChain r} -> Fin k -> Kchain R k rc -> Block
kchainBlock zero     (schain {b = b}  _ _ _ _ _ _)   = b
kchainBlock (suc x)  (schain          _ _ _ _ _ ch)  = kchainBlock x ch
\end{code}
\end{myhs}

  Finally, we have the necessary notions to encode the commit rule, which states
that a block is considered commited whenever it is the head of a contiguous $3$-chain.
We encode this as a relation between record chains and blocks, by the |CommitRule|
datatype defined below.

\begin{myhs}
\begin{code}
data CommitRule : forall {r} -> RecordChain r -> Block -> Set1 where
  commitrule  : forall {r b}{rc : RecordChain r}(c3 : Kchain Contig 3 rc) 
              -> b == kchainBlock (suc (suc zero)) c3
              -> CommitRule rc b
\end{code}
\end{myhs}

  Our objective then becomes clearer: we want to prove that the commit rule
is safe, in the sense that if two blocks match the commit rule, they belong 
to the same chain. That is, one extends the other.
This is estabilished by theorem S5 in the original paper.
Our encoding of it is given below. 

\begin{myhs}
\begin{code}
thmS5  : forall {q q'}{rc : RecordChain (Q q)}{rc' : RecordChain (Q q')}
       -> {b b' : Block}
       -> CommitRule rc  b
       -> CommitRule rc' b'
       -> Either  HashBroke 
                  (Either (B b inRC rc') (B b' inRC rc)
\end{code}
\end{myhs}

  The |inRC| here estabilishes \victor{continue...}

\begin{myhs}
\begin{code}
data inRCD (r0 : Record) : ∀{r1} -> RecordChain r1 -> Set where
  here   : ∀{rc : RecordChain r0} -> r0 inRC rc
  there  : ∀{r1 r2}{rc : RecordChain r1}(p : r1 EXT r₂)(pv : Valid rc r2)
         -> r0 inRC rc
         -> {prf : IsInPool r2}
         -> r0 inRC (step rc p pv {prf})
\end{code}
\end{myhs}


\subsection{Voting Constraints}
\label{sec:voting-constraints}

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

