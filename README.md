# Formal verification of byzantine fault tolerant consensus in Agda

  This repository contains **work in progress** towards a model and formal verification of a Byzantine Fault Tolerant consensus protocol based on [LibraBFT](https://developers.diem.com/docs/technical-papers/state-machine-replication-paper), which is itself based on [HotStuff](https://arxiv.org/abs/1803.05069).  (Note that LibraBFT has recently been renamed to DiemBFT.)  The model and proofs are written in [Agda](https://agda.readthedocs.io).

  Our first contribution is an abstract representation of a system in which records (blocks, votes, and quorum certificates) exist satisfying certain properties, along with proofs that various correctness conditions hold, subject to assumptions about the maximum number of dishonest participants (per epoch) and rules that honest participants follow when sending votes, which we call *implementation obligations*.  One such correctness condition is essentially Theorem S5 from earlier versions of the LIbraBFT paper, which can be informally stated as:
  
> Given two committed blocks `b` and `b'`, either `b` extends `b'` or vice-versa.

Our next contribution is a system model  (`Yasm`), which can be instantiated to model an asynchronous distributed system in which a number of peers communicate by sending messages; messages can be reordered, dropped or duplicated.  The model is also instantiated with *handlers*, which take a message that has been sent and a previous peer state and produce a new peer state and a list of actions to perform, such as sending messages.  Honest behavior is modeled by these handlers, while dishonest (Byzantine) behavior is modeled by a "cheat" step that can send arbitrary messages, except that it is constrained so that it cannot forge honest signatures.  The system model supports a notion of "epochs", each of which has an "epoch configuration" that identifies the participants for each epoch, along with their public keys and various configuration parameters; this is used to constrain which messages can be sent by a cheat step.

Next, we have partially defined a concrete implementation by instantiating the system model with various types and handler functions, and we have defined an abstraction function from reachable system states to abstract system states, which we have proved enjoys various correctness conditions as described above.  This partial implementation includes (out of date) types used by the LibraBFT implementation, and a very simple handler that is designed to conform to one of the implementation obligations.  We are working on proving that it does, before we go on to update the implementation types to a more recent version, define more complete and accurate handlers, and prove that they meet all implementation obligations.

## Repository structure

The LibraBFT-specific parts of our development is divided into the following components:

* The [Abstract namespace](src/LibraBFT/Abstract) contains all the metatheory necessary for establishing the
crucial correctness condition for LibraBFT mentioned above, and some variations on it. 

* The [Concrete namespace](src/LibraBFT/Concrete) provides a concrete instance of the network model in `Yasm` (see below) using
the LibraBFT messages and nomenclature. This instance is passed down to the `Abstract` layer and used
to prove that the implementation satisfies the implementation obligations.

* The [Impl namespace](src/LibraBFT/Impl) defines the datatypes and handlers for our LibraBFT implementation, and ongoing work on proofs that they satisfy the implementation obligations.

The following components support our modeling and verification of the LibraBFT-specific components mentioned above.

* The [Dijkstra namespace](src/Dijkstra) contains a lightweight framework for proof engineering with Predicate Transformer Semantics, the use of which is demonstrated in
some proofs of properties in the [LibraBFT implementation](src/LibraBFT/Impl).

* The [Haskell namespace](src/Haskell) contains definitions to support modeling Haskell code in Agda with very similar syntax.

* The [Optics namespace](src/Optics) contains a small library to enable modeling Haskell lenses in Agda.

* The [Util namespace](src/Dijkstra) contains various utilities such as support for byte strings, cryptographic hashes and signatures, etc.

* The [Yasm namespace](src/Yasm) defines the system model and captures network assumptions, and can be instantiated with peers and handlers for any distributed system; in our case, we are interested in peers participating in a consensus network.

## Work in progress

As stated above, this repository represents **work in progress**.  While our work to date is encouraging, at this stage, nobody should interpret our work as proof that the HotStuff / LibraBFT algorithm is correct.  Furthermore, parts of our development are incomplete and other parts are still changing somewhat as we continue work on other parts.

## Getting started

To work with `Agda-LBFT`, you need to have Agda and its standard library installed.  The project currently works with Agda version 2.6.1.1 and Agda Standard Library v1.3 (i.e., we can successfully run `./Scripts/run-everything.sh yes` without errors).  Detailed instructions for installing Agda and setting up your environment are included at the [Getting Started section](https://plfa.github.io/GettingStarted) of [Programming Language Foundations in Agda](https://plfa.github.io), which is an excellent resource for learning Agda.

Once you have installed the correct version of Agda, you should be able to run `./Scripts/run-everything.sh yes` from the root directory of the project and observe successful completion with no errors.

To explore the repo, we suggest starting with the [`LibraBFT.Abstract.Properties`](src/LibraBFT/Abstract/Properties.agda) module if you are interested in exploring the abstract correctness proof, and with the [`LibraBFT.Yasm.Properties`](src/LibraBFT/Yasm/Properties.agda) module if you are interested in the system model and its properties.

If you would like to consider contributing to the project, please see our [Contribution Guide](CONTRIBUTING.md).

## Get Support

* Open a [GitHub issue](../../issues) to provide feedback, raise issues and ask questions.
* Report a security vulnerability according to the [Reporting Vulnerabilities guide](https://www.oracle.com/corporate/security-practices/assurance/vulnerability/reporting.html). More information at [SECURITY](SECURITY.md).

## License

`Agda-LBFT` is [licensed](LICENSE.txt) under [UPL 1.0](https://opensource.oracle.com/licenses/upl).

## Contributors

As of the beginning of this repo, contributions have been made by
ANONYMOUS

We are grateful to the following people for contributions since then:
* ANONYMOUS
