# game-trees

## Menu

- [Rationale](#rationale)
- [Quick start](#quick-start)
- [Building](#building)
- [Installation](#installation)
- [Contributions](#contributions)
- [License](#license)
- [Code of Conduct](#code-of-conduct)

## Rationale

This repository contains functions and proofs about game trees in Rocq, implemented as [rose trees](https://en.wikipedia.org/wiki/Rose_tree). We provide two different flavors of game trees, inductive and coinductive game trees. Inductive game trees are finite by construction, but it is difficult to populate a tree from an initial value and a function that gives the next steps. We have to prove that the population (anamorphism or unfolding of a rose tree) terminates. Coinductive game trees can be infinite or finite. Populating a coinductive tree is easy since we do not have to prove termination, but we need bisimulation to reason about them.

## Quick start

In `GameTrees.Trees.Unfold`, we provide an `unfold_tree` function that populates an inductive tree in a provably terminating way, if you abide by certain restrictions about what the `next` function says the next steps will be. We prove that this function is *sound* and *complete*: a value is in the game tree if and only if there is a sequence of applications of `next` from the initial state that create that value.

In `GameTrees.Cotrees.Unfold`, we provide an `unfold_cotree` function that populates a possibly infinite tree. We prove that this function is also *sound* and *complete*.

To showcase our library, we provide an example: a tic-tac-toe game for which we unfold a proven-complete game tree and run minimax algorithm to implement an unbeatable AI.

## Building

You have to have the `coq-released` registry of `opam`. You can obtain it by running `opam repo add coq-released https://coq.inria.fr/opam/released` if you do not already have it.

To install the dependencies, run `opam install . --deps-only`. The project certainly builds with Coq 8.20.1, so we hard-coded it for reproducibility.

To build the project use `make`. After that, you can optionally run the tic-tac-toe game with `make run`.

## Installation

To install the project use `opam install .`. You do not need the `make` step from the build instructions for this.

## Contributions

We :heart: contributions.

Have you had a good experience with this project? Why not share some love and contribute code, or just let us know about any issues you had with it?

We welcome issue reports [here](../../issues); be sure to choose the proper issue template for your issue, so that we can be sure you're providing the necessary information.

Before sending a [Pull Request](../../pulls), please make sure you read our
[Contribution Guidelines](https://github.com/bloomberg/.github/blob/master/CONTRIBUTING.md).

## License

Please read the [LICENSE](LICENSE) file.

## Code of Conduct

This project has adopted a [Code of Conduct](https://github.com/bloomberg/.github/blob/master/CODE_OF_CONDUCT.md).
If you have any concerns about the Code, or behavior which you have experienced in the project, please
contact us at opensource@bloomberg.net.
