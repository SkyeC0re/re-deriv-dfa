# re-deriv-dfa

A Haskell library for creating, minimizing and vizualizing Regular Expressions (REs) and their respective 
Deterministic Finite Automata (DFAs) transformations using the derivative approach, as is described in the paper
"Regular-expression derivatives re-examined" by by Scott Owens, John Reppy and Aaron Turon.


## Installation

Use the [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/) package manager to run
the project.

## Usage
The main program will compute the list of dissimilar REs of size i or less, for 1<=i<=8 across the alphabet {a,b}.
For each i, the the program produces:
  - The size of the list of dissimilar REs (dREs)
  - The amount of dREs which produce minimal DFAs using the derivative method (mDFA).
  - The maximum size across all of the aforementioned mDFAs.

```batch
stack build
stack exec re-deriv-dfa-exe
```

To run the test suite, use:

```batch
stack test
```

## License
[MIT](https://choosealicense.com/licenses/mit/)
