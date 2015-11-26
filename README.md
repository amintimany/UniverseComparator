# Universe Comparator

A plugin for Coq that provides comparison of universe levels. For details of how it works see https://amintimany.github.io/UniverseComparator/html/test.html

## Compatibility
This plugin works with Coq 8.5.

Versions 1.0 and 1.0.1 are compatible with Coq8.5~beta2 and earlier.
For the documentation of UniverseComparator 1.0.1 see https://amintimany.github.io/UniverseComparator/older_versions/v1.0.1/html/test.html  
Version 1.1 is compatible with Coq8.5~beta3.

## Install with OPAM
Add the OPAM repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-universe-comparator

## Install from source
You need to have `coq_makefile`, `coqc` and `ocamlc` on the path. To compile use:

``./configure.sh``  
``make``

To install use:  

``make install``

## Acknowledgement
I would like to thank the organizers of the [First Coq Coding Sprint](https://coq.inria.fr/cocorico/CoqCodingSprint/CoqCS1). I would also like to specially thank Matthieu Sozeau and Pierre-Marie Pédrot for their help.
