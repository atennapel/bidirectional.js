WIP

Implementation based on the algorithm given in "A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference".
I'm using reference cells for the meta type variables to reduce the amount of substitution I need to do.
I also use meta type variables for the synthesis judgments (for the same reason).

Questions:
- How/when to do generalization?
- Can the system be easily extended to do kind inference (on the type annotations)

TODO:
- add kmeta, turn wfType in to judgment
- kind inference
